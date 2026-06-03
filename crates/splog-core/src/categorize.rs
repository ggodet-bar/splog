//! This module handles the logic for parsing log lines, for identifying the line header, if any,
//! and for extracting category candidates.
use std::{borrow::Cow, collections::HashSet, sync::OnceLock};

use regex::Regex;

const LEVELS: &[&str] = &[
    "TRACE", "TRC", "DEBUG", "DBG", "INFO", "INF", "NOTICE", "NOTE", "WARN", "WARNING", "WRN",
    "ERROR", "ERR", "FATAL", "CRITICAL", "CRIT", "VERBOSE", "VRB",
];

/// Bytes of "glue" punctuation tolerated between two header tokens before the
/// contiguous prefix is considered broken. Wide enough for `" | "`, `" - "`,
/// or `": "`, narrow enough that a sentence's space-word-space cadence ends
/// the header on the first free-text token.
const MAX_GLUE: usize = 3;

/// Extract candidate category tags from a raw log line. Candidates come from
/// `[...]` and `(...)` groups that sit inside the line's leading "header"
/// region — a contiguous run of timestamp / severity / bracketed-or-paren
/// tokens separated by a few glue characters. Bracket/paren groups in the
/// free-text payload are ignored, which is what keeps recurring parenthetical
/// asides ("(session expired)", "(retrying)") out of the category set.
/// Candidates between dashes, eg. `-...-` are parsed as a special case and returned
/// immediately.
#[inline]
pub fn extract(line: &str) -> Vec<String> {
    let plain = strip_ansi(line);
    let (header_end, dashed_candidates) = header_end_and_dash_candidates(&plain);
    let mut out = Vec::new();
    let mut seen = HashSet::<String>::new();

    // SAFETY: all occurrences of `cap` will match a group, `.get(0)` and `.get(1)` will always
    // a result.
    for re in [bracketed_re(), parenthesized_re(), fqn_like_re()] {
        for cap in re.captures_iter(&plain) {
            if cap.get(0).unwrap().start() >= header_end {
                continue;
            }
            let cap = cap.get(1).unwrap();
            let inner = cap.as_str().trim();
            if accept_tag(inner) && seen.insert(inner.to_string()) {
                out.push((inner.to_string(), cap.start(), cap.end()));
            }
        }
    }
    for (dashed_candidate, start_idx, end_idx) in dashed_candidates {
        if accept_tag(&dashed_candidate) && seen.insert(dashed_candidate.clone()) {
            out.push((dashed_candidate, start_idx, end_idx));
        }
    }
    if out.is_empty() {
        return Vec::new();
    }
    // Merge overlapping candidates
    out.sort_by(|(_, idx_a, _), (_, idx_b, _)| (*idx_a).cmp(idx_b));
    let (mut current_tag, mut current_start_idx, mut current_end_idx) = out[0].clone();
    let mut merged = Vec::new();
    for (tag, start_idx, end_idx) in &out[1..] {
        if *start_idx > current_end_idx {
            merged.push(current_tag.clone());
            current_tag = tag.to_owned();
            current_start_idx = *start_idx;
            current_end_idx = *end_idx;
        } else if current_end_idx < *end_idx {
            current_tag = plain[current_start_idx..*end_idx].to_owned();
            current_end_idx = *end_idx;
        }
    }
    merged.push(current_tag);
    merged
}

fn strip_ansi(s: &str) -> Cow<'_, str> {
    // Most log lines have no ESC byte; skip the regex pass entirely
    // and hand back the input as a borrow. Replace_all already
    // returns Cow, so the slow path keeps its existing semantics.
    if !s.contains('\x1b') {
        return Cow::Borrowed(s);
    }
    static R: OnceLock<Regex> = OnceLock::new();
    let re = R.get_or_init(|| Regex::new(r"\x1B\[[0-9;?]*[A-Za-z]").unwrap());
    re.replace_all(s, "")
}

fn dashed_re() -> &'static Regex {
    static R: OnceLock<Regex> = OnceLock::new();
    R.get_or_init(|| Regex::new(r"-\s+([^\s]+)\s+-").unwrap())
}

fn bracketed_re() -> &'static Regex {
    static R: OnceLock<Regex> = OnceLock::new();
    R.get_or_init(|| Regex::new(r"\[([^\[\]]+)\]").unwrap())
}

fn parenthesized_re() -> &'static Regex {
    static R: OnceLock<Regex> = OnceLock::new();
    R.get_or_init(|| Regex::new(r"\(([^()]+)\)").unwrap())
}

fn fqn_like_re() -> &'static Regex {
    static R: OnceLock<Regex> = OnceLock::new();
    R.get_or_init(|| Regex::new(r"([a-zA-Z](?:[a-zA-Z\.\$]|::)+[a-zA-Z]):").unwrap())
}

/// Byte offset where the line's contiguous header region ends. The walk
/// starts after any leading whitespace, then greedily eats header tokens
/// (bracketed/parenthesized groups, ISO dates, times, bare severities)
/// separated by up to `MAX_GLUE` bytes of punctuation/whitespace. Returns 0
/// when no header token sits at the start — every bracket/paren group on
/// such lines is then treated as payload and ignored.
fn header_end_and_dash_candidates(plain: &str) -> (usize, Vec<(String, usize, usize)>) {
    let bytes = plain.as_bytes();
    let mut i = 0;
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }

    let re = header_token_re();
    let mut last_end = i;
    let mut found_any = false;

    let mut dashed_candidates = Vec::new();
    let mut last_seen_dash = None;
    loop {
        if let Some(m) = re.find(&plain[i..]) {
            if m.start() != 0 {
                break;
            }
            i += m.end();
        } else {
            // Check for remaining tags based on non-whitespace glue characters (dashes, for now).
            if let Some(dash_idx) = last_seen_dash
                && dash_idx >= last_end
                && let Some(cap) = dashed_re().captures(&plain[dash_idx..])
            {
                let m = cap.get_match();
                // SAFETY: `dashed_re` matches a group, so `cap.get(1)` is always expected to
                // return a result.
                let cap = cap.get(1).unwrap();
                let (start_idx, end_idx) = (cap.start() + dash_idx, cap.end() + dash_idx);
                if m.start() == 0 {
                    i += cap.end() - (i - dash_idx);
                    dashed_candidates.push((cap.as_str().to_owned(), start_idx, end_idx));
                } else {
                    break;
                }
            } else {
                break;
            }
        };
        last_end = i;
        found_any = true;

        let mut glue = 0;
        while i < bytes.len() && glue < MAX_GLUE && is_glue(bytes[i]) {
            if bytes[i] == b'-' {
                last_seen_dash = Some(i);
            }
            i += 1;
            glue += 1;
        }
    }

    if found_any {
        (last_end, dashed_candidates)
    } else {
        (0, dashed_candidates)
    }
}

fn is_glue(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b':' | b'-' | b'|' | b'>' | b',')
}

fn header_token_re() -> &'static Regex {
    static R: OnceLock<Regex> = OnceLock::new();
    R.get_or_init(|| {
        let levels = LEVELS.join("|");
        let pattern = format!(
            r"(?xi)
            ^(?:
                \[[^\[\]]+\]
              | \([^()]+\)
              | \d+\s
              | \d{{4}}-\d{{2}}-\d{{2}}T?
              | \d{{8}}T?
              | \d{{2}}:\d{{2}}:\d{{2}}(?:[\.,]\d+Z?)?
              | \d{{2}}(?:\d{{2}})?/((?:\D{{3}})|(?:\d{{2}}))/\d{{2}}(?:\d{{2}})?
              | [a-zA-Z](?:[a-zA-Z\.\$]|::)+[a-zA-Z\]]:
              | [+\-]\d{{2}}:?\d{{2}}
              | (?:{levels})\b
            )"
        );
        Regex::new(&pattern).unwrap()
    })
}

fn accept_tag(s: &str) -> bool {
    if s.is_empty() || s.len() > 64 {
        return false;
    }
    if is_level(s) || is_timestampish(s) {
        return false;
    }
    // Pure numeric / dotted-number / whitespace-only content is noise (PIDs,
    // counts, decimals); leave proper identifiers alone.
    if s.chars()
        .all(|c| c.is_ascii_digit() || c == '.' || c.is_whitespace())
    {
        return false;
    }
    true
}

fn is_level(s: &str) -> bool {
    let upper = s.to_ascii_uppercase();
    LEVELS.iter().any(|&l| upper == l)
}

fn is_timestampish(s: &str) -> bool {
    static R: OnceLock<Regex> = OnceLock::new();
    let re =
        R.get_or_init(|| Regex::new(r"\d{4}-\d{2}-\d{2}|\d{2}:\d{2}:\d{2}|^\d+(\.\d+)?$").unwrap());
    re.is_match(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paren_group_in_payload_is_excluded() {
        let cats = extract("2026-05-06 12:00:00 INFO [auth] User did X (session expired)");
        assert_eq!(cats, vec!["auth".to_string()]);
    }

    #[test]
    fn paren_group_inside_header_is_kept() {
        let cats = extract("2026-05-06 INFO [auth] (worker-3) message body");
        assert_eq!(cats, vec!["auth".to_string(), "worker-3".to_string()]);
    }

    #[test]
    fn bare_bracket_prefix_still_works() {
        let cats = extract("[auth] message with (note)");
        assert_eq!(cats, vec!["auth".to_string()]);
    }

    #[test]
    fn line_without_header_yields_no_categories() {
        // No timestamp, no severity, no leading bracket: everything is payload.
        let cats = extract("just a message with (parens) in it");
        assert!(cats.is_empty(), "got {cats:?}");
    }

    #[test]
    fn long_separator_breaks_the_header() {
        // More than MAX_GLUE chars between tokens stops the contiguous run,
        // so the trailing `[b]` is treated as payload.
        let cats = extract("[a] xxxxxxxxx [b]");
        assert_eq!(cats, vec!["a".to_string()]);
    }

    #[test]
    fn bracketed_severity_extends_header_without_becoming_a_category() {
        let cats = extract("[INFO] [auth] message (skip)");
        assert_eq!(cats, vec!["auth".to_string()]);
    }

    #[test]
    fn iso_datetime_with_timezone_extends_header() {
        let cats = extract("2026-05-06T12:00:00.123Z [svc] hello (world)");
        assert_eq!(cats, vec!["svc".to_string()]);
    }

    #[test]
    fn compact_yyyymmdd_dash_time_extends_header() {
        let cats = extract(
            "20250605-16:47:03.940196000 DEBUG [Strat] \
             Starting process round 0",
        );
        assert_eq!(cats, vec!["Strat".to_string()]);
    }

    #[test]
    fn dd_slash_month_slash_year_time_extends_header() {
        let cats = extract(
            "01/Jan/2016:03:45:49 +0100 DEBUG [Strat] \
             Starting process round 0",
        );
        assert_eq!(cats, vec!["Strat".to_string()]);
    }

    #[test]
    fn dash_separated_categories_extend_header() {
        let cats = extract("2026-05-02T09:43:45.729516 - INFO - Main - Cargo Profile: debug");
        assert_eq!(cats, vec!["Main".to_string()]);
        let cats = extract("2026-01-01 - INFO file-name-here.log");
        assert_eq!(cats, Vec::<String>::new());
        let cats = extract("2026-05-02T09:43:45.729516 - INFO - Main - some-dashed-payload");
        assert_eq!(cats, vec!["Main".to_string()]);
        let cats = extract("[a] - [b] xxxxxxx some-dashed-payload");
        assert_eq!(cats, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn multiple_dashed_categories_extend_header() {
        let cats = extract(
            "2026-05-02T09:43:45.729516 - INFO - Main - Server - Cluster0 - Cargo Profile: debug",
        );
        assert_eq!(
            cats,
            vec![
                "Main".to_string(),
                "Server".to_string(),
                "Cluster0".to_string()
            ]
        );
    }

    #[test]
    fn dashed_categories_with_inner_dashes_extend_header() {
        let cats = extract("2026-05-02T09:43:45.729516 - INFO - Main-Process - payload");
        assert_eq!(cats, vec!["Main-Process".to_string()]);
    }

    #[test]
    fn fully_qualified_name_like_text_extend_header() {
        let cats = extract(
            "17/06/09 20:10:40 INFO spark.SecurityManager: Changing view acls to: yarn,curi",
        );
        assert_eq!(cats, vec!["spark.SecurityManager".to_string()]);
    }

    #[test]
    fn merge_overlapping_candidates() {
        let cats = extract(
            "2015-07-29 19:04:29,071 - WARN  [SendWorker:188978561024:QuorumCnxManager$SendWorker@688] - Send worker leaving thread",
        );
        assert_eq!(
            cats,
            vec!["SendWorker:188978561024:QuorumCnxManager$SendWorker@688".to_string()]
        );
    }

    #[test]
    fn single_number_extends_header() {
        let cats = extract(
            "39 | 2026-05-29T07:23:44.365060Z TRACE cascaded::persistence::restore: Storing IXFR in-memory diff for SOA loaded serial -None:+None -> signed serial -Some(Serial(U32(2026052600))):+Som|",
        );
        assert_eq!(cats, vec!["cascaded::persistence::restore".to_string()]);
    }

    // NOTE The following test case would not be supported right now, as the categories appear as
    // "free" text without any delimiter. The fact that there is a timestamp afterwards might be
    // too brittle to rely on.
    // #[test]
    // fn name_pending() {
    //     let cats = extract("127.0.0.1 - JOHN DOE [01/Jan/2016:03:45:49 +0100]");
    //     assert_eq!(cats, vec!["127.0.0.1 - JOHN DOE".to_string()]);
    // }
}
