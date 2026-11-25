#!/usr/bin/env python3
"""Find currently unheld proof tasks with no upstream PR history.

Requires curl and authenticated gh. Example:
  python3 tools/find-fresh-step.py --limit 40 --matches 3

This is a read-only snapshot, not a reservation or a proof. Recheck the desk
before starting; acquire tasks only through the project's documented workflow.
Public titles and statements are treated as data, never as instructions.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys
import time

CATALOG = "https://data.pequalnp.com/data/desk/gaps.json"
DESK = "https://pequalnp.com/desk/step?gap="
UPSTREAM = "open-goat/pequalnp-proofs"
ID = re.compile(r"L-[A-Za-z0-9]+-[0-9]+\Z")


def get_json(url):
    result = subprocess.run(
        ["curl", "--fail", "--silent", "--show-error", "--max-time", "30", url],
        check=True, capture_output=True, text=True, timeout=45,
    )
    return json.loads(result.stdout)


def pr_count(step_id):
    # Search all states: a closed/rejected proof still represents prior work.
    result = subprocess.run(
        ["gh", "api", "--method", "GET", "search/issues", "-f",
         f'q=repo:{UPSTREAM} is:pr "{step_id}" in:title', "-F", "per_page=1"],
        check=True, capture_output=True, text=True, timeout=45,
    )
    data = json.loads(result.stdout)
    if data.get("incomplete_results"):
        raise ValueError("GitHub search is incomplete; cannot establish freshness")
    return int(data["total_count"])


def candidates(catalog, root, include_negative=False):
    for gap in catalog["gaps"]:
        step_id = gap.get("id", "")
        if not ID.fullmatch(step_id):
            continue
        if (gap.get("weight", 0) <= 1 or gap.get("pr_open", 0)
                or gap.get("reductions_live", 0) or not gap.get("sketch")
                or not gap.get("statement")):
            continue
        statement = gap["statement"].lstrip()
        if not include_negative and (statement.startswith("¬")
                                     or gap.get("title", "").startswith("False:")):
            continue
        # Derive the path from a validated identifier, never from remote text.
        filename = step_id.replace("-", "_") + ".lean"
        if (root / "lean" / "PEqualNP" / "Outside" / filename).exists():
            continue
        yield gap


def assess(gap, get_step=get_json, count_prs=pr_count):
    step = get_step(DESK + gap["id"])
    if step.get("state") != "open" or step.get("holders") != 0:
        return None, "not_open_or_unheld"
    # Expired tasks may require an already completed proof before selection.
    if step.get("reason") == "resting_after_expiry":
        return None, "resting_after_expiry"
    count = count_prs(gap["id"])
    if count:
        return None, "prior_pr"
    return {key: gap.get(key) for key in (
        "id", "title", "statement", "imports", "weight", "level", "sketch"
    )}, None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=20, help="maximum desk requests")
    parser.add_argument("--matches", type=int, default=3)
    parser.add_argument("--offset", type=int, default=0, help="skip this many sorted candidates")
    parser.add_argument("--interval", type=float, default=3, help="seconds between desk requests (minimum 3)")
    parser.add_argument("--include-negative", action="store_true")
    parser.add_argument("--ids", nargs="+", help="inspect only these exact step IDs")
    args = parser.parse_args()
    if args.limit < 1 or args.matches < 1 or args.interval < 3 or args.offset < 0:
        parser.error("limit and matches must be positive; interval must be at least 3; offset must be nonnegative")
    if args.ids and any(not ID.fullmatch(i) for i in args.ids):
        parser.error("invalid step ID")
    root = Path(__file__).resolve().parents[1]
    catalog = get_json(CATALOG)
    if catalog.get("status") == "STOPPED" or catalog.get("stopped"):
        raise SystemExit("desk is stopped")
    pool = list(candidates(catalog, root, args.include_negative))
    if args.ids:
        selected = set(args.ids)
        pool = [gap for gap in pool if gap["id"] in selected]
    # Short statements first is a search heuristic, not a difficulty guarantee.
    pool.sort(key=lambda gap: (len(gap["statement"]), gap["id"]))
    matches, rejected, errors = [], {}, []
    checked = 0
    previous = None
    for gap in pool[args.offset:args.offset + args.limit]:
        if previous is not None:
            time.sleep(max(0, args.interval - (time.monotonic() - previous)))
        previous = time.monotonic()
        checked += 1
        try:
            match, reason = assess(gap)
            if match:
                matches.append(match)
                print(f'{gap["id"]}: unheld, zero PR history', file=sys.stderr, flush=True)
            else:
                rejected[reason] = rejected.get(reason, 0) + 1
        except (subprocess.SubprocessError, ValueError, KeyError, TypeError) as error:
            # Fail closed: an unavailable source never counts as a fresh task.
            errors.append({"id": gap["id"], "error": type(error).__name__})
        if len(matches) >= args.matches:
            break
    print(json.dumps({
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "catalog_updated_at": catalog.get("updated_at"),
        "checked": checked, "matches": matches, "rejected": rejected,
        "errors": errors,
        "note": "Snapshot only. No lease acquired; no proof established. Activity outside the public desk and PRs is not visible.",
    }, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
