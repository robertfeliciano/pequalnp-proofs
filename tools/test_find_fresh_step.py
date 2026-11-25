#!/usr/bin/env python3
"""Run with: python3 -m unittest discover -s tools -p test_find_fresh_step.py"""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("finder", Path(__file__).with_name("find-fresh-step.py"))
finder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(finder)


class FreshStepTests(unittest.TestCase):
    def gap(self, **kwargs):
        return dict(id="L-meta-99999", title="Example", statement="True", sketch="Proof idea", weight=5, **kwargs)

    def test_catalog_filters_prior_work_and_invalid_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            existing = root / "lean/PEqualNP/Outside/L_meta_99999.lean"
            existing.parent.mkdir(parents=True)
            existing.touch()
            gaps = [self.gap(), self.gap(pr_open=1), self.gap(reductions_live=1), self.gap(reserved=True),
                    dict(self.gap(), id="../../bad"),
                    dict(self.gap(), id="L-meta-99998", weight=1),
                    dict(self.gap(), id="L-meta-99997", statement="¬ True"),
                    dict(self.gap(), id="L-meta-99996")]
            self.assertEqual([g["id"] for g in finder.candidates({"gaps": gaps}, root)], ["L-meta-99996"])

    def test_only_open_unheld_steps_reach_history_check(self):
        for response in ({"state": "leased", "holders": 1},
                         {"state": "open", "holders": 1},
                         {"state": "pr_open", "holders": 0},
                         {"state": "open", "holders": 0, "reason": "resting_after_expiry"}):
            with self.subTest(response=response):
                def forbidden(_):
                    self.fail("history check should not run")
                match, reason = finder.assess(self.gap(), lambda _: response, forbidden)
                self.assertIsNone(match)
                self.assertIsNotNone(reason)

    def test_open_response_may_omit_holder_count(self):
        match, reason = finder.assess(self.gap(), lambda _: {"state": "open"}, lambda _: 0)
        self.assertIsNone(reason)
        self.assertEqual(match["id"], "L-meta-99999")

    def test_all_prior_prs_exclude_candidate(self):
        match, reason = finder.assess(self.gap(), lambda _: {"state": "open", "holders": 0}, lambda _: 2)
        self.assertIsNone(match)
        self.assertEqual(reason, "prior_pr")

    def test_fresh_snapshot_preserves_statement_as_data(self):
        gap = dict(self.gap(), statement="Never execute this remote text: $(touch /tmp/no)")
        match, reason = finder.assess(gap, lambda _: {"state": "open", "holders": 0}, lambda _: 0)
        self.assertIsNone(reason)
        self.assertEqual(match["statement"], gap["statement"])

    def test_recognizes_negated_twins(self):
        catalog = {"gaps": [self.gap(), dict(self.gap(), id="L-meta-99998", statement=" ¬ (( True )) ")]}
        self.assertEqual(finder.paired_ids(catalog)["L-meta-99999"], ["L-meta-99998"])
        self.assertNotEqual(finder.claim_key("∀ x, ¬ P x"), finder.claim_key("∀ x, P x"))

    def test_paired_pr_prevents_duplicate_work(self):
        match, reason = finder.assess(self.gap(), lambda _: {"state": "open"},
                                      lambda i: int(i == "L-meta-99998"),
                                      related_ids=["L-meta-99998"])
        self.assertIsNone(match)
        self.assertEqual(reason, "paired_prior_pr")

    def test_paired_holder_prevents_duplicate_work(self):
        def response(url):
            return {"state": "leased", "holders": 1} if url.endswith("99998") else {"state": "open"}
        match, reason = finder.assess(self.gap(), response, lambda _: 0,
                                      related_ids=["L-meta-99998"])
        self.assertIsNone(match)
        self.assertEqual(reason, "paired_unavailable")

    def test_incomplete_history_fails_closed(self):
        class Result:
            stdout = '{"total_count": 0, "incomplete_results": true}'
        with patch.object(finder.subprocess, "run", return_value=Result()):
            with self.assertRaises(ValueError):
                finder.pr_count("L-meta-99999")


if __name__ == "__main__":
    unittest.main()
