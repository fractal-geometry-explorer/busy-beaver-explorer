"""Checks on the holdouts batch: generated Lean matches the machine, pages match their status.json.

usage: python3 holdouts/test_holdouts.py
"""
import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import build_pages  # noqa: E402
import gen  # noqa: E402
from bbtools.machine import Machine  # noqa: E402


class TestHoldouts(unittest.TestCase):
    def test_list_complete(self):
        rows = gen.load_triage()
        self.assertEqual(len(rows), 608)
        folders = {n for n, _ in build_pages.specs()}
        for r in rows:
            if r["machine"] not in gen.STUDIED:
                self.assertIn(r["machine"], folders)

    def test_machine_lean(self):
        by = {r["machine"]: r for r in gen.load_triage()}
        for name, spec in build_pages.specs():
            r = by[name]
            with open(os.path.join(HERE, name, "lean", "Machine.lean")) as f:
                src = f.read()
            self.assertIn(f'def text : String := "{name}"', src)
            self.assertIn(f"namespace {gen.ns_of(r)}", src)
            self.assertEqual(spec["machine"], name)
            Machine.parse(name)

    def test_generated_folders_current(self):
        by = {r["machine"]: r for r in gen.load_triage()}
        for name, spec in build_pages.specs():
            if not spec.get("generated", True):
                continue
            m = Machine.parse(name)
            self.assertEqual(spec, json.loads(json.dumps(gen.status_spec(by[name], m))), name)
            with open(os.path.join(HERE, name, "lean", "Blank.lean")) as f:
                self.assertEqual(f.read(), gen.blank_lean(by[name], m), name)

    def test_pages_current(self):
        for name, spec in build_pages.specs():
            d = os.path.join(build_pages.PAGES, name)
            with open(os.path.join(d, "explainer.html")) as f:
                self.assertEqual(f.read(), build_pages.build_explainer.build(spec, spec.get("home", "../index.html")),
                                 name)
            with open(os.path.join(d, "proof-status.html")) as f:
                self.assertEqual(f.read(), build_pages.build_status.build(spec, spec.get("home", "../index.html")),
                                 name)

    def test_index_current(self):
        with open(os.path.join(build_pages.PAGES, "index.html")) as f:
            old = f.read()
        build_pages.build_index()
        with open(os.path.join(build_pages.PAGES, "index.html")) as f:
            self.assertEqual(f.read(), old)


if __name__ == "__main__":
    unittest.main()
