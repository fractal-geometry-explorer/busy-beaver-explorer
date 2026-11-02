"""Checks of pages/1RB1RF_1LC0LB/explainer.html: its data blocks are current, and its engine agrees with the reference
simulator.

The page's run data (`<script id="run-data">`) is written by py/explainer_data.py and its status panel
(`<script id="status-data">`) by tools/pages/explainer_status.py from status.json; both must be current.  The engine
(`<script id="engine">`) is run in Node and compared with py/blank.py (the reference simulator of tools/py/bbtools):
the left-end moments, the transition counts and the word view of random tapes.  The Node part is skipped if `node`
is not installed.

usage: python3 bb6-1RB1RF_1LC0LB/tests/test_explainer.py        (a few seconds)
"""
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
PAGE = os.path.join(REPO, "pages", "1RB1RF_1LC0LB", "explainer.html")
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
sys.path.insert(0, os.path.join(REPO, "tools", "pages"))
sys.path.insert(0, os.path.join(ROOT, "py"))

import blank  # noqa: E402
import explainer_data  # noqa: E402
import explainer_status  # noqa: E402

NODE = shutil.which("node")
STEPS = 3 * 10 ** 6

DRIVER = r"""
const TAPES = __TAPES__;
console.log(JSON.stringify({
  left: leftEvents(__STEPS__, 1000),
  counts: transitionCounts(1000000),
  words: TAPES.map(words),
}));
"""


def page():
    with open(PAGE) as f:
        return f.read()


class TestData(unittest.TestCase):
    def test_run_data_current(self):
        p = page()
        self.assertEqual(explainer_data.build(p, explainer_data.data()), p)

    def test_status_current(self):
        self.assertTrue(explainer_status.check(os.path.join(ROOT, "status.json"), PAGE))

    def test_links(self):
        p = page()
        self.assertIn('href="proof-status.html"', p)
        self.assertIn('href="../index.html"', p)


@unittest.skipUnless(NODE, "node is not installed")
class TestEngine(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        engine = re.search(r'<script id="engine">\n(.*?)</script>', page(), re.S).group(1)
        rng = random.Random(5)
        cls.tapes = [[rng.randrange(2) for _ in range(rng.randrange(40))] for _ in range(300)]
        src = engine + DRIVER.replace("__TAPES__", json.dumps(cls.tapes)).replace("__STEPS__", str(STEPS))
        with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False) as f:
            f.write(src)
            path = f.name
        try:
            cls.out = json.loads(subprocess.run([NODE, path], check=True, capture_output=True, text=True).stdout)
        finally:
            os.unlink(path)

    def test_left_events(self):
        py = [[t, w, s, ws] for t, w, s, ws in blank.left_events(STEPS)]
        self.assertEqual(self.out["left"], py)

    def test_counts(self):
        py = {f"{s}{y}": c for (s, y), c in blank.rare(10 ** 6).items()}
        self.assertEqual(self.out["counts"], py)
        self.assertEqual(json.loads(re.search(r'id="run-data">\n(.*?)\n</script>', page(), re.S).group(1))["counts"], py)

    def test_words(self):
        self.assertEqual(self.out["words"], [blank.words(t) for t in self.tapes])


if __name__ == "__main__":
    unittest.main(verbosity=2)
