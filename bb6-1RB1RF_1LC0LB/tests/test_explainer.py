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
import counter  # noqa: E402
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
  counter: __LISTS__.map(t => { const r = counterStep(t); return r.t ? r.t : r.why; }),
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
        # level lists: the run's own at its first returns to the right end, and random ones
        cls.lists = [t for _, t in zip(range(400), (t for _, t in counter.returns(10 ** 7)))]
        for _ in range(600):
            t = [rng.randrange(1, 9)]
            for _ in range(rng.randrange(1, 7)):
                t += [rng.choice("01"), rng.randrange(1, 9)]
            cls.lists.append(t + ["0", 1])
        src = engine + DRIVER.replace("__TAPES__", json.dumps(cls.tapes)).replace("__STEPS__", str(STEPS)) \
            .replace("__LISTS__", json.dumps(cls.lists))
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

    def test_counter(self):
        want = []
        for t in self.lists:
            p, why = counter.predict(t)
            want.append(p if p is not None else why)
        self.assertEqual(self.out["counter"], want)
        self.assertGreater(sum(isinstance(w, list) for w in want), 300)

    def test_counter_start(self):
        # the widget starts from the run's tape at its first return to the right end after step 10^10
        start = re.search(r"const START = (\[.*?\]);", page(), re.S).group(1)
        want = next(t for s, t in counter.returns(float("inf")) if s >= 10 ** 10)
        self.assertEqual(json.loads(start.replace("\n", " ")), want)

    def test_words(self):
        self.assertEqual(self.out["words"], [blank.words(t) for t in self.tapes])


if __name__ == "__main__":
    unittest.main(verbosity=2)
