"""Regression checks for exact baseline/probe separation, not Lean proof tests."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

class NativeProbeTests(unittest.TestCase):
    def setUp(self):
        path = HERE / "prepare_native_probe.py"
        self.assertTrue(path.is_file(), "missing mandatory native-probe preparation")
        spec = importlib.util.spec_from_file_location("native_probe", path)
        self.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.module)
        self.baseline = (ROOT / self.module.TARGET).read_bytes()

    def test_exact_predecessor_bytes(self):
        candidate = self.module.make_probe(self.baseline)
        self.assertEqual(self.module.git_blob(candidate), "910ff74bbd5ef701b094a8b8edc04e697363f2d6")

    def test_baseline_not_proof_evidence(self):
        self.assertEqual(self.module.git_blob(self.baseline), "c8d38bef385eb15661c3daf7449625b66b019b2a")
        candidate = self.module.make_probe(self.baseline)
        self.assertIn(b"apply AEGIS.RHDeepMindTerminalV1.li_nonnegativity_closes_rh_v1", candidate)
        self.assertNotIn(b"theorem riemannHypothesis : RiemannHypothesis := by\n  sorry", candidate)

    def test_reject_source_drift(self):
        for mutated in (b"", self.baseline + b"\n", self.baseline.replace(b"import FormalConjecturesUtil", b"import Mathlib")):
            with self.subTest(mutated=mutated[:30]):
                with self.assertRaises(ValueError):
                    self.module.make_probe(mutated)

    def test_reject_already_prepared_probe(self):
        with self.assertRaises(ValueError):
            self.module.make_probe(self.module.make_probe(self.baseline))

    def test_cli_writes_exact_native_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / self.module.TARGET
            target.parent.mkdir(parents=True)
            target.write_bytes(self.baseline)
            result = subprocess.run([sys.executable, str(HERE / "prepare_native_probe.py"), str(root)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(self.module.git_blob(target.read_bytes()), self.module.PROBE_BLOB)
            self.assertIn("RH_PROVEN=FALSE", result.stdout)

    def test_cli_rejects_without_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / self.module.TARGET
            target.parent.mkdir(parents=True)
            original = self.baseline + b"-- drift\n"
            target.write_bytes(original)
            result = subprocess.run([sys.executable, str(HERE / "prepare_native_probe.py"), str(root)], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(target.read_bytes(), original)

if __name__ == "__main__":
    unittest.main()
