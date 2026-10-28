"""Negative tests for the OpenQASM AST simulator's input checks."""

import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch

import numpy as np
import openqasm3

from compile_check import Program, main


class ProgramRefusalTests(unittest.TestCase):
    def test_empty_output_directory_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch("compile_check.OUT_DIR", directory):
                with self.assertRaises(SystemExit) as result:
                    main()
                self.assertNotEqual(result.exception.code, 0)

    def test_missing_expected_leaves_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            Path(directory, "example.qasm").write_text("OPENQASM 3.0;\n")
            with patch("compile_check.OUT_DIR", directory):
                with self.assertRaises(SystemExit) as result:
                    main()
                self.assertNotEqual(result.exception.code, 0)

    def run_program(self, source):
        program = Program(openqasm3.parse(source))
        state = np.zeros((2,) * program.nq, dtype=complex)
        state[(0,) * program.nq] = 1
        return program.run_stmts(program.body, state, {})

    def test_empty_program_has_unit_amplitude(self):
        branches = self.run_program("OPENQASM 3.0;\n")
        self.assertEqual(len(branches), 1)
        state, bits = branches[0]
        self.assertEqual(state.shape, ())
        self.assertEqual(complex(state), 1)
        self.assertEqual(bits, {})

    def test_zero_width_quantum_register_is_refused(self):
        with self.assertRaisesRegex(ValueError, "positive"):
            self.run_program("OPENQASM 3.0; qubit[0] q;\n")

    def test_boolean_literals_select_the_expected_arm(self):
        for literal, expected in (("true", [0, 1]), ("false", [1, 0])):
            with self.subTest(literal=literal):
                source = f"""OPENQASM 3.0;
qubit[1] q;
if ({literal}) {{ x q[0]; }} else {{ }}
"""
                branches = self.run_program(source)
                self.assertEqual(len(branches), 1)
                self.assertTrue(np.allclose(branches[0][0], expected))

    def test_parentheses_preserve_boolean_grouping(self):
        cases = (("(true || false) && false", [1, 0]),
                 ("true || (false && false)", [0, 1]))
        for condition, expected in cases:
            with self.subTest(condition=condition):
                source = f"""OPENQASM 3.0;
qubit[1] q;
if ({condition}) {{ x q[0]; }} else {{ }}
"""
                branches = self.run_program(source)
                self.assertEqual(len(branches), 1)
                self.assertTrue(np.allclose(branches[0][0], expected))

    def test_literal_in_lifted_guard_keeps_record_weights(self):
        source = """OPENQASM 3.0;
qubit[2] q;
bit[1] c;
h q[0];
c[0] = measure q[0];
if ((c[0] == 1) && true) { x q[1]; } else { }
"""
        branches = self.run_program(source)
        self.assertEqual(len(branches), 2)
        for state, bits in branches:
            bit = bits[("c", 0)]
            expected = np.zeros(4, dtype=complex)
            expected[3 * bit] = 1 / np.sqrt(2)
            self.assertTrue(np.allclose(state.reshape(-1), expected))
            self.assertAlmostEqual(float(np.vdot(state, state).real), 0.5)

    def test_global_phase_is_retained_without_qubits(self):
        branches = self.run_program("OPENQASM 3.0; gphase((pi + pi)/4);\n")
        self.assertEqual(len(branches), 1)
        state, bits = branches[0]
        self.assertEqual(state.shape, ())
        self.assertAlmostEqual(complex(state), 1j)
        self.assertEqual(bits, {})

    def test_unsupported_condition_is_refused_by_name(self):
        source = "OPENQASM 3.0; qubit[1] q; if (1 < 2) { x q[0]; }\n"
        with self.assertRaisesRegex(ValueError, "unsupported condition"):
            self.run_program(source)

    def test_condition_on_unmeasured_bit_is_refused(self):
        source = """OPENQASM 3.0;
qubit[2] q;
bit[1] c;
bit[1] result;
if (c[0] == 1) { x q[0]; } else { }
result[0] = measure q[0];
"""
        with self.assertRaisesRegex(ValueError, "no measurement has written"):
            self.run_program(source)

    def test_bit_index_past_declared_width_is_refused(self):
        source = """OPENQASM 3.0;
qubit[2] q;
bit[1] c;
bit[1] result;
c[3] = measure q[1];
result[0] = measure q[0];
"""
        with self.assertRaisesRegex(ValueError, "past the declared width"):
            self.run_program(source)


if __name__ == "__main__":
    unittest.main()
