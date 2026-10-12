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
