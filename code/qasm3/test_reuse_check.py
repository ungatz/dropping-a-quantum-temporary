"""Channel-check falsifiers: allocation, ordered returns, and preparation."""
import unittest
import tempfile

import numpy as np
import openqasm3

import reuse_check as checker


def allocation(*, temp_basis=1):
    return {
        "freshQubits": 2,
        "reuseQubits": 2,
        "wires": [
            {"name": "x", "kind": "input", "fresh": [0], "reuse": [0], "basis": None},
            {"name": "t", "kind": "temporary", "fresh": [1], "reuse": [1], "basis": temp_basis},
        ],
        "returns": [["x"]],
        "lifts": [],
        "sites": [],
    }


def qasm(prepare=True, result_qubit=0):
    prep = "x q[1];" if prepare else ""
    return f"""OPENQASM 3.0;
qubit[2] q;
bit[1] result;
{prep}
cx q[1], q[0];
result[0] = measure q[{result_qubit}];
"""


class ReuseChannelTests(unittest.TestCase):
    def test_temporary_wire_mappings_may_repeat_but_scratch_begins_as_zero(self):
        data = allocation()
        data["wires"].append(
            {"name": "u", "kind": "temporary", "fresh": [2], "reuse": [1], "basis": 0}
        )
        program = checker.sim.Program(openqasm3.parse("OPENQASM 3.0; qubit[2] q;"))
        width, _, inputs, loans, temp_bits = checker.validate_allocation(data, program, "reuse")
        self.assertEqual(width, 2)
        self.assertEqual(inputs, [0])
        self.assertEqual(loans, [])
        self.assertEqual(temp_bits, {})
        state = checker.initial_state(width, inputs, loans, temp_bits)
        self.assertEqual(np.argmax(np.abs(state.reshape(-1))), 0)

    def test_nonbasis_temporary_is_rejected(self):
        data = allocation(temp_basis=None)
        program = checker.sim.Program(openqasm3.parse("OPENQASM 3.0; qubit[2] q;"))
        with self.assertRaisesRegex(ValueError, "non-basis temporary"):
            checker.validate_allocation(data, program, "fresh")

    def test_loan_without_ordinary_inputs_is_still_a_quantum_input(self):
        data = {
            "freshQubits": 1, "reuseQubits": 1,
            "wires": [{"name": "a", "kind": "loan", "fresh": [0], "reuse": [0], "basis": None}],
            "returns": [["a"]], "lifts": [], "sites": [],
        }
        program = checker.sim.Program(openqasm3.parse("OPENQASM 3.0; qubit[1] q;"))
        width, _, inputs, loans, temp_bits = checker.validate_allocation(data, program, "fresh")
        state = checker.initial_state(width, inputs, loans, temp_bits).reshape(-1)
        self.assertEqual(inputs, [])
        self.assertEqual(loans, [0])
        self.assertTrue(np.allclose(state, [1 / np.sqrt(2), 0, 0, 1 / np.sqrt(2)]))

    def test_wrong_ordered_output_mapping_is_rejected(self):
        data = allocation()
        program = checker.sim.Program(openqasm3.parse(qasm(result_qubit=1)))
        reads = checker.result_measurements(program)
        _, wires, *_ = checker.validate_allocation(data, program, "fresh")
        returned = tuple(q for name in data["returns"][0] for q in wires[name])
        self.assertNotEqual(reads, returned)
        with self.assertRaisesRegex(ValueError, "result measures"):
            checker.channels(qasm(result_qubit=1), data, "fresh")

    def test_missing_basis_preparation_changes_the_channel(self):
        data = allocation()
        fresh, *_ = checker.channels(qasm(prepare=True), data, "fresh")
        changed, *_ = checker.channels(qasm(prepare=False), data, "fresh")
        ok, deviation, _ = checker.compare_channels(fresh, changed)
        self.assertFalse(ok)
        self.assertGreater(deviation, checker.TOL)

    def test_result_measurement_before_a_gate_is_rejected(self):
        early = qasm() + "x q[0];\n"
        with self.assertRaisesRegex(ValueError, "must be terminal"):
            checker.channels(early, allocation(), "fresh")

    def test_duplicate_result_bit_is_rejected(self):
        duplicate = qasm() + "result[0] = measure q[0];\n"
        with self.assertRaisesRegex(ValueError, "omit or duplicate"):
            checker.channels(duplicate, allocation(), "fresh")

    def test_empty_or_nonfinite_channel_comparison_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "no records"):
            checker.compare_channels({}, {})
        with self.assertRaisesRegex(ValueError, "non-finite"):
            checker.compare_channels({(): np.array([[np.nan]])}, {(): np.array([[0]])})

    def test_empty_suite_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(SystemExit):
                checker.main(["--dqt", "dqt", "--programs", directory])


if __name__ == "__main__":
    unittest.main()
