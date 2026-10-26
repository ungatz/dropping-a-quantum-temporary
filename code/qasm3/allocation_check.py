"""Check pool admission and zero state at each released block."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

import numpy as np
import openqasm3

import compile_check as sim
import reuse_check as reuse


def check_pools(qasm, data):
    """Inspect each release before later operations can conceal a bad return."""
    pooled = {s['site']: s for s in data['sites'] if s['pooled']}
    seen = set()
    def checkpoint(match):
        site = int(match.group(1))
        if site not in pooled:
            raise AssertionError(f"unexpected pool site {site}")
        seen.add(site)
        qs = ', '.join(f'q[{q}]' for q in pooled[site]['reuse'])
        return f'barrier {qs};'
    instrumented = re.sub(r'// pool site (\d+):[^\n]*', checkpoint, qasm)
    if seen != set(pooled):
        raise AssertionError('missing pool checkpoint')

    class PoolProgram(sim.Program):
        checked = 0
        def run_stmts(self, stmts, state, bits):
            if stmts and isinstance(stmts[0], openqasm3.ast.QuantumBarrier):
                targets = [sim.qubit_index(q) for q in stmts[0].qubits]
                index = [slice(None)] * state.ndim
                for q in targets:
                    index[q] = 0
                residual = state.copy()
                residual[tuple(index)] = 0
                outside = float(np.linalg.norm(residual.ravel()))
                if outside > reuse.TOL:
                    raise AssertionError(f'block {targets} entered the pool outside zero')
                self.checked += 1
                return self.run_stmts(stmts[1:], state, bits)
            return super().run_stmts(stmts, state, bits)

    program = PoolProgram(openqasm3.parse(instrumented))
    reuse.result_measurements(program)
    width, _, inputs, loans, temps = reuse.validate_allocation(data, program, 'reuse')
    state = reuse.initial_state(width, inputs, loans, temps)
    program.nq = state.ndim
    program.run_stmts(program.body, state, {})
    return program.checked


def report(exe, path):
    return json.loads(reuse.run_command(exe, 'allocation', path))


def boundary_checks(exe, programs):
    tests = 0
    def require(condition, label):
        nonlocal tests
        if not condition:
            raise AssertionError(label)
        tests += 1
    def sites(name):
        return report(exe, programs / name)['sites']
    require(all(s['pooled'] for s in sites('two-phases.s')), 'fixed nonbasis certificate can be restored and pooled')
    require(all(s['pooled'] for s in sites('measured-and-twice.s')), 'all reachable measured records can be pooled')
    require(all(s['pooled'] for s in sites('bell-pair.s')), 'joint Bell block can be restored')
    require(not any(s['pooled'] for s in sites('bell-pair-split.s')), 'separate Bell drops must not enter pool')
    c = sites('c-decomposed.s')
    require(not any(s['pooled'] for s in c), 'one safe record is insufficient for this allocator')
    require({r['verdict'] for r in c[0]['records']} == {'safe', 'unsafe'}, 'program (c) keeps both verdicts')
    require(not any(s['pooled'] for s in sites('mcx-dirty-x.s')), 'loans are not scratch')
    # a non-basis allocation is outside the compilation fragment: the
    # emitter refuses it before any pool decision
    try:
        report(exe, programs.parent / 'test/fixtures/dirty-nonbasis.s')
        require(False, 'nonbasis allocation is refused as outside the fragment')
    except subprocess.CalledProcessError:
        require(True, 'nonbasis allocation is refused as outside the fragment')
    cases = {
        'block': 'prog p (x:[2]) : [2]*[2]*[2] { new t:[4] @ |3>; drop t; new u:[2] @ |1>; new v:[2] @ |0>; return (x,u,v) }',
        'reversed': 'prog p (x:[2]) : [2]*[4] { new a:[2] @ |1>; new b:[2] @ |0>; H b; drop (b,a); new t:[4] @ |2>; return (x,t) }',
        'unreachable': 'prog p (x:[2]) : [2] { new t:[2] @ |0>; p=lift[{1}] t; drop t; new u:[2] @ |0>; drop u; return x }',
        'indicator': 'prog p (x:[2]) : [2]*[4] { new t:[2] @ |0>; drop t; new a:[4] @ |0>; p=lift[{0}] a; drop a; new b:[4] @ |0>; return (x,b) }',
        'mixed': 'prog p (x:[2], loan a:[2]) : [2] { new t:[2] @ |0>; H t; X a; drop (t,a); return x }',
        'empty': 'prog p (x:[2]) : [2] { drop (); return x }',
        'input': 'prog p (x:[2]) : [2] { drop x; new t:[2] @ |0>; return t }',
        'unsupported': 'prog p (x:[2], loan a:[2], loan b:[2]) : [2] { H a; CX a b; drop (a,b); return x }',
    }
    with tempfile.TemporaryDirectory() as tmp:
        for name, source in cases.items():
            path = Path(tmp) / (name + '.s')
            path.write_text(source)
            data = report(exe, path)
            if name == 'block':
                require(data['reuseQubits'] == 3 and data['freshQubits'] == 5, 'split a restored basis block into later lifetimes')
                result = reuse.check_file(exe, path)
                require(result['ok'], 'nonzero basis preparation after block reuse')
            elif name == 'reversed':
                require(data['reuseQubits'] == 3, 'reversed tuple order reuses the block')
                require(reuse.check_file(exe, path)['ok'], 'reversed tuple preserves output order and preparation')
                require(check_pools(reuse.run_command(exe, 'compile-reuse', path), data) > 0, 'reversed tuple actually restored')
            elif name == 'unreachable':
                require(data['sites'][0]['pooled'], 'zero-weight record does not prevent pooling a safe block')
                require({r['verdict'] for r in data['sites'][0]['records']} == {'safe', 'unreachable'}, 'zero record is reported explicitly')
                require(reuse.check_file(exe, path)['ok'], 'zero and nonzero records agree after reuse')
            elif name == 'indicator':
                require(data['reuseQubits'] == 4, 'indicator has its own reserved wire')
                used = {q for w in data['wires'] for q in w['reuse']}
                require(set(range(4)) - used == {3}, 'indicator never aliases a program register')
                require(reuse.check_file(exe, path)['ok'], 'block-lift records preserved through reuse')
                require(check_pools(reuse.run_command(exe, 'compile-reuse', path), data) > 0, 'block-lift temporary restored')
            elif name == 'mixed':
                require(not data['sites'][0]['pooled'], 'mixed loan/temporary block never enters scratch pool')
                require(data['sites'][0]['records'][0]['restoration'] == 'emitted', 'mixed block can be restored without pooling loan')
            elif name == 'empty':
                require(not data['sites'][0]['pooled'], 'empty block does not allocate pool wires')
            elif name == 'input':
                require(not data['sites'][0]['pooled'], 'an ordinary input is not scratch')
            elif name == 'unsupported':
                # once outside the emitter's shapes; the general return gate
                # now returns every safe loan block,
                # and a returned loan still goes back to the caller, never
                # to the pool
                require(not data['sites'][0]['pooled'], 'a returned loan block does not release wires')
                require(data['sites'][0]['records'][0]['restoration'] == 'emitted', 'the general return gate is emitted')
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dqt', required=True)
    parser.add_argument('--programs', type=Path, required=True)
    args = parser.parse_args()
    boundaries = boundary_checks(args.dqt, args.programs)
    checkpoints = 0
    for name in ['two-phases.s', 'grover-two-rounds.s', 'measured-and-twice.s', 'bell-pair.s']:
        source = args.programs / name
        data = report(args.dqt, source)
        qasm = reuse.run_command(args.dqt, 'compile-reuse', source)
        checkpoints += check_pools(qasm, data)
    # Remove restoration while leaving its release marker: the checkpoint
    # must fail even if there is no later use of that wire.
    source = args.programs / 'two-phases.s'
    data = report(args.dqt, source)
    qasm = reuse.run_command(args.dqt, 'compile-reuse', source)
    marker = '// pool site 0:'
    before, separator, after = qasm.partition(marker)
    gates = data['sites'][0]['records'][0]['gates']
    if len(gates) != 1 or not before.endswith(gates[0] + '\n') or not separator:
        raise AssertionError('first release does not have the expected adjacent restoration')
    mutant = before[:-len(gates[0] + '\n')] + separator + after
    try:
        check_pools(mutant, data)
    except AssertionError:
        pass
    else:
        raise AssertionError('pool check missed a deleted restoration')
    print(json.dumps({'admissionChecks': boundaries, 'checkpointBranches': checkpoints,
                      'deletedRestorationRejected': True}, indent=2))


if __name__ == '__main__':
    main()
