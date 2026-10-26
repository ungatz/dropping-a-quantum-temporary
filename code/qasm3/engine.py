"""engine.py -- the machine of the language, numerically (tolerance 1e-8).

The exact engine is the Haskell package next door; this is the floating-point
one the two benchmark scripts in this directory run on.

What it computes, on a program whose statements form a TREE (an `if` has no
continuation, so a lift may sit inside a branch and conditionals may nest):

  A  K# = sum_o |beta(o)> (x) E_o(c)      the deferred-measurement form: the
                                          record-indexed family, stacked
  B  a composite drop of (t, r) safe  =>  every record's drop safe (the
                                          converse fails)
  C  a composite drop is safe  <=>  the command's channel on v is unitary,
                                    i.e. has one Kraus operator
  D  reading r at the end (l commuting lifts on the composite) reproduces
     E_o(c)

Registers are named; the temporaries are the non-`vis` registers; every state
is an unnormalised vector in the tensor product of the registers in declared
order.  A record is a LEAF -- the outcomes read along one path -- and the
stacking (A) runs over leaves, with |0> at the record positions a leaf never
read.  The "weight" printed is tr(Gamma)/m, the average over the maximally
mixed visible input, not the paper's weight at one unit input (which for
teleport.s depends on the input).
"""
import numpy as np, itertools
from functools import reduce
np.set_printoptions(precision=4, suppress=True, linewidth=160)
kron = lambda *ms: reduce(np.kron, ms)
I2 = np.eye(2); X = np.array([[0,1],[1,0]]); Z = np.diag([1,-1]); H = np.array([[1,1],[1,-1]])/np.sqrt(2)
CZ = np.diag([1,1,1,-1.]); CX = np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0.]])
CCX = np.eye(8); CCX[6:8,6:8] = X
tilt = np.array([[2,2,1],[2,-1,-2],[1,-2,2]])/3
X3 = np.roll(np.eye(3),1,axis=0)
READ3 = sum(np.kron(np.outer(np.eye(3)[t],np.eye(3)[t]), np.linalg.matrix_power(X3,t)) for t in range(3))  # t first: |t x> -> |t, x+t>; the .s gate READ3 x t is this with x named first

class Regs:
    def __init__(self, regs): self.names=[n for n,_ in regs]; self.dims=[d for _,d in regs]
    def dim(self): return int(np.prod(self.dims))
    def embed(self, names, U):
        """U acts on the listed registers (in that order); return it on the whole space."""
        idx = [self.names.index(n) for n in names]
        rest = [i for i in range(len(self.names)) if i not in idx]
        d_sub = int(np.prod([self.dims[i] for i in idx])); d_rest = int(np.prod([self.dims[i] for i in rest]))
        assert U.shape == (d_sub, d_sub), (names, U.shape)
        full = np.kron(U, np.eye(d_rest)).reshape([self.dims[i] for i in idx+rest]*2)
        perm = np.argsort(idx+rest); n = len(self.names)
        full = full.transpose(list(perm) + [n+p for p in perm])
        return full.reshape(self.dim(), self.dim())
    def proj(self, name, block):
        d = self.dims[self.names.index(name)]; P = np.zeros((d,d))
        for s in block: P[s,s] = 1
        return self.embed([name], P)
    def basis(self, assign):   # dict name->index for some registers; others |0>
        v = np.ones((1,1))
        for n,d in zip(self.names,self.dims):
            e = np.zeros((d,1)); e[assign.get(n,0)] = 1; v = np.kron(v,e)
        return v

# A program is a list of statements over the *original* registers:
#  ('gate', [names], U) | ('lift', p, name, block) | ('if', p, [stmts], [stmts])
# Branches may themselves contain lifts and conditionals (the paper's tree).
def run_record(R, prog, inp, record):
    """The machine along `record` (a list of 'in'/'out' in program order), unnormalised: E_o(c) inp."""
    psi = inp.copy(); store = {}; it = iter(record)
    def go(stmts):
        nonlocal psi
        for s in stmts:
            if s[0]=='gate': psi = R.embed(s[1], s[2]) @ psi
            elif s[0]=='lift':
                b = next(it); _, p, name, block = s
                P = R.proj(name, block) if b=='in' else np.eye(R.dim()) - R.proj(name, block)
                psi = P @ psi; store[p] = 1 if b=='in' else 0
            elif s[0]=='if': go(s[2] if store[s[1]] else s[3])
    go(prog); return psi

def run_assign(R, prog, inp, assign):
    """The machine with outcomes looked up BY LIFT NAME (a tree may read only some);
    returns (E_leaf inp, the dict of names actually read)."""
    psi = inp.copy(); store = {}; read = {}
    def go(stmts):
        nonlocal psi
        for s in stmts:
            if s[0]=='gate': psi = R.embed(s[1], s[2]) @ psi
            elif s[0]=='lift':
                _, p, name, block = s; b = assign[p]; read[p] = b
                P = R.proj(name, block) if b=='in' else np.eye(R.dim()) - R.proj(name, block)
                psi = P @ psi; store[p] = 1 if b=='in' else 0
            elif s[0]=='if': go(s[2] if store[s[1]] else s[3])
    go(prog); return psi, read

def lifts_of(prog):
    """Every lift OCCURRENCE in the tree, in program order (branches after their guard)."""
    out = []
    for s in prog:
        if s[0]=='lift': out.append(s)
        elif s[0]=='if': out += lifts_of(s[2]) + lifts_of(s[3])
    return out

def leaves_of(R, prog):
    """The reached records of a tree: distinct partial assignments actually read."""
    ls = lifts_of(prog); seen = {}
    for o in itertools.product(['in','out'], repeat=len(ls)):
        assign = dict(zip([s[1] for s in ls], o))
        _, read = run_assign(R, prog, R.basis({}), assign)
        key = tuple(sorted(read.items()))
        seen.setdefault(key, assign)
    return seen   # leaf (as sorted items) -> one full assignment extending it

def dmp(R, prog):
    """The deferred-measurement embedding: registers R# = R + one qubit r_p per lift
    OCCURRENCE in the tree; a lift -> a copy gate on (t, r_p); a conditional -> the
    controlled unitary  P1 (x) U(c1#) + P0 (x) U(c0#)  where U(c#) is the total
    unitary of the branch's own deferred program (which may hold copies and nested
    controls of its own). Returns (R#, prog#) with prog# lift-free."""
    ls = lifts_of(prog)
    R2 = Regs(list(zip(R.names, R.dims)) + [('r_'+s[1], 2) for s in ls])
    def defer(stmts):
        out = []
        for s in stmts:
            if s[0]=='gate': out.append(s)
            elif s[0]=='lift':
                _, p, name, block = s; d = R.dims[R.names.index(name)]
                C = np.zeros((2*d, 2*d))          # on (name, r_p): |i,b> -> |i, b xor [i in block]>
                for i in range(d):
                    for b in range(2):
                        C[i*2 + (b ^ (1 if i in block else 0)), i*2 + b] = 1
                out.append(('gate', [name, 'r_'+p], C))
            elif s[0]=='if':
                _, p, c1, c0 = s
                U1 = total(defer(c1)); U0 = total(defer(c0))
                P1 = R2.proj('r_'+p, [1]); P0 = np.eye(R2.dim()) - P1
                out.append(('full', P1 @ U1 + P0 @ U0))   # block diagonal in r_p; U1, U0 never touch r_p
        return out
    def total(stmts):
        return reduce(lambda acc,s: (R2.embed(s[1],s[2]) if s[0]=='gate' else s[1]) @ acc, stmts, np.eye(R2.dim()))
    return R2, defer(prog)

def run_plain(R, prog, inp):
    psi = inp.copy()
    for s in prog:
        psi = (R.embed(s[1], s[2]) if s[0]=='gate' else s[1]) @ psi
    return psi

def verdict(K, d, m):
    Ks = [K[i*m:(i+1)*m,:] for i in range(d)]
    M = np.array([B.reshape(-1) for B in Ks]); G = M @ M.conj().T; tr = np.trace(G).real
    if tr < 1e-12: return 'UNREACHABLE', tr
    Gn = G/tr; return ('SAFE' if np.allclose(Gn@Gn, Gn) else 'UNSAFE'), tr

def analyse(title, regs, vis, prog):
    R = Regs(regs); m = int(np.prod([d for n,d in regs if n in vis])); tmp = [n for n,_ in regs if n not in vis]
    ls = lifts_of(prog); L = len(ls)
    print(f"\n==== {title}: temporaries {tmp}, visible {vis} (m={m}), {L} lift(s)")
    # order every state as (temporaries..., visible...) : build a permutation to that order
    order = tmp + vis
    def reorder(R_, psi, front):   # bring registers `front` (list) to the front, rest after in declared order
        rest = [n for n in R_.names if n not in front]; idx = [R_.names.index(n) for n in front+rest]
        return psi.reshape(R_.dims).transpose(idx).reshape(-1,1)
    vis_basis = list(itertools.product(*[range(d) for n,d in regs if n in vis]))
    def column(R_, psi_fn):
        cols = []
        for vb in vis_basis:
            assign = dict(zip(vis, vb)); cols.append(psi_fn(R_.basis(assign)))
        return np.hstack(cols)
    d = int(np.prod([dd for n,dd in regs if n in tmp]))
    names = [s[1] for s in ls]
    # per record = per LEAF of the tree (a top-level command's leaves are all 2^L assignments)
    leaves = leaves_of(R, prog)
    E = {}; label = {}
    for key, assign in leaves.items():
        K = column(R, lambda inp: reorder(R, run_assign(R, prog, inp, assign)[0], tmp))
        read = dict(key); E[key] = K; v, w = verdict(K, d, m)
        # the record label: the read bit at read positions, 0 (unread) elsewhere
        label[key] = tuple((1 if read[p]=='in' else 0) if p in read else 0 for p in names)
        shown = ''.join((read[p][0] if p in read else '.') for p in names) or '-'
        print(f"  record {shown:>4}: weight {w/m:.4f}  drop {tmp}: {v}")
    nreach = sum(1 for key in leaves if verdict(E[key], d, m)[0] != 'UNREACHABLE')
    if L and len(leaves) != 2**L: print(f"  tree: {len(leaves)} leaves for {L} lift occurrences ({nreach} reachable)")
    # DMP
    R2, prog2 = dmp(R, prog); rnames = ['r_'+p for p in names]
    Ksharp = column(R2, lambda inp: reorder(R2, run_plain(R2, prog2, inp), rnames + tmp))
    stacked = sum(np.kron(kron(*[np.eye(2)[b].reshape(2,1) for b in label[key]]) if L else np.ones((1,1)), E[key]) for key in leaves)
    print(f"  A: K# == sum_leaves |beta~(o)> (x) E_o ? {np.allclose(Ksharp, stacked)}   (K# is {Ksharp.shape[0]}x{Ksharp.shape[1]}, isometry: {np.allclose(Ksharp.T@Ksharp, np.eye(m))})")
    big, _ = verdict(Ksharp, (2**L)*d, m)
    print(f"  B: composite drop of (record, {tmp}): {big}")
    # channel on v
    D = (2**L)*d; blocks = [Ksharp[i*m:(i+1)*m,:] for i in range(D)]
    Kr = np.array([B.reshape(-1) for B in blocks]); rank = np.linalg.matrix_rank(Kr, tol=1e-9)
    print(f"  C: number of independent Kraus operators of the channel = {rank}  -> channel {'unitary' if rank==1 else 'not unitary'}")
    # D: read the record at the end of the DMP'd program (L commuting lifts on r): the row
    #    labelled beta~(leaf) equals E_leaf; every other full assignment is unreachable
    ok = True; bylabel = {label[key]: key for key in leaves}
    for o in itertools.product([1,0], repeat=L):
        P = np.eye(R2.dim())
        for p, b in zip(names, o): P = P @ R2.proj('r_'+p, [b])
        Ko = column(R2, lambda inp: reorder(R2, P @ run_plain(R2, prog2, inp), rnames + tmp))
        idx = sum((b << (L-1-k)) for k,b in enumerate(o)) if L else 0
        slab = Ko[idx*d*m:(idx+1)*d*m, :]
        ok &= np.allclose(slab, E[bylabel[o]]) if o in bylabel else np.allclose(slab, 0)
    print(f"  D: reading the record at the end reproduces every E_o(c) (other rows unreachable): {ok}")
    return E, Ksharp

