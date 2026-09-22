"""s_bench.py -- what the verdict buys a reuse schedule, counted.

Reads the artifact's `.s` corpus (a small parser for the surface syntax, on
engine.py) and three generated families, and for EVERY drop site
prints the per-record verdict on the cut {dropped register} | rest, then the
price of three schedules for that temporary:

  measure+reset  the qubit-reuse compilers' schedule (DeCross et al. 2210.08039;
                 Hua et al., CaQR, ASPLOS '23): one mid-circuit measurement and
                 one reset per temporary, paid on EVERY shot.
  uncompute      the pebble-game schedule (Bennett 1989; Kornerup et al. 2025):
                 the temporary's own gates run again in reverse -- counted here
                 as the number of gate occurrences that touch the temporary
                 before its drop (a lower bound on the uncomputation), per shot.
  this paper     a safe drop needs neither: 0 measurements, 0 extra gates per
                 shot; the price is the VERDICT, paid once at compile time:
                 one exact pass per reachable record (the pass's matrix is
                 (d*m) x m for temporary dimension d and visible dimension m).
                 An unsafe drop is refused, and the schedule falls back to the
                 baseline for that temporary (counted as such).

Verdicts are numerical (numpy, tolerance 1e-8); the artifact's are exact.
Run from this directory:  nice -n 19 python3 s_bench.py
"""
import re, sys, itertools, numpy as np
src = open('engine.py').read().split('# ---- programs')[0]
exec(src)
np.set_printoptions(precision=3, suppress=True, linewidth=140)

# ---- gates of the S table ---------------------------------------------------
I2 = np.eye(2); Xg = np.array([[0,1],[1,0]]); Zg = np.diag([1,-1]); Hg = np.array([[1,1],[1,-1]])/np.sqrt(2)
Sg = np.diag([1,1j]); Tg = np.diag([1,np.exp(1j*np.pi/4)])
CXg = np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]])            # control first
CCXg = np.eye(8); CCXg[6,6]=CCXg[7,7]=0; CCXg[6,7]=CCXg[7,6]=1        # Toffoli(c1,c2; t)
SWAPg = np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
plus2 = np.ones(4)/2; DIFFg = 2*np.outer(plus2,plus2) - np.eye(4)
READ3s = sum(np.kron(np.linalg.matrix_power(X3,t), np.outer(np.eye(3)[t],np.eye(3)[t])) for t in range(3))  # x first: |x t> -> |x+t, t>
GATES = {'H':Hg,'HC':Hg,'X':Xg,'Z':Zg,'S':Sg,'T':Tg,'CX':CXg,'CCX':CCXg,'Swap':SWAPg,'tilt':tilt,'READ3':READ3s,'Diff':DIFFg}

def mcx(n):
    """n-controlled X on n+1 qubits, controls first."""
    U = np.eye(2**(n+1)); a, b = 2**(n+1)-2, 2**(n+1)-1
    U[a,a]=U[b,b]=0; U[a,b]=U[b,a]=1; return U

# ---- a parser for the S surface syntax (the syntax figure) --------------------------
#
# The same grammar the Haskell parser reads (programs/SYNTAX.md): optional
# top-level `gate NAME : A = mat {...} | diag (...) | perm (...);`
# declarations, then one `prog f (x : [d], loan a : [d]) : A { ... return v }`.
# A header `loan` is an input register the program is handed in a state it does
# not know, so it carries no declared state and is not seeded: it is varied
# over its own basis, like a visible register, and its drop is decided by the
# block-factor test of the site definition's clause (4) ('loan_verdict' below), not by the
# fixed-ray test a temporary gets.  Seeding a loan at |0> and asking the
# temporary's question instead would call test/fixtures/cz-loan.s SAFE, where the criterion and the Haskell engine
# both say UNSAFE: CZ leaves every basis label of the loan fixed, so the ray
# test passes, and no fixed B on the loan alone reproduces the joint action.
SYMS = set(':;,@(){}[]=^*/+-|<>!&')

def _tokenize(text):
    text = re.sub(r'--[^\n]*', '', text)
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace(): i += 1; continue
        if c.isdigit():
            j = i
            while j < n and text[j].isdigit(): j += 1
            toks.append(text[i:j]); i = j; continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (text[j].isalnum() or text[j] == '_'): j += 1
            toks.append(text[i:j]); i = j; continue
        if c in SYMS: toks.append(c); i += 1; continue
        raise ValueError('unexpected character %r' % c)
    return toks

def parse_s(text):
    """Returns (regs, vis, loans, starts, stmts) where stmts are dmp_lab statements
    plus ('drop', name) and ('new', name) markers; starts maps a register to its
    start vector (loans and clean |0> allocations have no entry), and loans names
    the header parameters marked `loan`, which are varied over their own basis
    and decided by the block-factor test."""
    toks = _tokenize(text)
    pos = 0
    def peek(k=0): return toks[pos+k] if pos+k < len(toks) else None
    def take(x=None):
        nonlocal pos
        t = toks[pos]; pos += 1
        assert x is None or t == x, (x, t, toks[max(0,pos-6):pos+4]); return t
    def scalar(sexpr):
        z8 = np.exp(1j*np.pi/4); z16 = np.exp(1j*np.pi/8)
        env = {'i':1j, 'z8':z8, 'z16':z16, 'rt2':np.sqrt(2)}
        return complex(eval(sexpr.replace('^','**'), {'__builtins__':{}}, env))
    def scalar_list(closer=')'):
        """Scalars separated by ',' up to `closer`, consuming it."""
        out, cur, depth = [], '', 0
        while True:
            t = take()
            if t == closer and depth == 0:
                out.append(scalar(cur)); return out
            if t == ',' and depth == 0:
                out.append(scalar(cur)); cur = ''; continue
            if t == '(': depth += 1
            if t == ')': depth -= 1
            cur += t
    def ty_dim():
        """A type '1' | '[d]' | A * B, as its total dimension."""
        if peek() == '[': take('['); d = int(take()); take(']')
        elif peek() == '1': take('1'); d = 1
        else: raise ValueError('expected a type, found %r' % peek())
        if peek() == '*': take('*'); d *= ty_dim()
        return d
    def levels():
        take('['); take('{'); ls = [int(take())]
        while peek() == ',': take(','); ls.append(int(take()))
        take('}'); take(']'); return ls
    def names_until(stop):
        ns = []
        while peek() not in stop: ns.append(take())
        return ns

    # top-level gate declarations
    gates = dict(GATES)
    while peek() == 'gate':
        take('gate'); nm = take(); take(':'); d = ty_dim(); take('=')
        gates[nm] = gate_literal(take, peek, scalar_list, d)
        take(';')

    take('prog'); take()                       # the program's name
    take('(')
    regs, vis, loans, starts = [], [], [], {}
    if peek() != ')':
        while True:
            loan = False
            if peek() == 'loan': take('loan'); loan = True
            x = take(); take(':'); take('['); d = int(take()); take(']')
            regs.append((x, d))
            if loan: loans.append(x)            # a loan is dropped, so it is a site
            else:    vis.append(x)
            if peek() == ',': take(','); continue
            break
    take(')'); take(':'); ty_dim(); take('{')

    def block(stop):
        out = []
        while peek() not in stop:
            t = take()
            if t == 'new':
                x = take(); take(':'); take('['); d = int(take()); take(']'); take('@')
                if peek() == '|':
                    take('|'); k = int(take()); take('>')
                    if k != 0:
                        v = np.zeros(d, dtype=complex); v[k] = 1; starts[x] = v
                else:
                    take('('); amps = scalar_list(')')
                    v = np.array(amps, dtype=complex); starts[x] = v/np.linalg.norm(v)
                take(';'); regs.append((x, d)); out.append(('new', x))
            elif t == 'drop':
                # `drop (a, b)` is ONE site (SYNTAX.md, "a tuple drop is one
                # site, not two"), so a tuple drop is stored as one marker
                # holding the tuple of names, not one marker per name; a
                # bare `drop a` keeps the single-name string.
                if peek() == '(':
                    take('('); ns = [take()]
                    while peek() == ',': take(','); ns.append(take())
                    take(')')
                    out.append(('drop', tuple(ns)))
                else:
                    out.append(('drop', take()))
                take(';')
            elif t == 'if':
                g = take()
                if g in ('!', 'not') or peek() in ('&&', '&', '|'):
                    raise NotImplementedError('compound guard in ' + repr(g))
                take('{'); c1 = block({'}'}); take('}')
                take('else'); take('{'); c2 = block({'}'}); take('}')
                if peek() == ';': take(';')
                out.append(('if', g, c1, c2))
            elif t == 'mat':
                ns = names_until({'{'}); take('{')
                rows = []
                while True:
                    row, cur, done = [], '', False
                    while True:
                        u = take()
                        if u == ',': row.append(scalar(cur)); cur = ''; continue
                        if u == ';':
                            row.append(scalar(cur)); break
                        if u == '}':
                            row.append(scalar(cur)); done = True; break
                        cur += u
                    rows.append(row)
                    if done or peek() == '}':
                        if not done: take('}')
                        break
                if peek() == ';': take(';')
                out.append(('gate', ns, np.array(rows, dtype=complex)))
            elif t == 'diag':
                ns = names_until({'('}); take('('); ds = scalar_list(')'); take(';')
                out.append(('gate', ns, np.diag(ds)))
            elif t == 'perm':
                ns = names_until({'('}); take('(')
                img = []
                while peek() != ')': img.append(int(take()))
                take(')'); take(';')
                U = np.zeros((len(img), len(img)), dtype=complex)
                for j, pj in enumerate(img): U[pj, j] = 1      # |j> -> |p_j>
                out.append(('gate', ns, U))
            elif t == 'return':
                if peek() == '(':
                    take('(')
                    while peek() != ')': take()
                    take(')')
                else:
                    take()
                if peek() == ';': take(';')
            elif peek() == '=':                 # a binding: p = lift[S] x;  (the only one used)
                take('=')
                if peek() != 'lift':
                    raise NotImplementedError('binding form %r' % peek())
                take('lift'); ls = levels(); r = take(); take(';')
                out.append(('lift', t, r, ls))
            elif t in gates:
                ns = names_until({';'}); take(';')
                out.append(('gate', ns, gates[t]))
            else:
                raise ValueError('unknown statement ' + t)
        return out

    stmts = block({'}'})
    take('}')
    return regs, vis, loans, starts, stmts

def gate_literal(take, peek, scalar_list, d):
    """The right-hand side of a gate declaration, at total dimension d."""
    kind = take()
    if kind == 'diag':
        take('('); return np.diag(scalar_list(')'))
    if kind == 'perm':
        take('(')
        img = []
        while peek() != ')': img.append(int(take()))
        take(')')
        U = np.zeros((len(img), len(img)), dtype=complex)
        for j, pj in enumerate(img): U[pj, j] = 1
        return U
    if kind == 'mat':
        take('{')
        rows, row, cur = [], [], ''
        while True:
            u = take()
            if u == ',': row.append(scalar_of(cur)); cur = ''; continue
            if u == ';': row.append(scalar_of(cur)); rows.append(row); row = []; cur = ''; continue
            if u == '}':
                if cur.strip() or row: row.append(scalar_of(cur)); rows.append(row)
                break
            cur += u
        return np.array(rows, dtype=complex)
    raise ValueError('unknown gate literal ' + kind)

def scalar_of(sexpr):
    z8 = np.exp(1j*np.pi/4); z16 = np.exp(1j*np.pi/8)
    env = {'i':1j, 'z8':z8, 'z16':z16, 'rt2':np.sqrt(2)}
    return complex(eval(sexpr.replace('^','**'), {'__builtins__':{}}, env))

def strip_markers(stmts):
    out = []
    for s in stmts:
        if s[0] in ('new','drop'): continue
        if s[0] == 'if': out.append(('if', s[1], strip_markers(s[2]), strip_markers(s[3])))
        else: out.append(s)
    return out

def as_names(target):
    """A drop site's target, normalised to a tuple of names: a bare `drop a`
    stores the string 'a', a tuple drop `drop (a, b)` stores the tuple
    ('a','b')."""
    return (target,) if isinstance(target, str) else tuple(target)

def site_label(target):
    return ','.join(as_names(target))

def prefix_through_drop(stmts, name):
    """The program up to and including the drop of `name` (the S engine's rule),
    with markers stripped; drops inside branches are not in the corpus."""
    out = []
    for s in stmts:
        if s[0] == 'drop' and s[1] == name: return strip_markers(out)
        out.append(s)
    raise ValueError('no drop of ' + repr(name))

def gates_touching(stmts, name):
    names = as_names(name)
    n = 0
    for s in stmts:
        if s[0] == 'gate' and any(x in s[1] for x in names): n += 1
        elif s[0] == 'if': n += gates_touching(s[2], name) + gates_touching(s[3], name)
    return n

# ---- the verdict on one cut -----------------------------------------------------

def loan_verdict(cols, d, D, dl, n_other):
    """the site definition's clause (4) at a block that IS one loan: the site map factors as
    sigma_s = B (x) W, with B : H_loan -> H_block a block factor, iff the
    reshape that groups (block output, loan input) against (rest output, every
    other input) has rank 1 -- and then B, read back as the d x dl factor, is
    an isometry up to scale, B^dagger B = t.I with t != 0.

    `cols` is indexed [loan_input][other_input] and holds the full state with
    the block's registers already permuted to the front.  The Haskell engine
    does exactly this (Drop.Lang.Interp.loanResult); the fixed-ray test a
    temporary gets is a different, and here unsound, question.

    Returns (verdict, tr, B) with B the (d x dl) block factor when SAFE
    (unnormalised: B^dagger B = t.I, t the same t returned alongside it via
    the caller reading G[0,0] again), else B is None."""
    M = np.zeros((d, D, dl, n_other), dtype=complex)
    for lk in range(dl):
        for oj in range(n_other):
            M[:, :, lk, oj] = cols[lk][oj].reshape(d, D)
    tr = float(np.real(np.vdot(M, M)))
    if tr < 1e-12: return 'UNREACHABLE', tr, None
    A = M.transpose(0, 2, 1, 3).reshape(d * dl, D * n_other)
    u, sv, _ = np.linalg.svd(A)
    if len(sv) > 1 and sv[1] > 1e-8 * sv[0]: return 'UNSAFE', tr, None   # rank > 1: no B (x) W
    B = (u[:, 0] * sv[0]).reshape(d, dl)
    G = B.conj().T @ B
    t = G[0, 0]
    if abs(t) < 1e-12 or not np.allclose(G, t * np.eye(dl), atol=1e-8):
        return 'UNSAFE', tr, None                                  # B is not an isometry up to scale
    return 'SAFE', tr, B

def temp_certificate(K, d, D):
    """The (d,)-certificate ray g of a SAFE temporary record, up to a global
    phase, recovered from K (rows ordered temp-major: row i*D+j is temp
    basis state i, 'rest' index j) the same way `loan_verdict` reads B off
    its reshape: K = g (x) W is rank 1 in the (temp) vs (rest, column)
    split, so g is the top left singular vector of that reshape -- the
    verdict's own G = M @ M^dagger (engine.py's `verdict`) has this g as its
    top eigenvector; SVD of M is the numerically direct way to it."""
    ncols = K.shape[1]
    M = K.reshape(d, D, ncols).reshape(d, D * ncols)
    u, _, _ = np.linalg.svd(M, full_matrices=False)
    return u[:, 0]

def alloc_psi(regs, starts, names):
    """The allocation state psi of a temporary block: the |0> (or the stated
    `new ... @ ...` amplitude vector) of each named register, kron'd in the
    order the drop names them -- the first name on the high (slowest-
    varying) factor, matching `to_front`'s ordering below."""
    dims = dict(regs)
    def e0(n):
        v = np.zeros(dims[n], dtype=complex); v[0] = 1; return v
    out = None
    for n in names:
        v = starts.get(n, e0(n))
        out = v if out is None else np.kron(out, v)
    return out

def householder_reflection(psi, g):
    """The reclaiming proposition's gate, R = I - 2 w w^dagger / ||w||^2
    through w = psi - g~, R = I when w = 0 (g already proportional to psi);
    g~ is g phase-aligned to psi by <psi, g~> real positive when <psi, g> !=
    0, else by its own first nonzero coordinate real positive.  This is
    Drop.Lang.Compile.reflectionR, re-derived here from the certificate, not
    read off the compiler."""
    ip = np.vdot(psi, g)          # <psi, g> = sum conj(psi_i) g_i
    if abs(ip) > 1e-9:
        gTilde = g * np.exp(-1j * np.angle(ip))
    else:
        nz = np.nonzero(np.abs(g) > 1e-9)[0]
        j = int(nz[0]) if len(nz) else 0
        gTilde = g * np.exp(-1j * np.angle(g[j]))
    w = psi - gTilde
    wnorm2 = float(np.vdot(w, w).real)
    n = len(psi)
    if wnorm2 < 1e-18:
        return np.eye(n, dtype=complex)
    return np.eye(n, dtype=complex) - 2 * np.outer(w, w.conj()) / wnorm2

def fmt_complex(z, places=4):
    z = complex(z)
    re = round(z.real, places); im = round(z.imag, places)
    if abs(im) < 10 ** (-places): return f"{re:g}"
    if abs(re) < 10 ** (-places): return f"{im:g}i"
    return f"{re:g}{'+' if im >= 0 else '-'}{abs(im):g}i"

def fmt_matrix(M, places=4):
    rows = ["[" + ", ".join(fmt_complex(z, places) for z in row) + "]" for row in M]
    return "[" + "; ".join(rows) + "]"

def normalize_phase(R, tol=1e-9):
    """A gate is a gate up to a global phase (Drop.Lang.Compile.u3OfMatrix's own
    docstring: "equals the given 2x2 unitary up to a global phase" -- the
    reason mcx-dirty-x.s's emitted U(...) is read as X below); a loan's B is
    fixed only up to a positive SCALE by the block-factor SVD used above,
    and this file's SVD leaves its PHASE arbitrary too (unlike a temporary's
    certificate, whose reflection has no residual freedom once psi and g~
    are fixed). Canonicalise by the same tie-break gTilde uses: the first
    nonzero entry of the first column, made real positive."""
    col0 = R[:, 0]
    nz = np.nonzero(np.abs(col0) > tol)[0]
    if len(nz) == 0:
        return R
    ph = col0[int(nz[0])]
    return R / (ph / abs(ph))

def name_gate(R, tol=1e-8):
    """Names the reclaiming gate R by recognising the matrix, tolerance
    1e-8, up to the global phase `normalize_phase` removes: I; X; a
    transposition of two basis states printed `swap |i>,|j>`; (Z-X)/sqrt2;
    otherwise `reflection` and the matrix rounded to 4 places."""
    R = normalize_phase(R)
    n = R.shape[0]
    if np.allclose(R, np.eye(n), atol=tol):
        return 'I'
    if n == 2 and np.allclose(R, np.array([[0, 1], [1, 0]], dtype=complex), atol=tol):
        return 'X'
    if n == 2:
        zx = np.array([[1, -1], [-1, -1]], dtype=complex) / np.sqrt(2)
        if np.allclose(R, zx, atol=tol):
            return '(Z-X)/sqrt2'
    # a permutation matrix (real, entries 0/1, one per row/col) that is a
    # transposition of exactly two basis states, identity elsewhere
    if np.allclose(R.imag, 0, atol=tol):
        Rr = R.real
        if np.allclose(np.abs(Rr - np.round(Rr)), 0, atol=tol) and \
           np.allclose(Rr.T @ Rr, np.eye(n), atol=tol):
            P = np.round(Rr).astype(int)
            moved = [i for i in range(n) if P[i, i] != 1]
            if len(moved) == 2 and P[moved[0], moved[1]] == 1 and P[moved[1], moved[0]] == 1:
                i, j = sorted(moved)
                return f'swap |{i}>,|{j}>'
    return f'reflection {fmt_matrix(R)}'

def drop_verdicts(regs, vis, loans, starts, stmts, name):
    """Per reachable record: the verdict of dropping `name` on the cut name | rest.
    `name` is a single register (a bare `drop a`) or a tuple of registers
    (a tuple drop `drop (a, b)`, one site of block dimension prod of the
    dims, per SYNTAX.md). The site map's domain is the whole input context:
    every basis input of the VISIBLE registers crossed with every basis
    arrival of every loan (other temporaries start at their allocation
    state).  A temporary's block must come out on one fixed ray over that
    whole domain; a loan's is decided by 'loan_verdict'.  Each row also
    carries the certificate needed for the reclaiming-gate column: ('temp',
    g) or ('loan', B), or None on an unsafe/unreachable record."""
    names = as_names(name)
    R = Regs(regs); prog = prefix_through_drop(stmts, name)
    d = int(np.prod([R.dims[R.names.index(n)] for n in names]))
    rest = [n for n in R.names if n not in names]
    m = int(np.prod([dd for n,dd in regs if n in vis]))
    is_loan = any(n in loans for n in names)
    others = [n for n in loans if n not in names]            # loans other than the target
    dl = d if is_loan else 1
    if is_loan and len(names) != 1:
        raise NotImplementedError('a composite loan block is not exercised by this corpus')
    vis_basis = list(itertools.product(*[range(dd) for n,dd in regs if n in vis]))
    oth_basis = list(itertools.product(*[range(R.dims[R.names.index(n)]) for n in others]))
    all_loans = loans
    n_loan_basis = int(np.prod([R.dims[R.names.index(n)] for n in all_loans])) if all_loans else 1
    def start(vb, lassign):
        v = np.ones((1,1))
        for n,dd in zip(R.names, R.dims):
            if n in vis: e = np.zeros((dd,1)); e[vb[vis.index(n)]] = 1
            elif n in lassign: e = np.zeros((dd,1)); e[lassign[n]] = 1
            elif n in starts: e = starts[n].reshape(dd,1)
            else: e = np.zeros((dd,1)); e[0] = 1
            v = np.kron(v, e)
        return v
    def to_front(psi):
        idx = [R.names.index(n) for n in names] + [R.names.index(n) for n in rest]
        return psi.reshape(R.dims).transpose(idx).reshape(-1,1)
    leaves = leaves_of(R, prog); lnames = [s[1] for s in lifts_of(prog)]
    rows = {}
    for key, assign in leaves.items():
        def col(vb, lassign):
            return to_front(run_assign(R, prog, start(vb, lassign), assign)[0])
        if is_loan:
            [target] = names
            # one column list per arrival of the target loan; the "other input"
            # axis is (every other loan's arrival, every visible basis input).
            cols = [[ col(vb, dict(list(zip(others, ob)) + [(target, lk)]))
                      for ob in oth_basis for vb in vis_basis ]
                    for lk in range(dl)]
            D = cols[0][0].shape[0] // d
            v, tr, B = loan_verdict(cols, d, D, dl, len(oth_basis) * len(vis_basis))
            cert = ('loan', B) if v == 'SAFE' else None
        else:
            flat = [ col(vb, dict(zip(all_loans, lb)))
                     for lb in (itertools.product(*[range(R.dims[R.names.index(n)])
                                                    for n in all_loans]) if all_loans else [()])
                     for vb in vis_basis ]
            K = np.hstack(flat); D = K.shape[0] // d
            v, tr = verdict(K, d, D)
            cert = ('temp', temp_certificate(K, d, D)) if v == 'SAFE' else None
        read = dict(key); label = ''.join((read[p][0] if p in read else '.') for p in lnames) or '-'
        rows[label] = (v, tr/(m*n_loan_basis), cert)
    return rows, d, m, len(prog)

def schedule(rows, ngates_touch):
    """(measure+reset per shot, uncompute gates per shot, this paper's per-shot cost, passes at compile time)."""
    reach = {k:v for k,v in rows.items() if v[0] != 'UNREACHABLE'}
    safe_all = all(v[0]=='SAFE' for v in reach.values())
    ours = 0 if safe_all else 1
    return 1, ngates_touch, ours, len(reach), safe_all

def drop_sites(stmts):
    """The drop targets the program names, in program order: the sites
    priced below, each a register name or (a tuple drop) a tuple of names.
    A drop of an input register (copy-input.s) is a site like any other;
    the criterion is asked one drop at a time."""
    return [s[1] for s in stmts if s[0] == 'drop']

def reclaiming_gate_column(regs, starts, names, rows):
    """One `name:gate` entry per record, same order as the verdict column,
    computed from each record's certificate -- never transcribed from the
    compiler's output. '-' (dash) records keep their key; unsafe/unreachable
    records read '—'."""
    entries = []
    for k, (v, w, cert) in rows.items():
        if cert is None:
            entries.append(f"{k}:—")
            continue
        kind, payload = cert
        if kind == 'temp':
            psi = alloc_psi(regs, starts, names)
            gate = name_gate(householder_reflection(psi, payload))
        else:
            B = payload
            t = (B.conj().T @ B)[0, 0].real
            Biso = B / np.sqrt(t) if t > 1e-12 else B
            gate = name_gate(Biso.conj().T)
        entries.append(f"{k}:{gate}")
    return ', '.join(entries)

def report(title, regs, vis, loans, starts, stmts, out):
    for t in drop_sites(stmts):
        names = as_names(t)
        rows, d, m, ng = drop_verdicts(regs, vis, loans, starts, stmts, t)
        touch = gates_touching(stmts, t)
        mr, unc, ours, passes, safe_all = schedule(rows, touch)
        verd = ', '.join(f"{k}:{v[0]}({v[1]:.3g})" for k,v in rows.items())
        gate_col = reclaiming_gate_column(regs, starts, names, rows)
        label = site_label(t)
        line = f"| {title} | {label} (d={d}) | m={m} | {verd} | {mr} meas+reset | {unc} gates | {ours} | {passes} pass(es), matrix {d*m*np.prod([dd for n,dd in regs if n not in vis and n not in names]):.0f}x{m} | {gate_col} |"
        out.append(line); print(line)

# ---- the generated families ---------------------------------------------------------
def barenco_mcx(m):
    """Lemma 7.2 of Barenco et al. 1995: an m-controlled X from 4(m-2) Toffolis with
    m-2 ancillas that need not be cleared and are returned to their initial values.
    Controls c1..cm and target t visible; ancillas a1..a_{m-2} temporaries, dropped at
    the end, started at |0> (the loan).  With A = T(c_m, a_{m-2}; t), B_1 = T(c1, c2; a1)
    and B_k = T(c_{k+1}, a_{k-1}; a_k), the network is
        A  B_{m-2} .. B_1  B_2 .. B_{m-2}  A  B_{m-2} .. B_1  B_2 .. B_{m-2}
    (Barenco's figure for n = 9, m = 5: twelve gates, the first seven set the target)."""
    regs = [(f'c{i}',2) for i in range(1,m+1)] + [('t',2)] + [(f'a{i}',2) for i in range(1,m-1)]
    vis = [f'c{i}' for i in range(1,m+1)] + ['t']
    T = lambda a,b,c: ('gate',[a,b,c],CCXg)
    A = T(f'c{m}', f'a{m-2}', 't')
    B = {1: T('c1','c2','a1')}
    for k in range(2, m-1): B[k] = T(f'c{k+1}', f'a{k-1}', f'a{k}')
    chain = [B[k] for k in range(m-2, 0, -1)] + [B[k] for k in range(2, m-1)]
    prog = [A] + chain + [A] + chain
    assert len(prog) == 4*(m-2)
    # The ancillas are Barenco's DIRTY ancillas: borrowed in a state the
    # network does not know and handed back in it.  They are loans, not
    # allocations, so no ('new', a) marker and no |0> seeding -- each is
    # varied over its own basis and its drop is decided by the block-factor
    # test, which is the claim Lemma 7.2 actually makes.
    anc = [a for a,_ in regs if a not in vis]
    stmts = prog + [('drop', a) for a in anc]
    return regs, vis, anc, {}, stmts, len(prog)

def check_barenco(m):
    """The network's action on the visible registers is the m-controlled X, and the
    ancillas return to |0..0>: K = |0..0> (x) mcx(m)."""
    regs, vis, loans, starts, stmts, ng = barenco_mcx(m)
    R = Regs(regs); prog = strip_markers(stmts)
    m_vis = 2**(m+1); cols = []
    for vb in itertools.product(range(2), repeat=m+1):
        psi = run_record(R, prog, R.basis(dict(zip(vis, vb))), [])
        cols.append(psi)
    K = np.hstack(cols)                      # rows ordered as R.names: visible first, then ancillas
    d_anc = 2**(m-2)
    K = K.reshape(m_vis, d_anc, m_vis)       # (visible level, ancilla level, column)
    W = K[:,0,:]; rest = K[:,1:,:]
    assert np.allclose(rest, 0) and np.allclose(W, mcx(m)), f"Barenco network wrong at m={m}"
    return True

def dj(n, balanced=True):
    """Deutsch-Jozsa on n input qubits with the parity oracle (balanced) or the constant oracle."""
    regs = [(f'x{i}',2) for i in range(n)] + [('t',2)]; vis = [f'x{i}' for i in range(n)]
    prog = [('gate',['t'],Xg), ('gate',['t'],Hg)] + [('gate',[f'x{i}'],Hg) for i in range(n)]
    if balanced: prog += [('gate',[f'x{i}','t'],CXg) for i in range(n)]
    prog += [('gate',[f'x{i}'],Hg) for i in range(n)]
    return regs, vis, {}, [('new','t')] + prog + [('drop','t')]

def grover(n):
    """One Grover iteration on n visible qubits with a marking ancilla: compute the mark
    (an n-controlled X into t), Z on t, uncompute."""
    regs = [(f'x{i}',2) for i in range(n)] + [('t',2)]; vis = [f'x{i}' for i in range(n)]
    xs = [f'x{i}' for i in range(n)]
    prog = [('gate',[x],Hg) for x in xs] + [('gate', xs+['t'], mcx(n)), ('gate',['t'],Zg), ('gate', xs+['t'], mcx(n))]
    return regs, vis, {}, [('new','t')] + prog + [('drop','t')]

def bennett(n):
    """Compute-copy-uncompute (Bennett 1973): scratch s := AND(x1..xn), copy s into the
    visible target y, uncompute s. Scratch dropped."""
    regs = [(f'x{i}',2) for i in range(n)] + [('y',2), ('s',2)]; vis = [f'x{i}' for i in range(n)] + ['y']
    xs = [f'x{i}' for i in range(n)]
    prog = [('gate', xs+['s'], mcx(n)), ('gate',['s','y'],CXg), ('gate', xs+['s'], mcx(n))]
    return regs, vis, {}, [('new','s')] + prog + [('drop','s')]

def measure_uncompute_family(n):
    """Kornerup-Sadun-Soloveichik's measure-then-fix-up uncomputation of AND(x1..xn) into a
    (temp-general.s generalised): CnX; H a; lift; if X; CnX; if Z; CnX; drop."""
    regs = [(f'x{i}',2) for i in range(n)] + [('a',2)]; vis = [f'x{i}' for i in range(n)]
    xs = [f'x{i}' for i in range(n)]
    prog = [('gate', xs+['a'], mcx(n)), ('gate',['a'],Hg), ('lift','b','a',[1]),
            ('if','b',[('gate',['a'],Xg)],[]), ('gate', xs+['a'], mcx(n)),
            ('if','b',[('gate',['a'],Zg)],[]), ('gate', xs+['a'], mcx(n))]
    return regs, vis, {}, [('new','a')] + prog + [('drop','a')]

def check_loan_test_is_not_the_ray_test():
    """The gate on 'loan_verdict': test/fixtures/cz-loan.s separates the two
    questions a drop can be asked.  CZ leaves every basis label of the loan
    fixed, so the fixed-ray test a temporary gets passes; no fixed B on the
    loan alone reproduces the joint action, so the block-factor test of
    the site definition's clause (4) fails, and the file's own header says UNSAFE.  A future
    edit that seeds a loan at |0> and asks the ray question turns this red."""
    path = '../haskell/test/fixtures/cz-loan.s'
    regs, vis, loans, starts, stmts = parse_s(open(path).read())
    rows, _, _, _ = drop_verdicts(regs, vis, loans, starts, stmts, 't')
    assert rows == {'-': rows['-']} and rows['-'][0] == 'UNSAFE', \
        f'cz-loan.s must be UNSAFE at drop t (the site definition's clause (4)), got {rows}'
    return True

if __name__ == '__main__':
    import glob, os
    assert check_loan_test_is_not_the_ray_test()
    out = ["| program | temporary | visible | verdict per record (weight) | measure+reset schedule | uncompute schedule (gates on t) | this paper, per shot | the verdict's price, once | reclaiming gate per record |",
           "|---|---|---|---|---|---|---|---|---|"]
    corpus_dir = '../haskell/programs'
    print("== the corpus ==")
    for f in sorted(glob.glob(os.path.join(corpus_dir, '*.s'))):
        name = os.path.basename(f)
        # A file that does not parse is a failure, not a missing row: the
        # table is a claim about the whole corpus.
        regs, vis, loans, starts, stmts = parse_s(open(f).read())
        if not drop_sites(stmts):
            out.append(f"| {name} | no drop site | | | | | | | |"); continue
        report(name, regs, vis, loans, starts, stmts, out)
    print("== generated families ==")
    for m in (3,4,5):
        assert check_barenco(m)
        regs, vis, loans, starts, stmts, ng = barenco_mcx(m)
        report(f"C^{m}X, Barenco Lem. 7.2 ({ng} Toffolis, {m-2} dirty ancilla{'s' if m>3 else ''})", regs, vis, loans, starts, stmts, out)
    for n in (1,2,3,4):
        regs, vis, starts, stmts = dj(n, True); report(f"Deutsch-Jozsa n={n}, parity oracle", regs, vis, [], starts, stmts, out)
    regs, vis, starts, stmts = dj(3, False); report("Deutsch-Jozsa n=3, constant oracle", regs, vis, [], starts, stmts, out)
    for n in (2,3,4):
        regs, vis, starts, stmts = grover(n); report(f"Grover mark n={n}", regs, vis, [], starts, stmts, out)
    for n in (2,3,4):
        regs, vis, starts, stmts = bennett(n); report(f"compute-copy-uncompute n={n}", regs, vis, [], starts, stmts, out)
    for n in (2,3):
        regs, vis, starts, stmts = measure_uncompute_family(n); report(f"measure-and-fix-up n={n}", regs, vis, [], starts, stmts, out)
    open('s_bench_table.md','w').write('\n'.join(out)+'\n')
    print("written s_bench_table.md")
