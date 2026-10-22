# denest.py —— 开方（去根号）判定与计算   依赖: pip install mpmath
# 用法:  r = denest(alpha, n, extras=[...])   alpha 用 add_root 建出的 Elem 表达
# 保证: 命中必真（beta**n == alpha 精确验证 + 分支数值匹配）；完备性取决于池/精度
from fractions import Fraction as Q
from itertools import product
import mpmath as mp

# ================= 0. 数论小工具 =================
def _factor(t):
    out, r = [], 2
    while r * r <= t:
        if t % r == 0:
            f = 0
            while t % r == 0: t //= r; f += 1
            out.append((r, f))
        r += 1
    if t > 1: out.append((t, 1))
    return out

def _peel(t, e):                       # t = p^e * s
    p = s = 1
    for pr, f in _factor(t):
        q, r = divmod(f, e); p *= pr ** q; s *= pr ** r
    return p, s

def _iroot(t, n):
    if t <= 0: return None if t < 0 else 0
    r = 1 << max(1, t.bit_length() // n + 1)
    while (r + 1) ** n <= t: r += 1
    while r ** n > t: r -= 1
    return r

def is_nth_power_in_Q(x, n):
    x = Q(x)
    if x == 0: return True
    if x < 0:
        if n % 2 == 0: return False
        x = -x
    for t in (x.numerator, x.denominator):
        if _iroot(t, n) ** n != t: return False
    return True

# ============ 1. 代数: Q[u_0..]/(u_i^{e_i} - base_i),  base_i 只含 u_<i ============
#    规范形 Σ c·∏u_i^{a_i} (0<=a_i<e_i)。base_i 是 Elem ⇒ 天然支持根号套根号。
_POOL = []      # [(base: Elem, e: int)]

def _pad(t, k): return tuple(t) + (0,) * (k - len(t))
def _strip(t):
    t = tuple(t)
    while t and t[-1] == 0: t = t[:-1]
    return t

def _norm(terms):
    k = len(_POOL)
    out = {}
    for m, c in terms.items():
        m = _pad(m, k); c = Q(c)
        if c: out[m] = out.get(m, Q(0)) + c
    for i in range(k - 1, -1, -1):                # 从最高生成元向下约
        e, base = _POOL[i][1], _POOL[i][0]
        nxt = {}
        for m, c in out.items():
            a = m[i]
            if a < e:
                nxt[m] = nxt.get(m, Q(0)) + c; continue
            q, r = divmod(a, e)                   # u_i^a = base^q * u_i^r
            mm = m[:i] + (r,) + m[i + 1:]
            for m2, c2 in (base ** q).t.items():
                key = tuple(x + y for x, y in zip(_pad(mm, k), _pad(m2, k)))
                nxt[key] = nxt.get(key, Q(0)) + c * c2
        out = {m: c for m, c in nxt.items() if c}
    return {_strip(m): c for m, c in out.items() if c}

class Elem:
    __slots__ = ("t",)
    def __init__(self, terms=None): self.t = _norm(terms or {})
    def __add__(s, o):
        d = dict(s.t)
        for m, c in as_elem(o).t.items(): d[m] = d.get(m, Q(0)) + c
        return Elem(d)
    __radd__ = __add__
    def __neg__(s): return Elem({m: -c for m, c in s.t.items()})
    def __sub__(s, o): return s + (-as_elem(o))
    def __rsub__(s, o): return as_elem(o) + (-s)
    def __mul__(s, o):
        d = {}; k = len(_POOL)
        for m1, c1 in s.t.items():
            for m2, c2 in as_elem(o).t.items():
                key = tuple(x + y for x, y in zip(_pad(m1, k), _pad(m2, k)))
                d[key] = d.get(key, Q(0)) + c1 * c2
        return Elem(d)
    __rmul__ = __mul__
    def __pow__(s, n):
        r, b = Elem({(): Q(1)}), s
        while n:
            if n & 1: r = r * b
            b = b * b; n >>= 1
        return r
    def __eq__(s, o): return isinstance(o, Elem) and s.t == o.t
    def val(s):
        z = mp.mpc(0)
        for m, c in s.t.items():
            p = mp.mpf(c.numerator) / c.denominator
            for i, a in enumerate(m):
                for _ in range(a): p *= _uval(i)
            z += p
        return z
    def __repr__(s): return fmt(s)

def as_elem(x): return x if isinstance(x, Elem) else Elem({(): Q(x)})

def add_root(base, e=2):
    """加入生成元 u_i = base^(1/e)（固定取主值），base 可含已有生成元 ⇒ 根号套根号"""
    _POOL.append((as_elem(base), int(e)))
    k = len(_POOL)
    return Elem({tuple(1 if j == k - 1 else 0 for j in range(k)): Q(1)})

def reset(): _POOL.clear()

def legend():
    return [f"u{i} = ({fmt(b)})^(1/{e})" for i, (b, e) in enumerate(_POOL)]

def fmt(x):
    if not x.t: return "0"
    parts = []
    for m, c in sorted(x.t.items()):
        ms = "*".join(f"u{i}^{a}" if a > 1 else f"u{i}" for i, a in enumerate(m) if a) or "1"
        cs = str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"
        parts.append(cs if ms == "1" else (f"{cs}*{ms}" if c != 1 else ms))
    return " + ".join(parts).replace("+ -", "- ")

# ================= 2. 数值求值（统一主分支约定） =================
def _zroot(z, e):
    z = mp.mpc(z)
    if abs(mp.im(z)) < mp.mpf(10) ** (-(mp.mp.dps - 5)):      # 实数：奇次取实根
        x = mp.re(z)
        if x >= 0 or e % 2 == 1:
            return mp.root(x, e) if x >= 0 else -mp.root(-x, e)
    return mp.e ** (mp.log(z) / e)                             # 主值 Arg∈(-π,π]

def _uval(i):
    b, e = _POOL[i][0], _POOL[i][1]
    return _zroot(b.val(), e)

# ================= 3. LLL 与有理重构求解 =================
def _lll(B, delta=Q(3, 4)):
    B = [list(map(int, r)) for r in B]; n = len(B)
    def dot(u, v): return sum(Q(a) * Q(b) for a, b in zip(u, v))
    def gso():
        Bs, mu = [], [[Q(0)] * n for _ in range(n)]
        for i in range(n):
            v = [Q(x) for x in B[i]]
            for j in range(i):
                d = dot(Bs[j], Bs[j])
                mu[i][j] = dot(B[i], Bs[j]) / d if d else Q(0)
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
        return Bs, mu
    Bs, mu = gso(); k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            if abs(mu[k][j]) > Q(1, 2):
                q = int(mu[k][j] + (Q(1, 2) if mu[k][j] > 0 else -Q(1, 2)))
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]
                mu[k] = [mu[k][t] - q * mu[j][t] for t in range(n)]
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]):
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu = gso(); k = max(k - 1, 1)
    return B

def _relations(vals, w, dps):
    """求 c∈Q^m 使 Σc_j·vals_j = w（w=None 时求 vals 的整关系）"""
    mp.mp.dps = dps
    vals = [mp.mpc(v) for v in vals]
    m = len(vals); C = 10 ** (dps // 2)
    rows = []
    for j, v in enumerate(vals):
        r = [0] * (m + 1) + [int(mp.nint(C * mp.re(v))), int(mp.nint(C * mp.im(v)))]
        r[j] = 10; rows.append(r)
    if w is not None:
        w = mp.mpc(w)
        r = [0] * (m + 1) + [int(mp.nint(C * mp.re(w))), int(mp.nint(C * mp.im(w)))]
        r[m] = 10; rows.append(r)
    basis = _lll(rows)
    def ok(vec):
        resid = abs(vec[-1]) + abs(vec[-2])
        return resid <= max(1, sum(abs(x) for x in vec[:-2]))
    cands = []
    for vec in basis:                                   # 单个基向量
        if ok(vec): cands.append(vec)
    for i in range(len(basis)):                         # 两两和差（关系格秩>1 时兜底）
        for j in range(i + 1, len(basis)):
            for s in (1, -1):
                vec = [a + s * b for a, b in zip(basis[i], basis[j])]
                if ok(vec): cands.append(vec)
    out = []
    for vec in cands:
        if w is None:
            if any(vec[j] for j in range(m)): out.append([Q(vec[j]) for j in range(m)])
        elif vec[m] != 0:
            out.append([Q(-vec[j], vec[m]) for j in range(m)])
    return out

def _basis_mons():
    es = [e for _, e in _POOL]
    return [a for a in product(*[range(e) for e in es])] if es else [()]

# ================= 4. 范数否证（"不可去"的证书） =================
def _mat_det(A):
    A = [[Q(x) for x in r] for r in A]; n = len(A); det = Q(1)
    for i in range(n):
        p = next((r for r in range(i, n) if A[r][i]), None)
        if p is None: return Q(0)
        if p != i: A[i], A[p] = A[p], A[i]; det = -det
        det *= A[i][i]
        for r in range(i + 1, n):
            if A[r][i]:
                f = A[r][i] / A[i][i]
                A[r] = [a - f * b for a, b in zip(A[r], A[i])]
    return det

def _norm_of(alpha):
    """N(α) = 乘法矩阵行列式 ∈ Q；α=β^n ⇒ N(α)=N(β)^n 必为 n 次幂

    注：_norm 会把常数项 (0,…,0) 规范化成 ()，所以这里的基也用 _strip 后的形式，
    否则查 idx 会 KeyError（原稿的小 bug）。
    """
    mons = [_strip(m) for m in _basis_mons()]
    idx = {m: j for j, m in enumerate(mons)}
    d = len(mons); A = [[Q(0)] * d for _ in range(d)]
    for j, m in enumerate(mons):
        for mm, c in (alpha * Elem({m: Q(1)})).t.items():
            A[idx[_strip(mm)]][j] = c
    return _mat_det(A)

def _obstruction(alpha, n, dps):
    """返回否证字符串或 None（未能判定）"""
    mons = _basis_mons()
    vals = [Elem({m: Q(1)}).val() for m in mons]
    if _relations(vals, None, dps):
        return None                        # 池内有隐藏关系，不出证书
    N = _norm_of(alpha)
    if is_nth_power_in_Q(N, n): return None
    return f"N(α) = {N} 不是 Q 中的 {n} 次幂 ⇒ {fmt(alpha)} 在当前池上不可开 {n} 次方"

# ================= 5. 主流程 =================
def denest(alpha, n, extras=(), dps_list=(40, 80, 160)):
    """判定并计算 α^(1/n) 能否去根号。
       extras: 扩池（形状B搜索），如 [(Q(2),2)] 放 √2 进来。
       返回 dict: ok, beta(Elem|None), expr(str), shape('A'|'B'), cert(str|None)。
       注: 调用会把 extras 固化进池；beta 依赖当前池的生成元编号。"""
    alpha = as_elem(alpha); n = int(n)
    for q, e in extras: add_root(q, e)
    shape = "A" if not extras else "B"
    if alpha.t == {}:
        return dict(ok=True, beta=Elem(), expr="0", shape=shape, cert=None)
    mons = _basis_mons(); mele = [Elem({m: Q(1)}) for m in mons]
    for dps in dps_list:
        mp.mp.dps = dps
        vals = [e.val() for e in mele]
        w = _zroot(alpha.val(), n)
        for cs in _relations(vals, w, dps):
            beta = sum((c * e for c, e in zip(cs, mele)), Elem())
            if beta ** n == alpha and abs(beta.val() - w) < mp.mpf(10) ** (-(dps // 3)):
                return dict(ok=True, beta=beta, expr=fmt(beta), shape=shape, cert=None)
    return dict(ok=False, beta=None, expr=None, shape=shape,
                cert=_obstruction(alpha, n, dps_list[-1]))
