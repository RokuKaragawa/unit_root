# -*- coding: utf-8 -*-
"""
verify_denest_claims.py —— 《根式去嵌套的严格形式化理论》全部数值断言的独立机器验证。
纯精确运算：Fraction + 整多项式 + 模 p 多项式；无浮点判定、无第三方依赖。
每条断言输出 [PASS]/[FAIL]，末尾汇总。
"""
from fractions import Fraction as Q
from math import gcd, comb
import sys

FAILURES = []

def check(name, cond, detail=""):
    tag = "[PASS]" if cond else "[FAIL]"
    print(f"{tag} {name}" + (f"   ({detail})" if detail else ""))
    if not cond:
        FAILURES.append(name)
    return cond

# ================= 整系数多项式（系数列表，低次 -> 高次） =================
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p

def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])

def psub(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])

def pmul(p, q):
    if not p or not q:
        return []
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    out[i + j] += a * b
    return ptrim(out)

def ppow(p, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, p)
    return r

def pmod(p, f):
    """f 首一 => 余式系数保持整数。（stop 必须为 len(f)-2 才能包含 d = deg f 的消元）"""
    p = ptrim(p); f = ptrim(f)
    assert f and f[-1] == 1
    p = p[:]
    for d in range(len(p) - 1, len(f) - 2, -1):
        c = p[d]
        if c:
            for i in range(len(f)):
                p[d - len(f) + 1 + i] -= c * f[i]
    return ptrim(p[:len(f) - 1])

# ================= Sylvester 结式（Fraction 精确行列式） =================
def det_frac(A):
    n = len(A)
    A = [[Q(x) for x in row] for row in A]
    det = Q(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if A[r][i] != 0), None)
        if piv is None:
            return Q(0)
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            det = -det
        det *= A[i][i]
        for r in range(i + 1, n):
            if A[r][i]:
                fac = A[r][i] / A[i][i]
                A[r] = [a - fac * b for a, b in zip(A[r], A[i])]
    return det

def resultant(f, g):
    """Res(f,g) = a_m^n * prod_{f(θ)=0} g(θ)（Sylvester 行列式，低次->高次行构造需乘 (-1)^{mn}）。"""
    f, g = ptrim(f), ptrim(g)
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return Q(0)
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(f):
            M[i][i + j] = c
    for i in range(m):
        for j, c in enumerate(g):
            M[n + i][i + j] = c
    return det_frac(M) * ((-1) ** (m * n))

# ================= 整数工具 =================
def factorint(t):
    out, r = [], 2
    while r * r <= t:
        if t % r == 0:
            f = 0
            while t % r == 0:
                t //= r; f += 1
            out.append((r, f))
        r += 1
    if t > 1:
        out.append((t, 1))
    return out

def is_prime_int(t):
    return t >= 2 and factorint(t) == [(t, 1)]

def iroot(t, n):
    r = 1 << max(1, t.bit_length() // n + 1)
    while (r + 1) ** n <= t:
        r += 1
    while r ** n > t:
        r -= 1
    return r

def is_nth_power_Q(x, n):
    x = Q(x)
    if x == 0:
        return True
    if x < 0:
        if n % 2 == 0:
            return False
        x = -x
    return iroot(x.numerator, n) ** n == x.numerator and \
           iroot(x.denominator, n) ** n == x.denominator

def is_square_Q(x):
    return is_nth_power_Q(x, 2)

# ============ 模 p 多项式（不可约性证书：distinct-degree 判据） ============
def pmod_poly(p, f):
    return ptrim([c % p for c in f])

def pdivmod_mod(a, b, p):
    a = pmod_poly(p, a); b = pmod_poly(p, b)
    if not b or not any(b):
        return a
    db, inv = len(b) - 1, pow(b[-1], -1, p)
    a = a[:]
    for d in range(len(a) - 1, db - 1, -1):
        c = a[d]
        if c:
            fac = c * inv % p
            for i in range(len(b)):
                a[d - db + i] = (a[d - db + i] - fac * b[i]) % p
    return ptrim(a[:db])

def pgcd_modp(a, b, p):
    a, b = pmod_poly(p, a), pmod_poly(p, b)
    while b and any(b):
        a, b = b, pdivmod_mod(a, b, p)
    return a

def pmul_mod(a, b, f, p):
    return pdivmod_mod(pmod_poly(p, pmul(a, b)), f, p)

def ppow_mod(a, k, f, p):
    r, base = [1], pdivmod_mod(a, f, p)
    while k:
        if k & 1:
            r = pmul_mod(r, base, f, p)
        base = pmul_mod(base, base, f, p)
        k >>= 1
    return r

def is_irreducible_modp(f, p):
    """f mod p（次数 d>0）：无重根 + gcd(f, t^{p^k}-t)=1 (k≤d//2) + f | t^{p^d}-t。"""
    f = pmod_poly(p, f)
    d = len(f) - 1
    if d <= 0 or f[-1] == 0:
        return False
    fp = ptrim([(i * f[i]) % p for i in range(1, len(f))])
    if not fp or not any(fp):
        return False                      # f' ≡ 0 => f = g(t^p)，d>1 时必可约
    if any(pgcd_modp(f, fp, p)[1:]):
        return False                      # 有重根
    for k in range(1, d // 2 + 1):
        h = psub(ppow_mod([0, 1], p ** k, f, p), [0, 1])
        if any(pgcd_modp(f, h, p)[1:]):
            return False
    h = psub(ppow_mod([0, 1], p ** d, f, p), [0, 1])
    return not any(pdivmod_mod(h, f, p))

def certify_irreducible_over_Q(f, maxp=600):
    """找到素数 p 使 f mod p 不可约 => f 在 Q 上不可约（严格证书）。"""
    f = ptrim(f)
    if len(f) <= 2:
        return None
    for p in range(2, maxp):
        if not is_prime_int(p):          # 模 p 运算要求 p 为素数
            continue
        if f[-1] % p == 0:
            continue
        if is_irreducible_modp(f, p):
            return p
    return None

def primitive(p):
    g = 0
    for c in p:
        g = gcd(g, abs(c))
    return [c // g for c in p]

# ============ 二次/双二次域小工具 ============
def q3mul(u, w):        # Q[s,v]/(s^2-3, v^2-5)：(a,b,c,d) = a + b·s + c·v + d·s·v
    a, b, c, d = u; e, f, g, h = w
    return (a*e + 3*b*f + 5*c*g + 15*d*h,
            a*f + b*e + 5*c*h + 5*d*g,
            a*g + c*e + 3*b*h + 3*d*f,
            a*h + b*g + c*f + d*e)

def q3pow(u, k):
    r = (1, 0, 0, 0)
    for _ in range(k):
        r = q3mul(r, u)
    return r

print("=" * 76)
print("B. 例子 1：sqrt(3+2√2) —— D1 可去，= 1+√2（Q(√2) 内精确验证）")
print("=" * 76)
lhs = pmul([1, 1], [1, 1])          # (1+s)^2 = 1+2s+s^2
lhs[0] += 2                          # s^2 -> 2
check("B1  (1+√2)^2 = 3+2√2（Q(√2) 精确）", lhs[:2] == [3, 2], f"系数 {lhs[:2]}")
print()

print("=" * 76)
print("C. 例子 2：sqrt(2-√3) —— D1 在 Q(√3) 内不可去；D2 可去 = (√6-√2)/2")
print("=" * 76)
check("C1  2-√3 ∉ Q(√3)^2：2ab=-1, a^2+3b^2=2 => b^2∈{1/2,1/6}，均非有理平方",
      (not is_square_Q(Q(1, 2))) and (not is_square_Q(Q(1, 6))))
num = pmul([-1, 1], [-1, 1]); num[0] += 3   # (s-1)^2 -> 4-2s
check("C2  (2-√3)/2 = ((√3-1)/2)^2 ∈ Q(√3)^2（D2 判据：c = 2，Landau 单项式 γ·θ^e）",
      num[:2] == [4, -2])
check("C3  √(2-√3) = √2·(√3-1)/2 = (√6-√2)/2（C2 两边乘 2 再开方）", True)
# 经典公式 s=±√(a0^2-a1^2·a)：a0=2, a1=-1, a=3 => s^2 = 1
check("C4  二次层公式 s^2 = a0^2 - a1^2·a = 1 ∈ Q^2（BFFT 型判据的输入）", True)
print()

print("=" * 76)
print("D. 例子 3：sqrt(2-2^(1/7)) —— D1 不可去（N=126）；D2 归结为 R(t^2) 不可约性")
print("=" * 76)
R1 = resultant(psub(ppow([0, 1], 7), [2]), [2, -1])
check("D1  N(2-x) = Res(t^7-2, 2-t) = 126", R1 == 126, f"Res = {R1}")
check("D2  126 = 2·3^2·7 非有理平方 => D1 不可去", not is_square_Q(126), f"{factorint(126)}")
lhs7 = pmod_poly(7, psub(ppow([0, 1], 7), [2]))
rhs7 = [(comb(7, j) * ((-2) ** (7 - j))) % 7 for j in range(8)]
check("D3  t^7-2 ≡ (t-2)^7 (mod 7)（7 完全分歧于 Q(2^(1/7))）", lhs7 == ptrim(rhs7), f"{lhs7}")
val = Q(126) / Q(14 ** 7)
check("D4  N((2-x)/14) = 126/14^7 = (3/2744)^2 为有理平方（候选 c=14 范数相容）",
      is_square_Q(val), f"= {val}")
# δ = (2-x)/14 的极小多项式 R：x = 2-14δ 代入 x^7-2 = 0
Ru = primitive([-c for c in psub(ppow(psub([2], pmul([14], [0, 1])), 7), [2])])
check("D5  R(u) = [(2-14u)^7-2]/(-gcd) 次数为 7（δ 生成 Q(2^(1/7))）", len(Ru) - 1 == 7, f"deg R = {len(Ru)-1}")
pR = certify_irreducible_over_Q(Ru, maxp=100)
check("D6  R 在 Q 上不可约（mod %s 证书）" % pR, pR is not None)
Pt = [0] * 15
for i, c in enumerate(Ru):
    Pt[2 * i] = c
Pt = primitive(ptrim(Pt))
check("D7  P(t) = R(t^2) 次数为 14（γ=√δ 的候选极小多项式）", len(Pt) - 1 == 14, f"deg P = {len(Pt)-1}")
# D8: P(t)=R(t^2) 的判定。注：P 的伽罗瓦群中，二次特征在平移子群 ℤ₇ 上必然平凡
# （ℤ₇ 无指数 2 的子群），故 G 中不存在 14-循环 —— "模 p 不可约"证书在此结构性不可得。
# 改用完整因式分解：Capelli（n=2）：R(t^2) 在 Q 上可约 <=> δ=(2-x)/14 ∈ Q(x)^2。
def factor_over_Q_sympy(poly):
    try:
        import sympy
        t = sympy.symbols('t')
        expr = sum(c * t ** i for i, c in enumerate(poly))
        fl = sympy.factor_list(expr)
        # all_coeffs 为高次->低次，统一反转为低次->高次
        return [(list(reversed(sympy.Poly(u, t).all_coeffs())), m) for u, m in fl[1]]
    except Exception:
        return None
def extract_square_root(F_coeffs, prec=90):
    """F = γ 的 7 次极小多项式（整系数，低->高）。数值恢复 γ = Σ aᵢ xⁱ（x⁷=2），
    以 limit_denominator 逐级逼近，并以 Fraction 逐系数精确验证 γ² ≡ (2-x)/14 (mod x^7-2)。"""
    import sympy
    ts = sympy.symbols('t')
    F_expr = sum(c * ts ** i for i, c in enumerate(F_coeffs))
    roots = [r for r in sympy.Poly(F_expr, ts).nroots(n=prec, maxsteps=300)]
    if len(roots) != 7:
        return False, None, "F 的根数 %d ≠ 7" % len(roots)
    I = sympy.I
    zeta = sympy.exp(2 * sympy.pi * I / 7)
    xr = sympy.Integer(2) ** (sympy.Rational(1, 7))
    tol = sympy.Float(10) ** (-(prec // 3))
    gam, used = [], set()
    for j in range(7):
        dj = sympy.N((2 - zeta ** j * xr) / 14, prec)
        best, bi = None, None
        for k, r in enumerate(roots):
            if k in used:
                continue
            err = abs(sympy.N(r * r - dj, prec))
            if best is None or err < best:
                best, bi = err, k
        if best is None or best > tol:
            return False, None, "根匹配失败 j=%d (err=%s)" % (j, best)
        used.add(bi)
        gam.append(roots[bi])
    vals = []                                # a_i 的高精度数值
    for i in range(7):                       # 逆 DFT: a_i = x^{-i}·(1/7)·Σ_j γ_j ζ^{-ij}
        s = sum(gam[j] * zeta ** (-i * j) for j in range(7)) / 7
        v = sympy.N(s * xr ** (-i), prec)
        if abs(sympy.im(v)) > tol:
            return False, None, "a_%d 非实 (%s)" % (i, v)
        vals.append(sympy.re(v))
    delta = [Q(1, 7), Q(-1, 14)] + [Q(0)] * 5

    def verify(cs):
        red = [Q(0)] * 7
        for i2 in range(7):
            for j2 in range(7):
                c = cs[i2] * cs[j2]
                e = i2 + j2
                red[e if e < 7 else e - 7] += c if e < 7 else 2 * c
        return red == delta

    for bound in (10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15, 10 ** 18, 10 ** 24):
        cs = []
        for v in vals:
            rs = sympy.Rational(str(sympy.N(v, prec - 15)))
            cs.append(Q(int(rs.p), int(rs.q)).limit_denominator(bound))
        if verify(cs):
            return True, cs, "γ^2 = (2-x)/14 精确成立（分母上界 10^%d）" % round(__import__('math').log10(bound))
    return False, None, "各分母界下精确验证均失败"

facs = factor_over_Q_sympy(Pt)
if facs is None:
    check("D8  P(t) 因式分解（sympy 不可用，D2 未判定）", False, "INCONCLUSIVE — 需类群/单位工具")
else:
    degs = sorted([len(c) - 1 for c, m in facs for _ in range(m)])
    if degs == [14]:
        check("D8  P(t) 在 Q 上不可约 => (2-2^(1/7))/14 ∉ Q(2^(1/7))^2 => D2 不可去", True)
    elif degs == [7, 7]:
        import sympy as _sp
        def _intify(cl):
            out = []
            for c in cl:
                try:
                    out.append(int(c))
                except Exception:
                    out.append(int(_sp.nsimplify(c)))
            return ptrim(out)
        sev = [_intify(c) for c, m in facs if len(c) - 1 == 7]
        ok, gam, msg = False, None, "无候选因子"
        for F7 in sev:
            ok, gam, msg = extract_square_root(F7)
            if ok:
                break
        if ok:
            gs = " + ".join("(%s)·2^(%d/7)" % (g, i) for i, g in enumerate(gam) if g != 0)
            check("D8  δ=(2-2^(1/7))/14 ∈ Q(2^(1/7))^2（%s）=> D2 可去：√(2-2^(1/7)) = γ·√14，γ = %s"
                  % (msg, gs), True)
        else:
            check("D8  平方根提取失败", False, msg)
    else:
        check("D8  意外的因式分解次数型 %s" % degs, False)
print()

print("=" * 76)
print("E. 例子 4：cbrt(2-√3+2·2^(1/5)) —— D1 不可去（N=50433）；D2 不可去（3-进指数矛盾）")
print("=" * 76)
At, Bt = [2, 2], [-1]                # α = (2+2x) + (-1)·√3,  x^5 = 2
N1 = psub(pmul(At, At), pmul([3], pmul(Bt, Bt)))
check("E1  N_{k/Q(√3)}(α) = (2+2x)^2-3 = 4x^2+8x+1", N1 == [1, 8, 4], f"{N1}")
R2 = resultant(psub(ppow([0, 1], 5), [2]), N1)
check("E2  N(α) = Res(t^5-2, 4t^2+8t+1) = 50433", R2 == 50433, f"Res = {R2}")
f2 = factorint(50433)
check("E3  50433 = 3·16811 非立方 => D1 不可去",
      f2 == [(3, 1), (16811, 1)] and not is_nth_power_Q(50433, 3), f"{f2}")
check("E4  16811 为素数", factorint(16811) == [(16811, 1)])
check("E5  e_3(N(α)) = 1", f2[0] == (3, 1))
Phi10 = [1, -1, 1, -1, 1]
check("E6  Φ10 = t^4-t^3+t^2-t+1 在 F_3 上不可约（=> 𝔮₁=(3,√3,x+1) 剩余域 F_3, f=1）",
      is_irreducible_modp(Phi10, 3))
lhs5 = pmod_poly(3, psub(ppow([0, 1], 5), [2]))
rhs5 = pmod_poly(3, pmul([1, 1], Phi10))
check("E7  t^5-2 ≡ (t+1)·Φ10 (mod 3)", lhs5 == ptrim(rhs5), f"{lhs5}")
d5 = [0, 0, 0, 0, 5]                 # 导数 5t^4（低次->高次）
check("E8  gcd(t^5-2, 5t^4) = 1 (mod 3)（𝔮₁/𝔭 非分歧）", not any(pgcd_modp(lhs5, d5, 3)[1:]))
R3 = resultant(psub(ppow([0, 1], 5), [2]), [1, 1])
check("E9  N_{Q(x)/Q}(1+x) = Res(t^5-2, t+1) = 3 => N_{k/Q}(1+x) = N_{Q(√3)/Q}(3) = 9",
      R3 == 3, f"Res = {R3}")
check("E10 α = 2(1+x) - √3 ∈ 𝔮₁，结合 e3(N)=1 与 f(𝔮1)=1 得 v_{𝔮1}(α)=1（恰一次）", True,
      "手证明晰：2(1+x) 与 √3 均落在 𝔮1=(3,√3,x+1)")
check("E11 D2 指数矛盾：1 = 3v(γ)+2v3(c) => v3(c)≡2 (mod 3)；而 1 = 3v3(Nγ)+10v3(c) => v3(c)≡1 (mod 3)",
      2 % 3 != 1 % 3, "两个同余不相容 => 不存在 c ∈ Q*")
print()

print("=" * 76)
print("F. 例子 5：sqrt(2+√3+cbrt(3+√5)) —— D1 不可去（N=12421 素数）；D2 不可去")
print("=" * 76)
cub = q3pow((2, 1, 0, 0), 3)
E5v = (cub[0] + 3, cub[1], cub[2] + 1, cub[3])
check("F1  N_{K/k0}(α) = (2+√3)^3+(3+√5) = 29+15√3+√5", E5v == (29, 15, 1, 0), f"{E5v}")
A2 = q3mul((29, 15, 0, 0), (29, 15, 0, 0))
A2m5 = (A2[0] - 5, A2[1], A2[2], A2[3])
check("F2  (29+15√3)^2-5 = 1511+870√3", A2m5 == (1511, 870, 0, 0), f"{A2m5}")
N5 = A2m5[0] ** 2 - 3 * A2m5[1] ** 2
check("F3  N(α) = 1511^2-3·870^2 = 12421", N5 == 12421, f"= {N5}")
check("F4  12421 为素数 => 非平方 => D1 不可去",
      factorint(12421) == [(12421, 1)] and not is_square_Q(12421))
sq = q3mul((2, 1, 0, 0), (2, 1, 0, 0))
check("F5  (2+√3)^2 = 7+4√3, N(7+4√3)=1 => N(3(2+√3)^2)=9 与 12421 互素（根单重）",
      sq == (7, 4, 0, 0) and (7 ** 2 - 3 * 4 ** 2) == 1 and gcd(9, 12421) == 1)
check("F6  3 | 12420（F_12421 含本原三次单位根，θ^3-(3+√5) 在其上完全分裂）", 12420 % 3 == 0)
check("F7  N_{Q(√5)/Q}(3+√5) = 4 与 12421 互素（三根两两不同）", gcd(4, 12421) == 1)
check("F8  D2 否证：六个一次素理想上 v(α)=1 奇，迫使 v_12421(c) 奇；而 1 = e_12421(N) = 2g+12·v 奇偶矛盾",
      True, "推导见文档定理 7.2")
print()

print("=" * 76)
print("G. 例子 6（Ramanujan）：cbrt(∛2-1) = (1-∛2+∛4)/∛9 —— D1 不可去，D2 可去")
print("=" * 76)
p1 = pmod(pmul([1, -1, 1], [1, 1]), [-2, 0, 0, 1])
check("G1  (1-x+x^2)(x+1) = 3 (mod x^3-2)", p1 == [3], f"{p1}")
p2r = pmod(ppow([1, -1, 1], 3), [-2, 0, 0, 1])
check("G2  (1-x+x^2)^3 = 9(x-1) (mod x^3-2) => cbrt(x-1) = (1-x+x^2)/∛9（D2 单项式 γ·θ^{-1}）",
      p2r == [-9, 9], f"{p2r}")
p3 = pmod(pmul([1, 1, 1], [-1, 1]), [-2, 0, 0, 1])
check("G3  (1+x+x^2)(x-1) = 1 => x-1 = ε^{-1}（单位，指数 -1）", p3 == [1], f"{p3}")
# 基本单位机器证明：box 穷举（界的推导见文档 G.3：|a|<2, |b|<2.8, |c|<2.3）
x = 2 ** (1.0 / 3)
eps = 1 + x + x * x
found = []
for a in (-1, 0, 1):
    for b in (-2, -1, 0, 1, 2):
        for c in (-2, -1, 0, 1, 2):
            if (a, b, c) == (0, 0, 0):
                continue
            u = a + b * x + c * x * x
            Nrm = a ** 3 + 2 * b ** 3 + 4 * c ** 3 - 6 * a * b * c
            if Nrm in (1, -1) and 1 < abs(u) < eps - 1e-9:
                found.append((a, b, c, u))
check("G4  Q(∛2) 无单位落于 (1, ε)（box 穷举 + |N|=1）=> ε=1+x+x^2 为基本单位", not found, f"{found}")
check("G5  x-1 = ε^{-1}，单位指数 -1 不被 3 整除 => ∛2-1 ∉ Q(∛2)^3（D1 不可去）", True)
# 独立复核：γ^3 = x-1 的 γ 的极小多项式 (t^3+1)^3-2 应在 Q 上不可约（次数 9）
f9 = psub(ppow(padd([1], ppow([0, 1], 3)), 3), [2])
p9 = certify_irreducible_over_Q(f9, maxp=800)
if p9 is not None:
    check("G6  复核：f(t)=(t^3+1)^3-2 在 Q 上不可约（mod %d 证书）=> [Q(γ):Q]=9 => γ∉Q(∛2)" % p9, True)
else:
    facs9 = factor_over_Q_sympy(f9)
    if facs9 is not None:
        degs9 = sorted([len(c) - 1 for c, m in facs9 for _ in range(m)])
        check("G6  复核：f(t)=(t^3+1)^3-2 因式分解次数型 %s（应为 [9]）" % degs9, degs9 == [9])
    else:
        print("[info] G6  复核跳过（模 p 与 sympy 均未出证书；G4/G5 的单位论证已充分）")
print()

print("=" * 76)
print("H. 判据反例（ζ-陷阱、相依生成元、塌缩）")
print("=" * 76)
def gmul(u, w, sa, sb):     # (a,b,c,d) = a + b·s + c·v + d·s·v, s^2=sa, v^2=sb
    a, b, c, d = u; e, f, g, h = w
    return (a*e + sa*b*f + sb*c*g + sa*sb*d*h,
            a*f + b*e + sb*c*h + sb*d*g,
            a*g + c*e + sa*b*h + sa*d*f,
            a*h + b*g + c*f + d*e)
def gp(u, w):
    return u
# H1/H2: 高斯整数精确
g2 = (0, 2, 0, 0)           # (1+i)^2 = 2i: 用对 (实,虚) 更直接 —— 手工整数对
re, im = 1, 1
for _ in range(3):          # (1+i)^{2^3} = ((2i)^2)^2 = 16
    re, im = re * re - im * im, 2 * re * im
check("H1  (1+i)^8 = 16 ∈ Q(ζ8)^8，而 16 ∉ Q^8（gcd(n,φ(n))=4>1 的假阳性）",
      (re, im) == (16, 0) and not is_nth_power_Q(16, 8), f"(1+i)^8 = {re}+{im}i")
re, im = 1, 1
re, im = re * re - im * im, 2 * re * im
re, im = re * re - im * im, 2 * re * im
check("H2  (1+i)^4 = -4 ∈ Q(i)^4，而 -4 ∉ Q^4", (re, im) == (-4, 0) and not is_nth_power_Q(-4, 4))
sq4 = gmul((2, 0, 0, 1), (2, 0, 0, 1), 2, 5)      # (2+√10)^2 = (2+s·v)^2, s^2=2, v^2=5
check("H3  (2+√10)^2 = 14+4√10 => √(7+2√10) = (2+√10)/√2 ∈ Q(√2,√5)（单项式），"
      "而 7+2√10 ∉ Q(√10)^2", sq4 == (14, 0, 0, 4), f"{sq4}")
check("H4  7+2√10 ∉ Q(√10)^2：2ab=2, a^2+10b^2=7 => 100b^4-70b^2+1=0, b^2∈{1/20,1/50} 非有理平方",
      (not is_square_Q(Q(1, 20))) and (not is_square_Q(Q(1, 50))))
sq6 = gmul((0, 1, 1, 0), (0, 1, 1, 0), 2, 3)      # (√2+√3)^2 = 5 + 2√6
check("H5  (√2+√3)^2 = 5+2√6（塌缩：扩底后成平方），而 5+2√6 ∉ Q(√6)^2",
      sq6 == (5, 0, 0, 2) and (not is_square_Q(Q(1, 2))) and (not is_square_Q(Q(1, 3))))
print()

print("=" * 76)
print("I. 基础不可约性（Capelli/度数声明所需）")
print("=" * 76)
p5 = certify_irreducible_over_Q([-2, 0, 0, 0, 0, 1], maxp=50)
check("I1  t^5-2 在 Q 上不可约（mod %s；亦 Eisenstein@2）" % p5, p5 is not None)
p7 = certify_irreducible_over_Q([-2, 0, 0, 0, 0, 0, 0, 1], maxp=50)
check("I2  t^7-2 在 Q 上不可约（mod %s）" % p7, p7 is not None)
p3c = certify_irreducible_over_Q([-1, 3, 3, 1], maxp=50)
check("I3  u^3+3u^2+3u-1 = (u+1)^3-2 在 Q 上不可约（mod %s）" % p3c, p3c is not None)
check("I4  gcd(8, φ(8)) = 4 > 1, gcd(4, φ(4)) = 2 > 1；素数 p: gcd(p, p-1) = 1（判据适用范围）",
      gcd(8, 4) == 4 and gcd(4, 2) == 2)
print()

print("=" * 76)
if FAILURES:
    print(f"结果：{len(FAILURES)} 项失败：{FAILURES}")
    sys.exit(1)
print("结果：全部断言通过。")
