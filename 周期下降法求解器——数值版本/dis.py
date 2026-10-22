# -*- coding: utf-8 -*-
r"""
周期下降法标准形计算器 v4（输出完全合并）
==========================================

输入奇素数 p（或任意 n ≥ 2），按《单位根的周期下降解法》：

  1. 标准素分解：把 h = (p-1)/2 分解成素因子序列 ℓ₁ℓ₂…ℓ_s（奇素数由大到小，
     最后排 2），写出子群链 H_0 ⊃ H_1 ⊃ … ⊃ H_s 与各层周期表、分解表；
  2. 周期下降 / 逐层开方：θ^{(j)}_{a,k} = Σ_t ω_ℓ^{-kt} β^{(a)}_t，
     (θ^{(j)}_{a,k})^ℓ = u^{(j)}_{a,k} = τ^k(u^{(j)}_{a,1}) ∈ Q(ω_ℓ)，
     再按反演公式一层层升回去，直到 Λ_a = 2cos(2πa/p)；
  3. 输出全部是具体根式（ω_ℓ 也展开成 Λ^{(ℓ)} 与 √(2-Λ^{(ℓ)}) 的显式形式），
     预解式的分支由因子 ω_ℓ^{s} 显式记录（s 由数值分支核对唯一确定）；
  4. 打印前做一次「完全合并」（tidy）：
       · 同类根式合并同类项：核 = 项里的根式因子与 i，同一个核前面的系数相加
         （系数本身是和式也照加，如 (8 - 4i√3)·∛X）；i·i 一律并成 -1；
         含嵌套——根号里、根号内的根号里同样合并；
       · 一个和式的所有系数先通分，把公分母提到分式线上（整系数形式/公分母），
         项内的分数（1/8(46+6i√3)∛X 这种）也折进外层分母，并约掉上下的整数公因子；
       · 整数系数乘进和式：6(2-i√3)∛X → (12-6i√3)∛X；
       · 根号内的有理因子一律提出并有理化：√[d]{N/q} = √[d]{N·q^{d-1}}/q，
         提出的有理因子与原系数完全相乘约简；
       · 非根式的有理部分做完整算术合并；
       · 合并前后用数值复算核对（必须一致），并检查合并是幂等的。
  5. 生成 .tex 后做一次输出审计：根号内不得有 \frac、不得有完全 d 次幂因子，
     分式的上下不得还有公因数（违反即报告所在行）；
  6. 生成 .tex 并调用 pdflatex 编译，扫描日志确认没有超界（Overfull）。

用法
    python dis.py                    # 交互输入
    python dis.py 11                 # 直接算 11
    python dis.py 13 --no-pdf        # 只生成 .tex
    python dis.py --selftest         # 2..30 数值自检 + 完全合并自检
    python dis.py 23 -o D:\输出       # 指定输出根目录
    python dis.py 29 --cap 400000    # 放宽展开规模上限
"""

import cmath
import math
import os
import re
import subprocess
import sys
import time
from fractions import Fraction

sys.setrecursionlimit(20000)

# ======================================================================
# 数论工具
# ======================================================================


def factorize(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primitive_root(p):
    fs = list(factorize(p - 1))
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError("找不到模 %d 的原根" % p)


def level_order(h):
    """h 的素因子序列 ℓ₁…ℓ_s：奇素数从大到小，最后排 2"""
    f = factorize(h)
    odd = []
    for q in sorted([q for q in f if q != 2], reverse=True):
        odd += [q] * f[q]
    return odd + [2] * f.get(2, 0)


def inv_mod(a, m):
    a %= m
    for x in range(1, m):
        if (a * x) % m == 1:
            return x
    raise ValueError("模 %d 不可逆" % m)


def lam_index(n, t):
    """2cos(2πt/n) 的下标 t̄ ∈ 1..(n-1)//2；t ≡ 0 时返回 0（代表数值 2）"""
    t %= n
    if t == 0:
        return 0
    return min(t, n - t)


# ---- 名字（一律带模数标签，杜绝不同模数之间的撞名）------------------

def kE(mod, j, a):
    return r"\eta^{(%d)}_{%d}@%d" % (j, a, mod)


def kU(mod, j, a, k):
    return r"u^{(%d)}_{%d,%d}@%d" % (j, a, k, mod)


def kT(mod, j, a, k):
    return r"\theta^{(%d)}_{%d,%d}@%d" % (j, a, k, mod)


def kLAM(mod, a):
    return r"\Lambda^{(%d)}_{%d}@%d" % (mod, a, mod)


def disp(key):
    """去掉内部标签，得到打印用的名字"""
    i = key.find("@")
    return key[:i] if i >= 0 else key


# ======================================================================
# Z[ζ_p]
# ======================================================================


class ZRing:
    """长度 p-1 的整系数表，第 i 项是 ζ^i（i=0..p-2）的系数；ζ^{p-1} 已折叠。"""

    def __init__(self, p):
        self.p = p
        self.n = p - 1

    def zero(self):
        return [0] * self.n

    def one(self):
        v = [0] * self.n
        v[0] = 1
        return v

    @staticmethod
    def is_zero(a):
        return not any(a)

    def add(self, a, b):
        return [x + y for x, y in zip(a, b)]

    def smul(self, k, a):
        return [k * x for x in a]

    def fold(self, raw):
        p, n = self.p, self.n
        out = [0] * n
        special = 0
        for e, c in enumerate(raw):
            if c:
                e2 = e % p
                if e2 == p - 1:
                    special += c
                else:
                    out[e2] += c
        if special:
            for i in range(n):
                out[i] -= special
        return out

    def mul(self, a, b):
        p = self.p
        raw = [0] * (2 * p)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        e = i + j
                        if e >= p:
                            e -= p
                        raw[e] += x * y
        return self.fold(raw)

    def sigma(self, a, k):
        raw = [0] * self.p
        for i, c in enumerate(a):
            if c:
                raw[(i * k) % self.p] += c
        return self.fold(raw)

    def period_vec(self, H, a):
        raw = [0] * self.p
        for b in H:
            raw[(a * b) % self.p] += 1
        return self.fold(raw)

    def period_coeffs(self, c, reps, H):
        """把被固定在该层域中的元素 c 写成 Σ_{a∈reps} d_a·η(aH)，并重建核对。"""
        c0 = c[0]
        d = {}
        for a in reps:
            d[a] = -c0 if a == 1 else c[a] - c0
        acc = self.zero()
        for a in reps:
            if d[a]:
                acc = self.add(acc, self.smul(d[a], self.period_vec(H, a)))
        if list(acc) != list(c):
            raise AssertionError("周期系数提取失败：元素不在该层域中？")
        return d


# ======================================================================
# Z[ζ_p][ω]/(Φ_ℓ(ω))
# ======================================================================


class OmegaRing:
    def __init__(self, Z, ell):
        self.Z = Z
        self.ell = ell
        self.d = ell - 1

    def zero(self):
        return [self.Z.zero() for _ in range(self.d)]

    def one(self):
        v = [self.Z.zero() for _ in range(self.d)]
        v[0] = self.Z.one()
        return v

    def reduce(self, cur):
        Z, d = self.Z, self.d
        cur = [list(x) for x in cur]
        need = 2 * d + 2
        if len(cur) < need:
            cur += [Z.zero() for _ in range(need - len(cur))]
        for e in range(len(cur) - 1, d - 1, -1):
            ce = cur[e]
            if Z.is_zero(ce):
                continue
            neg = Z.smul(-1, ce)
            for i in range(d):
                cur[e - d + i] = Z.add(cur[e - d + i], neg)
        return cur[:d]

    def omega_pow(self, k):
        k %= self.ell
        c = [self.Z.zero() for _ in range(self.ell)]
        c[k] = self.Z.one()
        return self.reduce(c)

    def add(self, a, b):
        return [self.Z.add(x, y) for x, y in zip(a, b)]

    def scale(self, a, z):
        return [self.Z.mul(x, z) for x in a]

    def mul(self, a, b):
        Z, d = self.Z, self.d
        cur = [Z.zero() for _ in range(2 * d - 1)]
        for i, x in enumerate(a):
            if Z.is_zero(x):
                continue
            for j, y in enumerate(b):
                if Z.is_zero(y):
                    continue
                cur[i + j] = Z.add(cur[i + j], Z.mul(x, y))
        return self.reduce(cur)

    def pow(self, a, k):
        r = self.one()
        b = [list(x) for x in a]
        while k:
            if k & 1:
                r = self.mul(r, b)
            k >>= 1
            if k:
                b = self.mul(b, b)
        return r


# ======================================================================
# 层结构
# ======================================================================


class Levels:
    def __init__(self, p, g=None):
        self.p = p
        self.h = (p - 1) // 2
        self.g = g if g else primitive_root(p)
        self.order = level_order(self.h)
        self.m = [1]
        for q in self.order:
            self.m.append(self.m[-1] * q)
        self.s = len(self.order)
        self.H = []
        for j in range(self.s + 1):
            mj = self.m[j]
            H = set()
            for t in range(self.h // mj):
                x = pow(self.g, mj * t, p)
                H.add(x)
                H.add(p - x)
            self.H.append(H)
        self.reps, self.coset = [], []
        for j in range(self.s + 1):
            seen, reps = set(), []
            for a in range(1, p):
                if a in seen:
                    continue
                reps.append(a)
                for b in self.H[j]:
                    seen.add((a * b) % p)
            self.reps.append(reps)
            arr = [0] * p
            for a in reversed(range(1, p)):
                for b in self.H[j]:
                    arr[(a * b) % p] = a
            self.coset.append(arr)
        self.parent = [None] * (self.s + 1)
        self.tindex = [None] * (self.s + 1)
        for j in range(1, self.s + 1):
            mp, ell = self.m[j - 1], self.order[j - 1]
            par, tidx = {}, {}
            for r in self.reps[j - 1]:
                for t in range(ell):
                    child = self.coset[j][(r * pow(self.g, mp * t, p)) % p]
                    par[child] = r
                    tidx[child] = t
            self.parent[j], self.tindex[j] = par, tidx

    def kids(self, j):
        """第 j 层的子周期（母周期 a = 1 的那一组），下标 t 与反演公式的 t 一致"""
        return [self.coset[j][pow(self.g, self.m[j - 1] * t, self.p)]
                for t in range(self.order[j - 1])]

    def d_of(self, a):
        for d in range(self.h):
            if pow(self.g, d, self.p) == a % self.p:
                return d
        raise ValueError("编号表越界")


# ======================================================================
# 下降（精确数据层）
# ======================================================================


class Descent:
    def __init__(self, p, g=None):
        if p == 2 or not is_prime(p):
            raise ValueError("Descent 只处理奇素数")
        self.p = p
        self.L = Levels(p, g)
        self.Z = ZRing(p)
        self.steps = []

    def period_vec(self, j, a):
        return self.Z.period_vec(self.L.H[j], a)

    def u_block(self, j, a):
        """u^{(j)}_{a,1}：基块的 u 经 σ_a 作用（a 跑第 j-1 层的陪集代表）"""
        Z, L = self.Z, self.L
        st = self.steps[j - 1]
        if a == 1:
            return st["u"], st["coef"]
        u = [Z.sigma(c, a) for c in st["u"]]
        coef = [Z.period_coeffs(c, L.reps[j - 1], L.H[j - 1]) for c in u]
        return u, coef

    def run(self, verbose=False):
        L, Z = self.L, self.Z
        for j in range(1, L.s + 1):
            ell = L.order[j - 1]
            R = OmegaRing(Z, ell)
            kids = L.kids(j)
            betas = [self.period_vec(j, a) for a in kids]
            theta = R.zero()
            for t, b in enumerate(betas):
                theta = R.add(theta, R.scale(R.omega_pow((-t) % ell), b))
            u = R.pow(theta, ell)
            gen = pow(L.g, L.m[j - 1], L.p)
            for c in u:
                if Z.sigma(c, gen) != c:
                    raise AssertionError("第 %d 步：u 的系数不在上一层域中" % j)
            coef = [Z.period_coeffs(c, L.reps[j - 1], L.H[j - 1]) for c in u]
            self.steps.append(dict(j=j, ell=ell, kids=kids, betas=betas,
                                   theta=theta, u=u, coef=coef))
            if verbose:
                print("    第 %d 步（ℓ=%d）完成" % (j, ell))
        return self

    def verify(self):
        """θ^ℓ=u、反演公式、Λ_a=2cos(2πa/p) 的数值核对（精确数据层）"""
        L, p = self.L, self.p
        z = cmath.exp(2j * cmath.pi / p)
        worst = 0.0
        for j in range(1, L.s + 1):
            ell = L.order[j - 1]
            w = cmath.exp(2j * cmath.pi / ell)
            st = self.steps[j - 1]
            V = [sum(z ** ((a * b) % p) for b in L.H[j]) for a in st["kids"]]
            th = [sum(w ** (-k * t) * V[t] for t in range(ell)) for k in range(ell)]
            base = [sum(z ** ((a * b) % p) for b in L.H[j - 1]) for a in L.reps[j - 1]]
            idx = {r: i for i, r in enumerate(L.reps[j - 1])}
            for k in range(ell):
                val = 0j
                for i, co in enumerate(st["coef"]):
                    val += sum(c * base[idx[r]] for r, c in co.items()) * w ** (i * k)
                if k == 0:
                    want = base[idx[1]]
                    worst = max(worst, abs(th[0] - want) / max(1.0, abs(want)))
                else:
                    worst = max(worst, abs(th[k] ** ell - val) / max(1.0, abs(val)))
            for t in range(ell):
                back = sum(w ** (t * k) * th[k] for k in range(ell)) / ell
                worst = max(worst, abs(back - V[t]) / max(1.0, abs(V[t])))
        for a in L.reps[-1]:
            got = sum(z ** ((a * b) % p) for b in L.H[-1])
            worst = max(worst, abs(got - 2 * cmath.cos(2 * cmath.pi * a / p)))
        return worst


# ======================================================================
# 表达式树
#   ('Q',Fraction) ('I',) ('OM',ℓ,k) ('R',d,base) ('P',(…)) ('S',(…)) ('N',名字)
# ======================================================================


def QF(fr):
    return ("Q", fr)


def Q(a, b=1):
    return ("Q", Fraction(a, b))


II = ("I",)


def OM(ell, k):
    """ω_ℓ^k（ℓ 为素数）"""
    k %= ell
    if ell == 2:
        return Q(-1) if k == 1 else Q(1)
    if k == 0:
        return Q(1)
    return ("OM", ell, k)


def NM(name):
    return ("N", name)


def SU(*ts):
    """和式（顺带把有理项合并，免得出现 √(2+1) 这种）"""
    flat, rat = [], Fraction(0)
    for t in ts:
        if t[0] == "S":
            for u in t[1]:
                if u[0] == "Q":
                    rat += u[1]
                else:
                    flat.append(u)
        elif t[0] == "Q":
            rat += t[1]
        else:
            flat.append(t)
    out = ([QF(rat)] if rat != 0 else []) + flat
    if not out:
        return Q(0)
    if len(out) == 1:
        return out[0]
    return ("S", tuple(out))


def PR(*fs):
    flat = []
    for f in fs:
        if f[0] == "P":
            flat += list(f[1])
        elif f[0] == "Q":
            if f[1] == 0:
                return Q(0)
            if f[1] == 1:
                continue
            flat.append(f)
        else:
            flat.append(f)
    if not flat:
        return Q(1)
    rat = Fraction(1)
    rest = []
    for f in flat:
        if f[0] == "Q":
            rat *= f[1]
        else:
            rest.append(f)
    # i 一律排在乘积最末（「基」的写法）：228√3 i 而不是 228i√3。
    # i 与任何因子交换都只差一个交换律，值不变
    if any(f[0] == "I" for f in rest):
        rest = [f for f in rest if f[0] != "I"] + [f for f in rest if f[0] == "I"]
    if rat == 0:
        return Q(0)
    if not rest:
        return Q(rat)
    if rat != 1:
        rest = [QF(rat)] + rest
    if len(rest) == 1:
        return rest[0]
    return ("P", tuple(rest))


def _pull_dth_power(num, den, d):
    """从 num/den 中提出 d 次方因子，返回 (提出的有理数, 剩下的有理数)"""
    out = Fraction(1)
    for _ in range(40):
        done = False
        rn = int(round(abs(num) ** (1.0 / d))) if num else 1
        for c in range(max(2, rn - 2), rn + 3):
            if num and num % (c ** d) == 0:
                num //= c ** d
                out *= c
                done = True
                break
        rd = int(round(den ** (1.0 / d))) if den else 1
        for c in range(max(2, rd - 2), rd + 3):
            if den and den % (c ** d) == 0:
                den //= c ** d
                out /= c
                done = True
                break
        if not done:
            break
    return out, Fraction(num, den)


def _term_rat_rest(t):
    """把一个项拆成（有理系数，其余部分 or None）"""
    if t[0] == "Q":
        return t[1], None
    if t[0] == "F":
        return Fraction(1, t[1]), t[2]
    if t[0] == "P":
        rat, rest = Fraction(1), []
        for f in t[1]:
            if f[0] == "Q":
                rat *= f[1]
            else:
                rest.append(f)
        return rat, (rest[0] if len(rest) == 1 else PR(*rest))
    return Fraction(1), t


def _rad_depth(e):
    """项里根式的嵌套层数：没根号 0、一层 √5 是 1、两层 √(5-2√5) 是 2……"""
    op = e[0]
    if op in ("Q", "I", "OM", "N"):
        return 0
    if op == "R":
        return 1 + _rad_depth(e[2])
    if op == "F":
        return _rad_depth(e[2])
    return max((_rad_depth(x) for x in e[1]), default=0)


def _sum_sort_key(t):
    """和式里各项的标准次序：先实部、后虚部（顶层的 i 才算虚部），
    各组内按根式层数（无根号 → 一层 → 两层 → 三层），同层按 LaTeX 文本字典序"""
    has_i, _ = _split_top_i(t)
    return (1 if has_i else 0, _rad_depth(t), tex(t))


def _kernel_key(t):
    """项的核（复杂根式之积）的可比较键；没有核（纯系数）返回 ()"""
    _, kern = _kernel_split(t)
    return () if kern is None else skey(kern)


def _split_top_i(t):
    """项的**顶层因子**里有没有 i；有就摘掉一个 i 返回剩下的部分

    只认顶层——i 在系数的和式里（(-1-i√3)∛X 这种）不算，那种由内层和式自己归拢。
    """
    if t[0] == "I":
        return True, Q(1)
    if t[0] == "P":
        fs = list(t[1])
        for k, f in enumerate(fs):
            if f[0] == "I":
                return True, PR(*(fs[:k] + fs[k + 1:]))
    return False, t


def _simple_radical(f):
    """被开方数是有理数的根式（√3、√17 这类「简单根式」）"""
    return f[0] == "R" and f[2][0] == "Q" and f[2][1] > 0


def _kernel_split(t):
    """把一个项拆成（系数, 核 or None）：核 := 顶层的**复杂根式**因子之积，
    其余（有理数、i、简单根式、和式）一律算系数。

    核只认复杂根式（∛(-260+156i√3)、√(17+4√17) 这种被开方数不是有理数的），
    于是 i、√3 这类简单根式会乘进系数、同一个复杂根式前的项并成一项：
      −54i√3·R₃ 与 (36+234i√3)·R₃ → (36+180i√3)·R₃；
      (−6−2i√3)·i√3·∛X → (6−6i√3)·∛X。
    分式 F(x, q) = x/q 先按 x 拆，再把 1/q 并进系数。
    """
    op = t[0]
    if op == "F":
        coef, kern = _kernel_split(t[2])
        r = QF(Fraction(1, t[1]))
        return (r if coef is None else PR(r, coef)), kern
    if op == "P":
        cs, ks = [], []
        for f in t[1]:
            (cs if (f[0] != "R" or _simple_radical(f)) else ks).append(f)
        if ks:                              # 核因子的次序规范化，免得两个同核项分家
            ks.sort(key=skey)
        return (PR(*cs) if cs else None), (PR(*ks) if ks else None)
    if op == "R":
        return (t, None) if _simple_radical(t) else (None, t)
    return t, None


def _monos_of(e, limit=32):
    """把一个表达式乘开成单项表（和式因子逐层相乘、i·i 并成 -1）；太大返回 None

    只用于系数合并：这样 2(-1-i√3) 与 -2-2i√3 这类「写法不同、数值相同」的
    项才能认成同类项并到一起。
    """
    if e[0] == "S":
        out = []
        for t in e[1]:
            m = _monos_of(t, limit)
            if m is None:
                return None
            out += m
            if len(out) > limit:
                return None
        return out
    if e[0] == "P":
        opts, n = [], 1
        for f in e[1]:
            o = _monos_of(f, limit)
            if o is None:
                return None
            n *= len(o)
            if n > limit:
                return None
            opts.append(o)
        out = [PR()]
        for o in opts:
            out = [PR(x, y) for x in out for y in o]
        return [_fold_i(m) for m in out]
    return [e]


def _fold_i(m):
    """把单项里的 i·i 并成 -1"""
    if m[0] != "P":
        return m
    k = sum(1 for f in m[1] if f[0] == "I")
    if k < 2:
        return m
    rest = [f for f in m[1] if f[0] != "I"]
    coef = -1 if (k // 2) % 2 else 1
    parts = ([QF(Fraction(coef))] if coef != 1 else []) + rest
    if k % 2:
        parts.append(II)
    return PR(*parts) if parts else Q(1)


def _sum_coefs(lst):
    """把同一个核的一批系数加起来

    · 全是有理数：直接化成最简分数；
    · 否则把每个系数乘开成单项，再按「有理系数 × 其余」归并同类项
      （2(-1-i√3) 与 -2-2i√3 并成 -4-4i√3；8i√3 与 -3i√3 并成 5i√3），最后拼回一个和式。
    系数全为 0 时（列表被清空）返回 0：整项要丢掉，不能当成 1。
    """
    lst = [c for c in lst if not (c[0] == "Q" and c[1] == 0)]
    if not lst:
        return Q(0)
    if len(lst) == 1:
        return lst[0]
    if all(c[0] == "Q" for c in lst):
        return QF(sum((c[1] for c in lst), Fraction(0)))
    groups, order = {}, []
    for c in lst:
        monos = _monos_of(c) if node_count(c) <= 24 else None
        for t in (monos if monos is not None else
                  (c[1] if c[0] == "S" else (c,))):
            rat, rest = _term_rat_rest(t)
            key = "" if rest is None else skey(rest)
            if key not in groups:
                groups[key] = [rest, Fraction(0)]
                order.append(key)
            groups[key][1] += rat
    out = []
    for key in order:
        rest, rat = groups[key]
        if rat == 0:
            continue
        if rest is None:
            out.append(QF(rat))
        else:
            out.append(rest if rat == 1 else PR(QF(rat), rest))
    return SU(*out)


def distribute(ex, depth=0):
    """只把有理系数乘进和式（不做完全展开），便于合并同类项"""
    if depth > 30:
        return ex
    op = ex[0]
    if op == "S":
        return SU(*[distribute(t, depth + 1) for t in ex[1]])
    if op == "P":
        fs = [distribute(f, depth + 1) for f in ex[1]]
        rat, others = Fraction(1), []
        for f in fs:
            if f[0] == "Q":
                rat *= f[1]
            else:
                others.append(f)
        if len(others) == 1 and others[0][0] == "S" and rat != 1:
            return SU(*[PR(QF(rat), t) for t in others[0][1]])
        return PR(QF(rat), *others) if others else QF(rat)
    if op == "R":
        return ROOT(ex[1], distribute(ex[2], depth + 1))
    if op == "F":
        return F(distribute(ex[2], depth + 1), ex[1])
    return ex


def _as_qsqrt(base):
    """把 base 识别成 A + B√m（A、B 为有理数，m 无平方因子）；失败返回 None"""
    terms = base[1] if base[0] == "S" else (base,)
    A, B, m, dens = Fraction(0), Fraction(0), None, set()
    for t in terms:
        rat, rest = _term_rat_rest(t)
        if rest is None:
            A += rat
            dens.add(rat.denominator)
            continue
        if rest[0] == "R" and rest[1] == 2 and rest[2][0] == "Q" and rest[2][1] > 0:
            mm = int(rest[2][1])
            for q in range(2, 100):
                while mm % (q * q) == 0:
                    mm //= q * q
            if m is None:
                m = mm
            elif m != mm:
                return None
            B += rat
            dens.add(rat.denominator)
            continue
        return None
    if m is None:
        return None
    C = 1
    for dd in dens:
        C = C * dd // math.gcd(C, dd)
    return A, B, m, C


def _perfect_power_part(N, d):
    """|N| 的完全 d 次幂因子的最大者（用于把根号里提得出来的因子提干净）"""
    m, n = 1, abs(int(N))
    q = 2
    while q ** d <= n:
        while n % (q ** d) == 0:
            n //= q ** d
            m *= q
        q += 1
    return m


def is_nth_power_in_Q(x, n):
    """有理数 x 是不是有理数的 n 次幂"""
    x = Fraction(x)
    if x == 0:
        return True
    if x < 0:
        if n % 2 == 0:
            return False
        x = -x
    for t in (x.numerator, x.denominator):
        r = int(round(t ** (1.0 / n)))
        while (r + 1) ** n <= t:
            r += 1
        while r ** n > t:
            r -= 1
        if r ** n != t:
            return False
    return True


def _lit_content(ex):
    """和式各项**字面**有理系数的 gcd（不乘开；除它一定除得尽）"""
    terms = ex[1] if ex[0] == "S" else (ex,)
    g = 0
    for t in terms:
        c, _ = _term_rat_rest(t)
        if c.denominator != 1:
            return 1
        g = math.gcd(g, abs(c.numerator))
        if g == 1:
            return 1
    return g or 1


def _int_content(ex):
    """和式被开方数的整系数 gcd（每项**先乘开**再取；还有分数没通分时返回 1）

    用来把和式被开方数里的公因子提到根号外面：
    √(2496 + 24A + 24B) 的 G = 24，提出 4 得 2√(624 + 6A + 6B)。
    先乘开是为了认得出 (2+2i√3)(3-i√3)R 这种「写法没展开」的项里的真实系数
    （12+4i√3，公因子 4；只看未展开的写法只能看到 6）。
    注意：乘开后的公因子不一定整除**字面**系数，这时不能直接拿它去除，
    要先用 _flatten_sum 把和式乘开（见 _tidy_node 的 R 支）。
    """
    terms = ex[1] if ex[0] == "S" else (ex,)
    g = 0
    for t in terms:
        # 门槛只是省时间的预判：_monos_of 自己按单项数封顶（超过就返回 None）。
        # 归拢 i 之后项会变大（(…)√(5-2√5)·i 这种），门槛太紧就看不出公因子
        monos = _monos_of(t) if node_count(t) <= 120 else None
        for m in (monos if monos is not None else (t,)):
            c, _ = _term_rat_rest(m)
            if c.denominator != 1:
                return 1
            g = math.gcd(g, abs(c.numerator))
            if g == 1:
                return 1
    return g or 1


def _flatten_sum(ex):
    """把和式各项乘开成一个平铺的和（项数太多、或乘开后出现分数就返回 None）

    平铺之后「字面系数」就是真实系数，公因子才除得尽。
    """
    if ex[0] != "S":
        return None
    terms = []
    for t in ex[1]:
        if node_count(t) > 24:
            return None
        monos = _monos_of(t)
        if monos is None:
            return None
        for m in monos:
            c, rf = _term_rat_rest(m)
            if c.denominator != 1:
                return None
            if rf is None:
                terms.append(QF(c))
            else:
                terms.append(PR(QF(c), rf) if c != 1 else rf)
        if len(terms) > 64:
            return None
    if not terms:
        return None
    return SU(*terms) if len(terms) > 1 else terms[0]


def _quad_form(base):
    """把被开方数认成 A + B√m（A、B 有理，m 为无平方因子的整数，**正负都行**）

    与 _as_qsqrt 的区别：允许 √(-q)（即 i√q）这种，供 d 次根提因子用。
    """
    terms = base[1] if base[0] == "S" else (base,)
    A, B, m, dens = Fraction(0), Fraction(0), None, set()
    for t in terms:
        rat, rest = _term_rat_rest(t)
        if rest is None:
            A += rat
            dens.add(rat.denominator)
            continue
        mm = None
        if rest[0] == "R" and rest[1] == 2 and rest[2][0] == "Q" and rest[2][1] > 0:
            mm = int(rest[2][1])                       # √q
        elif (rest[0] == "P" and len(rest[1]) == 2
              and sum(1 for f in rest[1] if f[0] == "I") == 1):
            rf = [f for f in rest[1] if f[0] != "I"][0]   # i 的位置不管（PR 里排最后）
            if rf[0] == "R" and rf[1] == 2 and rf[2][0] == "Q" and rf[2][1] > 0:
                mm = -int(rf[2][1])                    # i√q
        if mm is None:
            return None
        for q in range(2, 200):                        # 化成平方自由
            while mm % (q * q) == 0:
                mm //= q * q
        if m is None:
            m = mm
        elif m != mm:
            return None
        B += rat
        dens.add(rat.denominator)
    if m is None:
        return None
    C = 1
    for dd in dens:
        C = C * dd // math.gcd(C, dd)
    return A, B, m, C


_SURD_CACHE = {}


def _surd_pull(base, d=2):
    """把 √[d](a + b√m) 写成 S·√[d]{T}，S = u + v√m、T = a' + b'√m 都在 Z[√m] 里

    d = 2 时手稿 p = 17 的 √(34-2√17) = (5-√17)√(17+4√17) 就是这一步；
    d ≥ 3 时找的是 S^d | 被开方数（即「立方根里还能提出因子」）。
    命中条件：数值分支核对通过（S·T^(1/d) 与被开方数的 d 次主根一致）、
    剩下的系数和必须变小、且 |N(T)| ≤ 50|N(S)|。返回 (S 的树, T 的树) 或 None。
    """
    key = (d, skey(base))
    if key in _SURD_CACHE:
        return _SURD_CACHE[key]
    out = _surd_pull_work(base, d)
    if len(_SURD_CACHE) < 4000:
        _SURD_CACHE[key] = out
    return out


def _surd_pull_work(base, d):
    info = _quad_form(base)
    if info is None:
        return None
    A, B, m, C = info
    if C != 1 or B == 0 or m is None or m == 0:
        return None
    rr = math.isqrt(abs(m))
    if rr * rr == abs(m):
        return None
    a, b = int(A), int(B)
    try:
        zb = ev(base, {})
    except Exception:
        return None
    K = min(60, max(24, int(math.isqrt(abs(a) + abs(b))) + 2))
    best = None
    for u in range(-K, K + 1):
        for v in range(-K, K + 1):
            if u == 0 and v == 0:
                continue
            PP, QQ = Fraction(1), Fraction(0)          # (u+v√m)^d = PP + QQ√m
            for _ in range(d):
                PP, QQ = PP * u + QQ * v * m, PP * v + QQ * u
            PP, QQ = int(PP), int(QQ)
            N2 = PP * PP - QQ * QQ * m                 # = N(S)^d
            if N2 == 0:
                continue
            num1, num2 = a * PP - b * QQ * m, b * PP - a * QQ
            if num1 % N2 or num2 % N2:
                continue
            ap, bp = num1 // N2, num2 // N2
            if abs(ap) + abs(bp) >= abs(a) + abs(b):
                continue                               # 必须真的变小才算提因子
            NS, NT = u * u - v * v * m, ap * ap - bp * bp * m
            if NT == 0 or abs(NT) > 50 * abs(NS):
                continue                               # 提出的与剩下的要"量级相当"
            try:                                       # 数值分支核对
                zm = cmath.sqrt(complex(m))
                lv = zb ** (1.0 / d)
                got = (u + v * zm) * (ap + bp * zm) ** (1.0 / d)
                if abs(got - lv) > 1e-7 * max(1.0, abs(lv)):
                    continue
            except Exception:
                continue
            score = (abs(NS), u * u + v * v * abs(m))
            if best is None or score > best[0]:
                best = (score, u, v, ap, bp)
    if best is None:
        return None
    _, u, v, ap, bp = best
    rt = ROOT(2, Q(abs(m)))
    sgn = 0 if m > 0 else 1                            # m<0 时 √m = i√|m|
    def mk(x, y):
        if y == 0:
            return QF(Fraction(x))
        ry = PR(QF(Fraction(y)), rt)
        return SU(QF(Fraction(x)), PR(ry, II)) if sgn else SU(QF(Fraction(x)), ry)
    return mk(u, v), mk(ap, bp)


def ROOT(d, base):
    """d 次根，按"正实主支"化简并给出规范写法：

    · d = 2：√(-a) → √a·i；√((5-√5)/2) 之类改写成 √(10-2√5)/2（与手稿一致）；
    · d 为奇数、被开方数是负有理数：写成 -√[d]{|a|}（实数根，与打印式一致）；
    · 有理数因子按完全 d 次幂提出。
    """
    if d == 2 and base[0] == "Q" and base[1] < 0:
        return PR(ROOT(2, QF(-base[1])), II)
    if d == 2:
        info = _as_qsqrt(base)
        if info is not None:
            A, B, m, C = info
            if C > 1 and B != 0:
                inner = collect(distribute(PR(QF(Fraction(C * C)),
                                               SU(QF(A), PR(QF(B), ("R", 2, Q(m)))))))
                return PR(QF(Fraction(1, C)), ROOT(2, inner))
    if base[0] == "Q":
        fr = base[1]
        pull = Fraction(_perfect_power_part(fr.numerator, d),
                        _perfect_power_part(fr.denominator, d))
        rest = fr / (pull ** d)
        if rest == 0:
            return Q(0)
        if rest < 0 and d % 2 == 1:
            return PR(QF(-pull), ROOT(d, QF(-rest)))
        if rest < 0:
            return ("R", d, base)
        if rest == 1:
            return QF(pull)
        root_rest = int(round(abs(rest) ** (1.0 / d)))
        if root_rest ** d == rest:
            return QF(pull * root_rest)
        if pull != 1:
            return PR(QF(pull), ("R", d, QF(rest)))
        return ("R", d, base)
    if base[0] == "P":
        rat = Fraction(1)
        rest = []
        for f in base[1]:
            if f[0] == "Q":
                rat *= f[1]
            else:
                rest.append(f)
        if rat != 1:
            pull, inner = _pull_dth_power(rat.numerator, rat.denominator, d)
            if pull != 1:                      # 没提出因子就不要再递归（否则死循环）
                newbase = PR(QF(inner), *rest) if rest else QF(inner)
                return PR(QF(pull), ROOT(d, newbase))
        return ("R", d, base)
    return ("R", d, base)


# ======================================================================
# 完全合并：同类项、系数公分母、根号内的有理因子
#   新节点 ('F', q, rest) 表示 rest/q：q 为正整数，rest 为整系数表达式
# ======================================================================


def F(ex, q):
    """把 ex 写成 ex/q（q 为正整数）；能约的就地约掉"""
    q = int(q)
    if q < 0:
        return F(PR(Q(-1), ex) if ex[0] != "Q" else QF(-ex[1]), -q)
    if q == 1:
        return ex
    if ex[0] == "Q":
        return QF(ex[1] / q)
    if ex[0] == "F":
        return F(ex[2], ex[1] * q)
    return ("F", q, ex)


def rat_content(ex):
    """把 ex 拆成 (有理数 c, 剩余 rest)，使 ex = c·rest；rest 为 None 表示 ex 本身是有理数。
    rest 一律是「整系数」的表达式：和式取各系数的公分母，乘积取各有理因子之积。"""
    op = ex[0]
    if op == "Q":
        return ex[1], None
    if op == "F":
        c, rest = rat_content(ex[2])
        return c / ex[1], rest
    if op == "P":
        c, rest = Fraction(1), []
        for f in ex[1]:                     # 每个因子各自提有理内容，递归到底
            cf, rf = rat_content(f)
            c *= cf
            if rf is not None:
                rest.append(rf)
        if not rest:
            return c, None
        return c, (rest[0] if len(rest) == 1 else ("P", tuple(rest)))
    if op == "S":
        q = 1
        for t in ex[1]:
            ct, _ = _term_rat_rest(t)
            q = q * ct.denominator // math.gcd(q, ct.denominator)
        if q == 1:
            return Fraction(1), ex
        terms = []
        for t in ex[1]:
            ct, rest = _term_rat_rest(t)
            coef = ct * q
            terms.append(PR(QF(coef), rest) if rest is not None else QF(coef))
        return Fraction(1, q), SU(*terms)
    return Fraction(1), ex


def _div_exact(ex, G):
    """把 ex 整体除以整数 G；只要有一处除不尽就返回 None

    和式里的和式也跟着缩：除以 2 时 (46+6i√3)∛X → (23+3i√3)∛X，
    所以分式线上下能约掉的整数因子一定约得干净（不会只约掉一半）。
    """
    if G == 1:
        return ex
    op = ex[0]
    if op == "Q":
        c = ex[1]
        if c.denominator != 1 or c.numerator % G:
            return None
        return QF(c / G)
    if op == "F":
        inner = _div_exact(ex[2], G)
        return F(inner, ex[1]) if inner is not None else F(ex[2], ex[1] * G)
    if op == "P":
        fs = list(ex[1])
        for i, f in enumerate(fs):          # 找第一个除得尽的因子除（有理系数优先，它在前面）
            got = _div_exact(f, G)
            if got is not None:
                fs[i] = got
                return PR(*fs)
        return None
    if op == "S":
        out = []
        for t in ex[1]:
            got = _div_exact(t, G)
            if got is None:
                return None
            out.append(got)
        return SU(*out)
    return None


def _reduce_fr(fr):
    """分式 fr = num/q：把分子的整数公因子与分母的公因子约掉

    分子的公因子按**乘开后**的系数算（(46+6i√3)∛X 贡献 46 和 6），
    除的时候用 _div_exact——除不干净就整个不约，绝不留半约的状态。
    """
    if fr[0] != "F":
        return fr
    num, q = fr[2], fr[1]
    g = math.gcd(_int_content(num), q)
    if g > 1:
        red = _div_exact(num, g)
        if red is not None:
            return F(red, q // g)
    return fr


def _fracify(ex):
    """把顶层系数的公分母提到分式线上：整系数形式 / 公分母，顺带约分

    F 节点要再往里通一次，这样「\frac{1}{8}(46+6i√3)∛X + …」这种**项内**的分数
    会折进外层分母（38 + 1/8(46+6i√3)∛X + …）/3 → (304 + (46+6i√3)∛X + …)/24
    """
    if ex[0] in ("Q", "I", "OM", "N"):
        return ex
    if ex[0] == "F":
        return _reduce_fr(F(_fracify(ex[2]), ex[1]))
    c, rest = rat_content(ex)
    if rest is None or c.denominator == 1:
        return ex
    num = rest if c.numerator == 1 else PR(QF(c.numerator), rest)
    return _reduce_fr(F(num, c.denominator))


def _merge_radicals(rads):
    """同次根式相乘：√A·√B = √(AB)（两项都是有理数或被开方数不太大时才并）"""
    out = []
    by_d = {}
    for r in rads:
        d, base = r[1], r[2]
        if base[0] == "Q" and base[1] < 0:
            out.append(r)                       # 负被开方数另有主支约定，不动
            continue
        by_d.setdefault(d, []).append(base)
    for d, bases in by_d.items():
        if len(bases) == 1:
            out.append(("R", d, bases[0]))
            continue
        prod = PR(*bases)
        if node_count(prod) <= 40:
            out.append(ROOT(d, prod))
        else:
            out.extend(("R", d, b) for b in bases)
    return out


TIDY_MAX_DEPTH = 400                # _tidy_node 的递归深度保险丝（正常式子远到不了）


def _tidy_node(ex, depth=0):
    """结构规范化：递归子树 + 提出根号内的有理因子 + 同次根式相乘

    depth 只是保险丝：正常情况下几步就到底；万一「通分母」与「提因子」互相触发，
    超过 TIDY_MAX_DEPTH 就原样返回，避免递归爆栈（值仍然是对的，只是少化简一步）。
    """
    if depth > TIDY_MAX_DEPTH:
        return ex
    op = ex[0]
    if op in ("Q", "I", "OM", "N"):
        return ex
    if op == "F":
        return F(_tidy_node(ex[2], depth + 1), ex[1])
    if op == "S":
        ts = [_tidy_node(t, depth + 1) for t in ex[1]]
        # i 的归拢：同一和式里带顶层因子 i 的项提出 i 合成一项，
        # 660i + 220i√5 → (660 + 220√5)i；实部照旧排在前面。
        # 但**某个核既出现在带 i 的项里、又出现在不带 i 的项里时不能提**——
        # 提了会把 (414+54i√3)∛X 拆成 414∛X + i(54√3∛X)，同一个核的实部虚部被拆到两处
        keep, parts = [], []
        kr, ki = set(), set()
        for t in ts:
            has_i, rest_i = _split_top_i(t)
            if has_i:
                parts.append(rest_i)
                ki.add(_kernel_key(rest_i))
            else:
                keep.append(t)
                kr.add(_kernel_key(t))
        if len(parts) >= 2 and not (ki & kr):
            ts = keep + [PR(SU(*parts), II)]
        ts.sort(key=_sum_sort_key)          # 实部在前、虚部在后，各组按根式层数
        return SU(*ts)
    if op == "P":
        rat, rest, rads, is_ = Fraction(1), [], [], []
        for f in ex[1]:
            f = _tidy_node(f, depth + 1)
            if f[0] == "Q":
                rat *= f[1]
                continue
            if f[0] == "I":                 # i 单独数个数，成对的 i·i = -1 先算掉
                is_.append(f)
                continue
            c, rf = rat_content(f)          # 因子的有理内容也提到乘积外面
            rat *= c
            if rf is None:
                continue
            (rads if rf[0] == "R" else rest).append(rf)
        lone_i = []                        # 落单的 i 放到乘积**最末**（i 作「基」）：228√3 i
        if is_:                            # i 成对的并成 -1，落单的留一个
            rat *= (-1) ** (len(is_) // 2)
            if len(is_) % 2:
                lone_i = [II]
        sums = [f for f in rest if f[0] == "S"]
        # 整数系数先乘进和式：6(2-i√3)∛X → (12-6i√3)∛X，复杂根式留在外面当核。
        # 只乘整数——分数乘进去会被 _fracify 的通分母再提出来，两支来回振荡
        if sums and rat.denominator == 1 and rat != 1:
            # 只乘进**一个**和式因子：两个以上和式时每个都乘就成了乘 rat 的若干次方
            s0 = sums[0]
            rest = list(rest)
            rest[rest.index(s0)] = SU(*[PR(QF(rat), u) for u in s0[1]])
            sums, rat = [f for f in rest if f[0] == "S"], Fraction(1)
        # 简单根式（√3 这类）一律乘进和式系数，同一个复杂根式前的项才能并到一起：
        # (-6-2i√3)·√3·∛X → (-6√3+6i)·∛X；复杂根式留在系数外面。
        # 落单的 i **不**乘进和式——它由和式支归拢成「(…)i」，乘进去就又散成 ai+bi 了
        small = [r for r in rads if _simple_radical(r)]
        if sums and small:
            cnt = 1
            for s in sums:
                cnt *= len(s[1])
            if cnt <= 64:
                big = [r for r in rads if not _simple_radical(r)]
                others = [f for f in rest if f[0] != "S"] + big
                terms = [PR(*(others + small + lone_i))]
                lone_i = []                   # i 已经乘进每一项，末尾不要再加一次
                for s in sums:
                    terms = [PR(t, u) for t in terms for u in s[1]]
                rest, rads, sums = [SU(*terms)], [], []   # 复杂根式已经乘进每一项里了
        if len(sums) >= 2:                  # 两个以上和式因子且规模不大：展开相乘
            cnt = 1
            for s in sums:
                cnt *= len(s[1])
            if cnt <= 64:
                others = [f for f in rest if f[0] != "S"]
                terms = [PR(*(others + lone_i)) if (others or lone_i) else Q(1)]
                lone_i = []                   # 同上：i 已经在这个乘积里了
                for s in sums:
                    terms = [PR(t, u) for t in terms for u in s[1]]
                rest = [SU(*terms)]
        if rat == 0:
            return Q(0)
        return PR(QF(rat), *(rest + _merge_radicals(rads) + lone_i))
    if op == "R":
        d = ex[1]
        base = _tidy_node(ex[2], depth + 1)
        if d == 2 and base[0] == "Q" and base[1] < 0:
            return PR(ROOT(2, QF(-base[1])), II)
        c, rest = rat_content(base)
        if rest is None:
            if c.denominator == 1:
                return ROOT(d, QF(c))
            p, q = c.numerator, c.denominator
            # √[d]{p/q} = √[d]{p·q^{d-1}}/q
            return PR(QF(Fraction(1, q)),
                      _tidy_node(("R", d, QF(p * q ** (d - 1))), depth + 1))
        if c.denominator > 1:
            p, q = c.numerator, c.denominator
            # √[d]{c·rest} = √[d]{p·q^{d-1}·rest}/q；整数因子乘进和式，保持被开方数是整系数和
            inner = distribute(PR(QF(p * q ** (d - 1)), rest))
            return PR(QF(Fraction(1, q)),
                      _tidy_node(("R", d, inner), depth + 1))
        # 和式被开方数里的公因子：提出它的完全 d 次幂部分（√(2496+24A+24B) = 2√(624+6A+6B)）
        # 被开方数 = c·rest，公因子是 c·G，G 按**乘开后**的系数算（认得出 (2+2i√3)(3-i√3)
        # 的真实系数 12+4i√3 里的 4；(…)√(5-2√5)·i 这种项里的 168960）。
        # 除的时候用 _div_exact 逐层缩和式、形状不动；除不尽才退回字面 gcd、最后才摊平重乘——
        # 直接用摊平后的东西会拆掉刚归拢好的 i；直接拿 G 除字面系数则会除出分数，
        # 下一轮「通分母」又把公因子乘回去，两支来回振荡（n=19 爆栈的根因）
        G = _int_content(rest)
        rest1 = _div_exact(rest, G) if G != 1 else rest
        if rest1 is None:
            G2 = _lit_content(rest)
            rest1 = _div_exact(rest, G2) if G2 != 1 else rest
            if rest1 is not None:
                G = G2
            else:
                flat = _flatten_sum(rest)
                rest1 = (_div_exact(flat, G)
                         if flat is not None and _int_content(flat) == G else None)
        if rest1 is None:
            rest1, G = rest, 1
        M = c * G
        pull = Fraction(_perfect_power_part(M.numerator, d),
                        _perfect_power_part(M.denominator, d))
        if pull != 1:
            inner = distribute(PR(QF(M / (pull ** d)), rest1))
            return PR(QF(pull), _tidy_node(("R", d, inner), depth + 1))
        # d 次根提因子：√(34-2√17) = (5-√17)√(17+4√17)；d≥3 时是「根号里提出 S^d」
        # 提完**不再就地递归**：剩下的根式交给 tidy 的下一轮（否则会和「通分母」那支
        # 在同一个调用栈里互相触发，n=19 时爆栈）
        got = _surd_pull(base, d)
        if got is not None:
            return PR(got[0], ROOT(d, got[1]))
        return ROOT(d, base)
    return ex


TIDY_INFO = {"收敛": True}          # 上一轮 tidy 是否达到了不动点


def tidy(ex):
    """完全合并：合并同类项 → 把系数公分母提出 → 再规范化，迭代到不动点

    达到不动点时把 TIDY_INFO["收敛"] 置真：这时返回值本身已验证是不动点，
    自检里不必再白跑一遍幂等复检。
    """
    for _ in range(8):
        new = _fracify(collect(_tidy_node(ex)))
        if new == ex:
            TIDY_INFO["收敛"] = True
            return ex
        ex = new
    TIDY_INFO["收敛"] = False
    return ex


# ---- 合并自检（数值等价 + 幂等）------------------------------------

TIDY_STATS = {"总次数": 0, "数值不符": 0, "非幂等": 0, "最大相对偏差": 0.0,
              "已验不动点": 0, "跳过幂等": 0}

AUDIT_EXPRS = []          # 本次生成时打印过的表达式，供范数证书审计用

IDEMPOTENT_LIMIT = 30000     # 节点数超过它的式子只做一次合并，不再复跑幂等检查


def tidy_checked(ex):
    """先做合并、再核对「合并前后数值一致」与「合并幂等」，统计写进 TIDY_STATS

    幂等复检要把合并结果再合并一遍；迭代已到不动点的（绝大多数）直接算作验过，
    只有迭代满 8 轮仍未定下来的才复检；式子上万节点时这一遍很贵（n = 23 时约 30 s），
    所以超过 IDEMPOTENT_LIMIT 的只记「跳过幂等」，各项数目在自检里如实报出。
    """
    te = tidy(ex)
    TIDY_STATS["总次数"] += 1
    if TIDY_INFO["收敛"]:
        TIDY_STATS["已验不动点"] += 1      # tidy 内部已经确认过，不必再跑
    elif node_count(te) > IDEMPOTENT_LIMIT:
        TIDY_STATS["跳过幂等"] += 1
    elif tidy(te) != te:
        TIDY_STATS["非幂等"] += 1
    if count_names(ex) == 0 and count_names(te) == 0:
        try:
            v0, v1 = ev(ex, {}), ev(te, {})
            den = max(1.0, abs(v0))
            rel = abs(v0 - v1) / den
            TIDY_STATS["最大相对偏差"] = max(TIDY_STATS["最大相对偏差"], rel)
            if rel > 1e-12:
                TIDY_STATS["数值不符"] += 1
        except Exception:
            TIDY_STATS["数值不符"] += 1
    return te


def _top_terms_text(body):
    """按顶层的 +/- 把一段 LaTeX 切开（忽略花括号里的）"""
    out, depth, cur = [], 0, ""
    for ch in body:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if ch in "+-" and depth == 0 and cur:
            out.append(cur)
            cur = ch
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def _brace_body(src, j):
    """src[j] 必须是 '{'；返回 (花括号里的内容, 右花括号后一位)，配不上返回 (None, j)"""
    if j >= len(src) or src[j] != "{":
        return None, j
    depth, m = 0, j
    while m < len(src):
        if src[m] == "{":
            depth += 1
        elif src[m] == "}":
            depth -= 1
            if depth == 0:
                return src[j + 1:m], m + 1
        m += 1
    return None, j


def _lead_gcd(body):
    """一段 LaTeX 里各项**写出来的**整数系数的 gcd（没写出来的算 1）"""
    g = 0
    for term in _top_terms_text(body):
        mt = re.match(r"\s*(-?\d+)", term.lstrip("+"))
        g = math.gcd(g, abs(int(mt.group(1))) if mt else 1)
        if g == 1:
            break
    return g


def audit_tex(src):
    """扫描生成的 .tex，报三类没做干净的地方：

    · 根号内还留着 \\frac（有理化不彻底）；
    · 根号内的整数系数还带着能提出来的完全 d 次幂因子（开方开不干净）；
    · 分式的分子公因子与分母还有公因数（没约分）。
    """
    bad, i = [], 0
    while True:
        k = src.find(r"\sqrt", i)
        if k < 0:
            break
        j = k + 5
        d = 2
        if j < len(src) and src[j] == "[":
            m2 = src.find("]", j)
            try:
                d = int(src[j + 1:m2])
            except ValueError:
                d = 2
            j = m2 + 1
        if j < len(src) and src[j] == "{":
            depth, m = 0, j
            while m < len(src):
                if src[m] == "{":
                    depth += 1
                elif src[m] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                m += 1
            body = src[j + 1:m]
            line = src.count("\n", 0, k) + 1
            if r"\frac" in body:
                bad.append((line, body[:70]))
            else:
                g = _lead_gcd(body)
                if g > 1 and _perfect_power_part(g, d) > 1:
                    bad.append((line, "还有完全 %d 次幂因子：%s" % (d, body[:60])))
        i = k + 5
    # 分式没约分：分母是整数，分子各项系数的公因子还和它有公因数
    i = 0
    while True:
        k = src.find(r"\frac", i)
        if k < 0:
            break
        a, j = _brace_body(src, k + 5)
        b, _ = _brace_body(src, j)
        if a is not None and b is not None and re.fullmatch(r"\s*\d+\s*", b):
            q = int(b)
            g = math.gcd(_lead_gcd(a), q)
            if q > 1 and g > 1:
                bad.append((src.count("\n", 0, k) + 1,
                            "分式没约分（上下可约 %d）：%s" % (g, a[:50])))
        i = k + 5
    return bad


def norm_certificates(exs):
    """对每个「a + b√m」型的根号算一次范数 N = a² - b²m：

    N 不是有理数的 d 次幂 ⇒ 被开方数在 Q(√m) 里开不动 d 次方（这是"开不彻底"的否证证书）。
    返回 (证书条数, 例子列表)。
    """
    certs, samples = 0, []
    seen = set()
    for ex in exs:
        if ex is None:
            continue
        stack = [ex]
        while stack:
            e = stack.pop()
            op = e[0]
            if op in ("R", "F"):
                if op == "R":
                    info = _quad_form(e[2])
                    if info is not None:
                        A, B, m, C = info
                        if B != 0 and C == 1 and m is not None:
                            N = Fraction(A * A - B * B * m)
                            key = (e[1], N)
                            if key not in seen and not is_nth_power_in_Q(N, e[1]):
                                seen.add(key)
                                certs += 1
                                if len(samples) < 4:
                                    samples.append((e[1], A, B, m, N))
                stack.append(e[2])
                continue
            if op in ("Q", "I", "OM", "N"):
                continue
            stack.extend(e[1])
    return certs, samples


# ---- LaTeX 打印 ------------------------------------------------------


def tex_rat(fr):
    if fr.denominator == 1:
        return str(fr.numerator)
    if fr.numerator < 0:
        return r"-\frac{%d}{%d}" % (-fr.numerator, fr.denominator)
    return r"\frac{%d}{%d}" % (fr.numerator, fr.denominator)


def tex(e, prec=0):
    op = e[0]
    if op == "Q":
        return tex_rat(e[1])
    if op == "I":
        return "i"
    if op == "N":
        return disp(e[1])
    if op == "OM":
        return r"\omega_{%d}^{%d}" % (e[1], e[2])
    if op == "F":
        return r"\frac{%s}{%d}" % (tex(e[2], 1), e[1])
    if op == "R":
        d, base = e[1], e[2]
        return r"\sqrt{%s}" % tex(base) if d == 2 else \
            r"\sqrt[%d]{%s}" % (d, tex(base))
    if op == "P":
        out = []
        prev_digit = False
        for i, f in enumerate(e[1]):
            if i == 0 and f[0] == "Q" and f[1].denominator == 1 \
                    and abs(f[1].numerator) == 1:
                # ±1 只留符号：-\sqrt{3} 而不是 -1\sqrt{3}
                if f[1].numerator < 0:
                    out.append("-")
                prev_digit = False
                continue
            s = tex(f, 0)
            if f[0] == "S" and len(f[1]) > 1:
                s = r"\left(%s\right)" % s
            cur_digit = f[0] == "Q" and f[1].denominator == 1
            if i and prev_digit and cur_digit:
                out.append(r"\cdot")
            out.append(s)
            prev_digit = cur_digit
        s = "".join(out)
        return r"\left(%s\right)" % s if prec >= 3 else s
    if op == "S":
        parts = []
        for i, t in enumerate(e[1]):
            neg, body = split_sign(t)
            s = tex(body, 1)
            if i == 0:
                parts.append(("-" if neg else "") + s)
            else:
                parts.append((" - " if neg else " + ") + s)
        s = "".join(parts)
        return r"\left(%s\right)" % s if prec >= 2 else s
    raise ValueError("未知节点：%s" % (op,))


def split_sign(t):
    if t[0] == "Q":
        return (t[1] < 0), (QF(-t[1]) if t[1] < 0 else t)
    if t[0] == "F":
        return False, t
    if t[0] == "P":
        fs = list(t[1])
        for i, f in enumerate(fs):
            if f[0] == "Q":
                if f[1] < 0:
                    fs[i] = QF(-f[1])
                    return True, PR(*fs)
                return False, t
        return False, t
    return False, t


def skey(e):
    """结构键（比 tex 严格）：不同模数的同名量绝不会被并到一起"""
    op = e[0]
    if op == "Q":
        fr = e[1]
        return "Q%d/%d" % (fr.numerator, fr.denominator)
    if op == "I":
        return "I"
    if op in ("N", "OM"):
        return "%s:%s" % (op, "-".join(map(str, e[1:])))
    if op == "F":
        return "F%d:%s" % (e[1], skey(e[2]))
    if op == "R":
        return "R%d:%s" % (e[1], skey(e[2]))
    return "%s(%s)" % (op, "|".join(skey(x) for x in e[1]))


def collect(ex):
    """递归合并同类项：按「根式核」分组，同核的系数相加

    核 = 项里顶层 R 因子之积；系数 = 其余因子之积（可以是有理数、i、ω 的多项式等）。
    系数相加后若是和式，就照原样留成和式（如 (2/3 − (√3/3)i)·∛X），
    下一轮 _tidy_node 会把系数里的乘积展开、同类项再并一次。
    """
    ex = distribute(ex)
    op = ex[0]
    if op == "P":
        return PR(*[collect(f) for f in ex[1]])
    if op == "F":
        return F(collect(ex[2]), ex[1])
    if op == "R":
        return ROOT(ex[1], collect(ex[2]))
    if op != "S":
        return ex
    groups, order = {}, []
    for t in ex[1]:
        t = collect(t)
        coef, kern = _kernel_split(t)
        key = "" if kern is None else skey(kern)
        if key not in groups:
            groups[key] = [kern, []]
            order.append(key)
        groups[key][1].append(Q(1) if coef is None else coef)
    out = []
    for key in order:
        kern, coefs = groups[key]
        coef = _sum_coefs(coefs)
        if coef[0] == "Q" and coef[1] == 0:
            continue
        if kern is None:
            out.append(coef)
        elif coef[0] == "Q" and coef[1] == 1:
            out.append(kern)
        else:
            out.append(PR(coef, kern))
    return SU(*out)


def node_count(e):
    op = e[0]
    if op in ("Q", "I", "N", "OM"):
        return 1
    if op in ("R", "F"):
        return 1 + node_count(e[2])
    return 1 + sum(node_count(x) for x in e[1])


def count_names(e):
    """展开后仍残留的命名量个数（应为 0，表示是具体根式）"""
    op = e[0]
    if op == "N":
        return 1
    if op in ("Q", "I", "OM"):
        return 0
    if op in ("R", "F"):
        return count_names(e[2])
    return sum(count_names(x) for x in e[1])


def expand(ex, defs, limit=200000):
    """把命名量与 ω 节点全部换成显式根式；超过规模上限时保留名字。

    名字一律带模数标签，定义表因此无环；这里仍保留循环检测，
    一旦真的出现循环会给出可读报错，而不是 RecursionError。
    """
    cnt = [0]

    def rec(e, path):
        op = e[0]
        if op == "N":
            key = e[1]
            if key not in defs:
                return e
            if key in path:
                raise RuntimeError("展开时检测到循环引用：%s" % disp(key))
            if cnt[0] > limit:
                return e
            cnt[0] += 1
            return rec(defs[key], path + [key])
        if cnt[0] > limit:
            return e
        if op == "OM":
            ell, k = e[1], e[2]
            kbar = lam_index(ell, k)
            second = lam_index(ell, 2 * k)
            eps = 1 if (k % ell) <= ell // 2 else -1
            radic = Q(2) if second == 0 else \
                SU(Q(2), PR(Q(-1), NM(kLAM(ell, second))))
            body = SU(PR(QF(Fraction(1, 2)), NM(kLAM(ell, kbar))),
                      PR(QF(Fraction(eps, 2)), ROOT(2, radic), II))
            cnt[0] += 1
            return rec(body, path)
        if op == "R":
            inner = rec(e[2], path)
            cnt[0] += 1
            return ROOT(e[1], inner)
        if op == "P":
            return PR(*[rec(f, path) for f in e[1]])
        if op == "S":
            return SU(*[rec(t, path) for t in e[1]])
        if op == "F":
            return F(rec(e[2], path), e[1])
        return e

    return rec(ex, [])


def ev(ex, defs, _path=None):
    """数值求值（一律主支；与打印式同约定）"""
    op = ex[0]
    if op == "Q":
        return complex(float(ex[1]))
    if op == "I":
        return 1j
    if op == "OM":
        return cmath.exp(2j * cmath.pi * ex[2] / ex[1])
    if op == "N":
        key = ex[1]
        if key not in defs:
            raise KeyError("未定义的量：%s" % disp(key))
        if _path is None:
            _path = []
        if key in _path:
            raise RuntimeError("求值时检测到循环引用：%s" % disp(key))
        return ev(defs[key], defs, _path + [key])
    if op == "S":
        return sum(ev(t, defs, _path) for t in ex[1])
    if op == "P":
        r = 1 + 0j
        for f in ex[1]:
            r *= ev(f, defs, _path)
        return r
    if op == "R":
        return ev(ex[2], defs, _path) ** (1.0 / ex[1])
    if op == "F":
        return ev(ex[2], defs, _path) / ex[1]
    raise ValueError("未知节点：%s" % (op,))


# ======================================================================
# 装配
# ======================================================================


class Builder:
    _cache = {}

    def __new__(cls, n):
        if n in cls._cache:
            return cls._cache[n]
        obj = object.__new__(cls)
        cls._cache[n] = obj
        obj._init(n)
        return obj

    def _init(self, n):
        self.n = n
        self.defs = {}
        self.shift = {}            # (j,a,k) -> (s, 残差)
        self.branch_res = 0.0
        self.is_prime_n = is_prime(n) and n > 2
        if n == 2:
            self.des = self.L = self.p = None
            return
        if self.is_prime_n:
            self.p = n
            self.des = Descent(n).run()
            self.L = self.des.L
            self._define_prime()
        else:
            self.des = self.L = self.p = None
            self._define_composite()

    def define(self, key, ex):
        self.defs[key] = ex
        return NM(key)

    # ---- 素数：完整下降 ----
    def _define_prime(self):
        p, L = self.p, self.L
        self.define(kE(p, 0, 1), Q(-1))            # 第 0 层：全部非零剩余之和 = -1
        for ell in sorted(set(L.order)):           # 并入辅助素数的定义表
            if ell != 2:
                self.defs.update(Builder(ell).defs)
        for j in range(1, L.s + 1):
            ell = L.order[j - 1]
            for a in L.reps[j - 1]:
                u_, coef = self.des.u_block(j, a)
                for k in range(1, ell):
                    terms = []
                    for i, co in enumerate(coef):
                        if not co:
                            continue
                        cex = SU(*[PR(QF(Fraction(c)), NM(kE(p, j - 1, r)))
                                   for r, c in sorted(co.items())])
                        terms.append(PR(cex, OM(ell, (i * k) % ell)))
                    self.define(kU(p, j, a, k), collect(SU(*terms)))
                    self.define(kT(p, j, a, k), ROOT(ell, NM(kU(p, j, a, k))))
                for k in range(1, ell):            # 分支核对：θ = ω_ℓ^{s}·√[ℓ]{u}
                    self._set_branch(j, a, k)
            for b in L.reps[j]:
                par, t = L.parent[j][b], L.tindex[j][b]
                terms = [NM(kE(p, j - 1, par))]
                for k in range(1, ell):
                    terms.append(PR(OM(ell, (k * t) % ell), NM(kT(p, j, par, k))))
                self.define(kE(p, j, b),
                            PR(QF(Fraction(1, ell)), collect(SU(*terms))))
        for a in L.reps[-1]:
            self.define(kLAM(p, a), NM(kE(p, L.s, a)))

    def _theta_true(self, j, a, k):
        """θ^{(j)}_{a,k} = Σ_t ω_ℓ^{-kt} σ_a(η^{(j)}_{c_t}) 的真值（数值）"""
        L, p = self.L, self.p
        ell = L.order[j - 1]
        z = cmath.exp(2j * cmath.pi / p)
        w = cmath.exp(2j * cmath.pi / ell)
        Hj = sorted(L.H[j])
        acc = 0j
        for t, kid in enumerate(L.kids(j)):
            V = sum(z ** ((a * kid * b) % p) for b in Hj)
            acc += w ** ((-k * t) % ell) * V
        return acc

    def _set_branch(self, j, a, k):
        """把 θ^{(j)}_{a,k} = √[ℓ]{u} 校正到真值所在的分支：θ = ω_ℓ^{s}·√[ℓ]{u}。

        参考值取"与打印式完全同一约定"的展开结果，因此打印出来的式子
        按主支求值恰好等于真值。
        """
        if (j, a, k) in self.shift:
            return self.shift[(j, a, k)][0]
        L = self.L
        ell = L.order[j - 1]
        tk = kT(self.p, j, a, k)
        ex = collect(expand(NM(tk), self.defs, limit=400000))
        ref = ev(ex, self.defs)
        want = self._theta_true(j, a, k)
        if abs(ref) < 1e-300 or abs(want) < 1e-300:
            self.shift[(j, a, k)] = (0, 0.0)
            return 0
        w = cmath.exp(2j * cmath.pi / ell)
        ratio = want / ref
        s = int(round(cmath.phase(ratio) * ell / (2 * cmath.pi))) % ell
        res = abs(ratio / w ** s - 1)
        self.shift[(j, a, k)] = (s, res)
        self.branch_res = max(self.branch_res, res)
        if s:
            self.defs[tk] = PR(OM(ell, s), self.defs[tk])
        return s

    # ---- 合数：并入所有子问题（各素数幂）的定义 ----
    def _define_composite(self):
        n = self.n
        f = factorize(n)
        for q, e in sorted(f.items()):
            for k in range(1, e + 1):
                m = q ** k
                if m != n:
                    self.defs.update(Builder(m).defs)

    # ---- 全部单位根 ----
    def omega(self, t):
        n = self.n
        t %= n
        if t == 0:
            return Q(1)
        if n == 2:
            return Q(-1)
        if self.is_prime_n:
            p, L = self.p, self.L
            tb = lam_index(p, t)
            eps = 1 if t <= L.h else -1
            s2 = lam_index(p, 2 * tb)
            radic = Q(2) if s2 == 0 else \
                SU(Q(2), PR(Q(-1), NM(kLAM(p, s2))))
            return SU(PR(QF(Fraction(1, 2)), NM(kLAM(p, tb))),
                      PR(QF(Fraction(eps, 2)), ROOT(2, radic), II))
        f = factorize(n)
        qs = [q ** e for q, e in sorted(f.items())]
        if len(qs) == 1:                          # 素数幂 p^k
            p = sorted(f)[0]
            k = f[p]
            prev = qs[0] // p
            if prev == 1:
                return Builder(p).omega(t)
            if t % prev == 0:
                # t = m·p^(k-1)，此时 ω_n^t = ω_p^m（不是 ω_{p^(k-1)}^m）
                return Builder(p).omega((t // prev) % p)
            b = t % prev
            signed = b if b <= prev // 2 else b - prev
            m = (t - signed) // prev
            a = (m * p ** (k - 2)) % prev
            return PR(Builder(prev).omega(a), ROOT(p, Builder(prev).omega(b)))
        fs = []                                   # 互素因子：CRT 相乘
        for q in qs:
            s = (t * inv_mod((n // q) % q, q)) % q
            fs.append(Builder(q).omega(s))
        return PR(*fs)


# ======================================================================
# LaTeX
# ======================================================================


PREAMBLE = r"""\documentclass[UTF8]{ctexart}
\usepackage{geometry}
\usepackage{amsmath,amssymb,mathtools}
\usepackage{adjustbox}
\usepackage{fancyhdr}
\newcommand{\fitmath}[1]{\begin{center}\adjustbox{max width=\linewidth, max totalheight=0.42\textheight}{$\displaystyle #1$}\end{center}}
\geometry{a4paper,scale=0.78}
\setlength{\headheight}{16pt}
\setlength{\emergencystretch}{3em}
\allowdisplaybreaks
\pagestyle{fancy}
\fancyhead[L]{%(title)s}
\begin{document}
\rmfamily
\title{\textbf{\huge %(title)s}}
\date{}
\maketitle
"""


def width_estimate(s):
    w, i, n = 0.0, 0, len(s)
    while i < n:
        c = s[i]
        if c == "\\":
            j = i + 1
            while j < n and s[j].isalpha():
                j += 1
            cmd = s[i:j]
            w += 2.0 if cmd == r"\frac" else (1.2 if cmd == r"\sqrt" else 0.6)
            i = j
        elif c in "{}":
            i += 1
        elif c.isalpha():
            w += 1.0
            i += 1
        elif c.isdigit():
            w += 0.55
            i += 1
        else:
            w += 0.7
            i += 1
    return w


class TexDoc:
    """只做两件事：往行表里塞内容；对每一行做美元号配对自检。

    所有公式一律走 \fitmath（文本模式里的 adjustbox 自动缩放盒），
    所以数学表达式无论多宽多高都不会超界；散文行一律写得很短。
    """

    def __init__(self, budget=88.0):
        self.lines = []
        self.budget = budget
        self.warnings = []

    def add(self, s=""):
        if "$$" in s or s.count("$") % 2:
            self.warnings.append(s.strip()[:120])
            if "$$" in s:
                s = s.replace("$$", "$ $")
        self.lines.append(s)

    def text(self, s):
        self.add(s + "\n")

    def sec(self, t):
        self.add(r"\section*{%s}" % t)

    def sub(self, t):
        self.add(r"\subsection*{%s}" % t)

    def _emit_line(self, s):
        self.add(r"\fitmath{%s}" % s)
        self.add()


def wrap_pieces(doc, lhs, pieces, per_line=8):
    """把若干 LaTeX 片段按行宽与个数折成若干 \\fitmath 行，保证不超界。"""
    lhs = lhs.rstrip()
    head = lhs + (" " if lhs.endswith("=") else " = ")
    if not pieces:
        doc._emit_line(head + "0")
        return
    lines, cur, cnt = [], "", 0
    for i, pc in enumerate(pieces):
        piece = pc.lstrip("+") if i == 0 else pc
        cand = piece if not cur else cur + piece
        if cur and (cnt >= per_line or width_estimate(cand) > doc.budget):
            lines.append(cur)
            cur, cnt = piece, 1
        else:
            cur, cnt = cand, cnt + 1
    if cur:
        lines.append(cur)
    for i, ln in enumerate(lines):
        doc._emit_line((head if i == 0 else r"\quad ") + ln)


def term_pieces(ex):
    if ex[0] == "S":
        out = []
        for t in ex[1]:
            neg, body = split_sign(t)
            out.append(("-" if neg else "+") + tex(body))
        return out
    return [tex(ex)]


def display_terms(doc, lhs, ex, per_line=8):
    """打印前先做「完全合并」：同类项、系数公分母、根号内的有理因子"""
    if ex is not None:
        ex = tidy_checked(ex)
        AUDIT_EXPRS.append(ex)          # 留给「范数证书」审计用
    wrap_pieces(doc, lhs, term_pieces(ex), per_line=per_line)


def pieces_of_zetas(p, H, a):
    return [r"\zeta^{%d}" % e for e in sorted({(a * b) % p for b in H})]


# ======================================================================
# 文档生成
# ======================================================================


def aux_sections(doc, b, done):
    """写出用到的全部辅助素数（含递归）的显式结果"""
    if not b.is_prime_n:
        for q in sorted(factorize(b.n)):
            if q != 2:
                aux_sections(doc, Builder(q), done)
        return
    for ell in sorted(set(b.L.order)):
        if ell == 2 or ell in done:
            continue
        ab = Builder(ell)
        aux_sections(doc, ab, done)
        done.add(ell)
        doc.sub(r"辅助问题 $p = %d$（供 $\omega_{%d}^{k}$ 使用）" % (ell, ell))
        doc.text(r"$h = %d$，$g = %d$，层阶 $%s$。" %
                 (ab.L.h, ab.L.g,
                  (r"\times".join(str(q) for q in ab.L.order) if ab.L.order else "1")))
        for a in ab.L.reps[-1]:
            ex = collect(expand(NM(kLAM(ell, a)), ab.defs))
            display_terms(doc, r"\Lambda^{(%d)}_{%d} = " % (ell, a), ex)
        doc.text(r"$\omega_{%d}^{k} = \frac{1}{2}\Lambda^{(%d)}_{\bar k}"
                 r" + \frac{\varepsilon_k}{2}\sqrt{2-\Lambda^{(%d)}_{\overline{2k}}}\,i$。"
                 % (ell, ell, ell))


def make_document(n, brief=False, cap=200000):
    b = Builder(n)
    doc = TexDoc()
    doc.add(PREAMBLE % {"title": "%d 次单位根的根式解" % n})

    # ---------- 1 参数与标准素分解 ----------
    doc.sec("参数与标准素分解")
    if n == 2:
        doc.text(r"$\omega_{2}^{1} = -1$。")
    elif b.is_prime_n:
        p, L = b.p, b.L
        doc.text(r"$p = %d$，$h = (p-1)/2 = %d$，模 $%d$ 的最小原根 $g = %d$。" %
                 (p, L.h, p, L.g))
        doc.text(r"$h$ 的标准素分解：$h = %s$，子群链共 $%d$ 层。" %
                 ((r"\times".join(str(q) for q in L.order) if L.order else "1"), L.s))
        doc.text(r"$m_0 = 1$" + "".join(r"，$m_{%d} = %d$" % (i + 1, m)
                                        for i, m in enumerate(L.m[1:])) + "。")
        doc.text(r"各层子群 $H_j = \{\pm g^{m_j t}\}$，其中 $H_0$ 是全部 $%d$ 个非零剩余："
                 % (p - 1))
        for j in range(1, L.s + 1):
            doc._emit_line(r"H_{%d} = \{%s\}" %
                           (j, r",\,".join(map(str, sorted(L.H[j])))))
        doc.text(r"各层周期 $\eta^{(j)}_{a} = \sum_{b \in H_j}\zeta^{ab}$（$a$ 取陪集代表）。")
    else:
        f = factorize(n)
        doc.text(r"$n = %s$。" % r"\times".join(
            ("%d^{%d}" % (q, e)) if e > 1 else str(q) for q, e in sorted(f.items())))
        doc.text(r"合数按算术基本定理归约：素数幂用主支 $p$ 次根递推，")
        doc.text(r"互素因子用 CRT 相乘：")
        doc._emit_line(r"\omega_{n}^{t} = \prod_i \omega_{q_i}^{s_i},\qquad"
                       r" s_i \equiv t\,(n/q_i)^{-1} \pmod{q_i}")

    # ---------- 2 各层周期与分解表 ----------
    if b.is_prime_n:
        L = b.L
        p = b.p
        doc.sec("各层周期与分解表")
        for j in range(L.s + 1):
            doc.sub(r"第 $%d$ 层：%d 个周期" % (j, len(L.reps[j])))
            if j == 0:
                doc.text(r"$H_0$ 是全部 $%d$ 个非零剩余，故 $\eta^{(0)}_{1} = -1$。"
                         % (p - 1))
                continue
            for a in L.reps[j]:
                wrap_pieces(doc, r"\eta^{(%d)}_{%d} = " % (j, a),
                            [("+" if i else "") + t for i, t in
                             enumerate(pieces_of_zetas(p, L.H[j], a))],
                            per_line=8)
        doc.sub(r"分解表：每个母周期拆成 $\ell_j$ 个子周期")
        for j in range(1, L.s + 1):
            for r in L.reps[j - 1]:
                kids = [r"\eta^{(%d)}_{%d}" % (j, L.coset[j][
                    (r * pow(L.g, L.m[j - 1] * t, L.p)) % L.p])
                    for t in range(L.order[j - 1])]
                wrap_pieces(doc, r"\eta^{(%d)}_{%d} = " % (j - 1, r),
                            [("+" if i else "") + k for i, k in enumerate(kids)],
                            per_line=8)
            doc.text(r"（第 $%d$ 层，$\ell = %d$。）" % (j, L.order[j - 1]))

    # ---------- 3 辅助单位根 ----------
    doc.sec("辅助单位根")
    doc.text(r"$\ell = 2$ 时 $\omega_{2}^{1} = -1$。")
    doc.text(r"$\ell \geq 3$ 时按主支：")
    doc._emit_line(r"\omega_{\ell}^{k} = \frac{\Lambda^{(\ell)}_{\bar k}}{2}"
                   r" + \frac{\varepsilon_k}{2}\sqrt{2-\Lambda^{(\ell)}_{\overline{2k}}}\,i")
    doc.text(r"其中 $\varepsilon_k = \operatorname{sgn}\sin(2\pi k/\ell)$，"
             r"$\bar k = \min(k,\ell-k)$。")
    aux_sections(doc, b, set())

    # ---------- 4 逐层开方 ----------
    if b.is_prime_n:
        L, p = b.L, b.p
        doc.sec("逐层开方")
        doc.text(r"每一步把母周期 $\eta^{(j-1)}_{a}$ 分解成 $\ell$ 个子周期"
                 r" $\beta^{(a)}_{t}$。")
        doc.text(r"预解式取离散 Fourier 变换：")
        doc._emit_line(r"\theta^{(j)}_{a,k} = \sum_{t=0}^{\ell-1}"
                       r"\omega_{\ell}^{-kt}\beta^{(a)}_{t}")
        doc._emit_line(r"\left(\theta^{(j)}_{a,k}\right)^{\ell} = u^{(j)}_{a,k}"
                       r" = \tau^{k}\left(u^{(j)}_{a,1}\right)")
        doc._emit_line(r"\eta^{(j)}_{b(t)} = \frac{1}{\ell}\left(\eta^{(j-1)}_{a}"
                       r" + \sum_{k=1}^{\ell-1}\omega_{\ell}^{kt}"
                       r"\theta^{(j)}_{a,k}\right)")
        doc.text(r"（$\tau$ 把 $\omega_{\ell}$ 送到 $\omega_{\ell}^{k}$；$b(t)$ 为第 $t$ 个子周期。）")
        doc.text(r"开方一律取正实主支；预解式的分支由因子 $\omega_{\ell}^{s}$ 记录（见报告里的分支表）。")
        for j in range(1, L.s + 1):
            ell = L.order[j - 1]
            doc.sub(r"第 $%d$ 步（$\ell = %d$，%d 个母周期）"
                    % (j, ell, len(L.reps[j - 1])))
            for a in L.reps[j - 1]:
                if brief and a != 1:
                    continue
                if kU(p, j, a, 1) not in b.defs:
                    continue
                ex1 = collect(expand(NM(kU(p, j, a, 1)), b.defs, limit=cap))
                if count_names(ex1):
                    ex1 = collect(b.defs[kU(p, j, a, 1)])
                display_terms(doc, r"u^{(%d)}_{%d,1} = " % (j, a), ex1)
                exth = collect(expand(NM(kT(p, j, a, 1)), b.defs, limit=cap))
                if count_names(exth):
                    exth = collect(b.defs[kT(p, j, a, 1)])
                display_terms(doc, r"\theta^{(%d)}_{%d,1} = " % (j, a), exth)

    # ---------- 5 实部数值 ----------
    doc.sec("实部数值")
    if b.is_prime_n:
        for a in b.L.reps[-1]:
            ex = collect(expand(NM(kLAM(b.p, a)), b.defs, limit=cap))
            display_terms(doc, r"\Lambda_{%d} = 2\cos\frac{2\pi\cdot %d}{%d} = "
                               % (a, a, b.p), ex)
    elif n == 2:
        doc.text(r"$\Lambda_{1} = 2\cos\pi = -2$。")
    else:
        doc.text(r"合数情形的实部由各因子相乘得到，直接看下一节的写开结果。")

    # ---------- 6 全部单位根 ----------
    doc.sec("全部单位根")
    if b.is_prime_n:
        doc.text(r"最终形式：")
        doc._emit_line(r"\omega_{n}^{t} = \frac{\Lambda_{\bar t}}{2}"
                       r" + \frac{\varepsilon_t}{2}\sqrt{2-\Lambda_{\overline{2t}}}\,i,"
                       r"\qquad \Lambda_{\bar t} = 2\cos\frac{2\pi\bar t}{n}")
        doc.text(r"其中 $\bar t = \min(t, n-t)$，"
                 r"$\varepsilon_t = \operatorname{sgn}\sin(2\pi t/n)$。")
        doc.text(r"以下逐一写开（全部为具体根式）：")
    else:
        doc.text(r"以下逐一写开（合数情形已由 CRT 归约为因子次单位根之积）：")
    for t in range(1, n):
        ex = collect(expand(b.omega(t), b.defs, limit=cap))
        if count_names(ex):
            doc.warnings.append("n = %d 的 ω^%d 展开超出规模上限，保留了命名量" % (n, t))
        display_terms(doc, r"\omega_{%d}^{%d} = " % (n, t), ex)

    doc.add(r"\end{document}")
    return "\n".join(doc.lines), doc.warnings


# ======================================================================
# 编译与检查
# ======================================================================


def compile_pdf(tex_path, workdir, passes=2):
    """编译若干遍；返回 (是否成功, 日志, 出错处 .tex 原文, Overfull 计数)"""
    logs = []
    for _ in range(max(1, passes)):
        try:
            p = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                                "-halt-on-error", os.path.basename(tex_path)],
                               cwd=workdir, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=7200)
            logs.append(p.stdout.decode("utf-8", "replace"))
        except FileNotFoundError:
            return False, "找不到 pdflatex：请安装 MiKTeX/TeX Live 并把 bin 加入 PATH。", [], 0
        except Exception as e:
            return False, "pdflatex 调用失败：%r\n%s" % (e, "\n".join(logs)), [], 0
    last = logs[-1]
    ok = ("! " not in last) and ("Output written" in last)
    n_over = len(re.findall(r"Overfull \\[hv]box", last))
    hints = []
    try:
        with open(tex_path, encoding="utf-8") as f:
            src = f.read().splitlines()
    except Exception:
        src = []
    for m in re.finditer(r"^l\.(\d+)", last, re.M):
        ln = int(m.group(1))
        for k in range(max(1, ln - 2), min(len(src), ln + 2) + 1):
            hints.append("%4d: %s" % (k, src[k - 1]))
        hints.append("")
    return ok, "\n".join(logs), hints, n_over


# ======================================================================
# 自检
# ======================================================================


def branch_res_of(b):
    if b.n == 2:
        return 0.0
    if b.is_prime_n:
        return b.branch_res
    subs = [branch_res_of(Builder(q))
            for q in sorted(set(factorize(b.n))) if q > 2]
    if not subs:            # n = 2^k（k ≥ 2）：每层都是 L_r = 2，共轭分支已被迫取定，残差为 0
        return 0.0
    return max(subs)


def check_n(n, verbose=True, cap=200000, merge_ts=None):
    """逐 t 核值；merge_ts 给出要做「完全合并」核对的 t（None 表示全部）

    n 大时展开式可达几万节点，每个 t 的合并要一两分钟，故自检对 n > 20 只抽查 t = 1。
    """
    b = Builder(n)
    if merge_ts is None:
        merge_ts = set(range(n))
    worst, left = 0.0, 0
    for t in range(n):
        ex = collect(expand(b.omega(t), b.defs, limit=cap))
        left = max(left, count_names(ex))
        worst = max(worst, abs(ev(ex, b.defs) - cmath.exp(2j * cmath.pi * t / n)))
        if t in merge_ts:
            te = tidy_checked(ex)           # 完全合并后再核一遍值
            worst = max(worst, abs(ev(te, b.defs) - cmath.exp(2j * cmath.pi * t / n)))
    if b.des is not None:
        worst = max(worst, b.des.verify())
    bres = branch_res_of(b)
    if verbose:
        print("  n = %-3d 最大偏差 %.3e  分支残差 %.1e  残留命名量 %d"
              % (n, worst, bres, left))
    return worst, left, bres


def selftest():
    print("== 2..30 次单位根自检（与《单位根的排序》的覆盖范围一致）==")
    bad = []
    for n in range(2, 31):
        try:
            # n > 20 的展开式动辄几万节点，每个 t 的合并要一两分钟，故只抽查 t = 1
            mts = set(range(n)) if n <= 20 else {1}
            w, left, bres = check_n(n, merge_ts=mts)
            if w > 1e-8 or left:
                bad.append(n)
        except Exception as e:
            print("  n = %-3d 失败：%r" % (n, e))
            bad.append(n)
    st = TIDY_STATS
    print("  完全合并自检：共 %d 个公式；数值不符 %d 处；非幂等 %d 处；最大相对偏差 %.1e"
          % (st["总次数"], st["数值不符"], st["非幂等"], st["最大相对偏差"]))
    print("  （%d 处迭代到不动点即算验过；%d 处复检；节点数 > %d 的跳过复检 %d 处）"
          % (st["已验不动点"], st["总次数"] - st["已验不动点"] - st["跳过幂等"],
             IDEMPOTENT_LIMIT, st["跳过幂等"]))
    print("  （n ≤ 20 逐 t 全查；n > 20 只查 t = 1）")
    if st["数值不符"] or st["非幂等"]:
        bad.append("tidy")
    print("未通过：%s" % (bad if bad else "无"))
    return bad


# ======================================================================
# 主程序
# ======================================================================


def run_one(n, outroot=None, pdf=True, brief=False, cap=200000):
    outroot = outroot or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                      "运行结果")
    workdir = os.path.join(outroot, "%s_n%d" % (time.strftime("%Y%m%d-%H%M%S"), n))
    os.makedirs(workdir, exist_ok=True)
    print("== 计算 n = %d 的全部单位根 ==" % n)
    t0 = time.time()
    del AUDIT_EXPRS[:]
    texsrc, warns = make_document(n, brief=brief, cap=cap)
    tex_path = os.path.join(workdir, "单位根_n%d.tex" % n)
    with open(tex_path, "w", encoding="utf-8") as f:
        f.write(texsrc)
    print("  已写出 %s（%.1f KB，%.2f s）" %
          (tex_path, len(texsrc.encode("utf-8")) / 1024.0, time.time() - t0))

    rep = []
    if warns:
        rep.append("排版/规模提示 %d 处：" % len(warns))
        rep += ["  " + w for w in warns]
        print("  [提示] %d 处，详见 报告.txt" % len(warns))

    worst, left, bres = check_n(n, cap=cap)
    rep.append("表达式求值 vs exp(2πit/n) 的最大偏差：%.3e" % worst)
    rep.append("预解式分支核对的最大残差：%.3e" % bres)
    rep.append("展开后残留的命名量（应为 0）：%d" % left)

    b = Builder(n)
    if b.is_prime_n and b.shift:
        rep.append("分支表 θ^{(j)}_{a,k} = ω_ℓ^{s}·√[ℓ]{u}：")
        rep.append("  " + "，".join("(j=%d,a=%d,k=%d):s=%d"
                                    % (kk[0], kk[1], kk[2], vv[0])
                                    for kk, vv in sorted(b.shift.items())))

    st = TIDY_STATS
    rep.append("完全合并自检：共 %d 个公式；合并前后数值不一致 %d 处；非幂等 %d 处；"
               "最大相对偏差 %.1e（%d 处迭代到不动点、%d 处复检、%d 处因过大跳过复检）"
               % (st["总次数"], st["数值不符"], st["非幂等"], st["最大相对偏差"],
                  st["已验不动点"],
                  st["总次数"] - st["已验不动点"] - st["跳过幂等"], st["跳过幂等"]))
    bad = audit_tex(texsrc)
    rep.append("输出审计（根号内不得有 \\frac、不得有完全 d 次幂因子；分式必须约分）："
               "未做干净处 %d" % len(bad))
    for ln, body in bad[:20]:
        rep.append("  .tex 第 %d 行：%s" % (ln, body))
    ncerts, nsamp = norm_certificates(AUDIT_EXPRS)
    rep.append("范数证书：%d 个「a+b√m」型根号已证明在 Q(√m) 内开不动（N 不是有理 d 次幂）"
               % ncerts)
    for d, A, B, m, N in nsamp:
        rep.append("  例：%d 次根 a=%s b=%s m=%d，N=%s" % (d, A, B, m, N))
    print("  完全合并：%d 个公式，数值不符 %d，非幂等 %d，最大相对偏差 %.1e"
          "（不动点 %d／复检 %d／跳过 %d）"
          % (st["总次数"], st["数值不符"], st["非幂等"], st["最大相对偏差"],
             st["已验不动点"],
             st["总次数"] - st["已验不动点"] - st["跳过幂等"], st["跳过幂等"]))
    print("  输出审计：没做干净处 %d（根号内 \\frac／完全 d 次幂因子、分式没约分）"
          % len(bad))
    print("  范数证书：%d 个 a+b√m 型根号已证明在 Q(√m) 内开不动" % ncerts)

    if pdf:
        ok, log, hints, n_over = compile_pdf(tex_path, workdir)
        with open(os.path.join(workdir, "编译日志.txt"), "w",
                  encoding="utf-8") as f:
            f.write(log)
        rep.append("pdflatex：%s；Overfull 计数 = %d%s" %
                   ("成功" if ok else "失败", n_over,
                    "（有超界！）" if n_over else "（无超界）"))
        print("  " + rep[-1])
        if not ok:
            for ln in log.splitlines():
                if ln.startswith("!"):
                    print("  " + ln)
            if hints:
                print("  —— 出错处的 .tex 原文 ——")
                for h in hints[:40]:
                    print("  " + h)
                rep.append("出错处 .tex 原文：")
                rep += hints[:60]

    with open(os.path.join(workdir, "报告.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(rep) + "\n")
    print("  输出目录：%s" % workdir)
    return worst


def ask_n():
    while True:
        try:
            s = input("请输入 n（奇素数，或任意 n ≥ 2；q 退出）：").strip()
        except EOFError:
            return None
        if s.lower() in ("q", "quit", "exit"):
            return None
        if s.isdigit() and int(s) >= 2:
            return int(s)
        print("  请输入 ≥ 2 的整数。")


def main(argv):
    args = list(argv[1:])
    outroot, pdf, brief, cap = None, True, False, 200000
    if "--no-pdf" in args:
        pdf = False
        args.remove("--no-pdf")
    if "--brief" in args:
        brief = True
        args.remove("--brief")
    if "--cap" in args:
        i = args.index("--cap")
        cap = int(args[i + 1])
        del args[i:i + 2]
    if "-o" in args:
        i = args.index("-o")
        outroot = args[i + 1]
        del args[i:i + 2]
    if "--selftest" in args:
        selftest()
        return 0
    n = None
    for a in args:
        if a.isdigit():
            n = int(a)
    if n is None:
        n = ask_n()
        if n is None:
            return 1
    run_one(n, outroot=outroot, pdf=pdf, brief=brief, cap=cap)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
