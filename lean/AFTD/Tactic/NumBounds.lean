import AFTD.Prelude

/-!
# `num_bounds` and `num_ineq`: numerical inequalities in one tactic call

A refutation by a computed instance often ends in a strict inequality between
closed real numbers such as `(100/3433 : ℝ) ^ ((1:ℝ)/2)`, `√3`, `Real.exp (1/2)`
or `Real.log 3`. `linarith` cannot see inside these terms, and `norm_num` can
only evaluate them when the value is rational. This file closes such goals.

* `num_bounds` (or `num_bounds 30`, the number of significant decimal digits;
  the default is 15) finds every closed real subterm of the goal and of the
  hypotheses that `linarith` would treat as an atom, computes rational numbers
  `lo` and `hi` with `lo ≤ t ≤ hi`, and adds both as hypotheses. The bounds are
  computed with exact rational and integer arithmetic (integer `q`-th roots,
  Taylor series with Mathlib's remainder bound) and every one is checked by
  the kernel through the lemmas below and `norm_num`; nothing is trusted.
* `num_ineq` (or `num_ineq 160`, the largest precision to try; the default is
  80) closes a goal `a < b`, `a ≤ b`, `a ≠ b` (or `False` from such
  hypotheses): it runs `norm_num`, then `num_bounds` at 10, 20, 40 and 80
  digits, each followed by `linarith`, and `nlinarith` as a last resort when
  there are at most four atoms. When it fails, its error message says which
  terms it could not bound and, for `a < b` or `a ≤ b`, an interval for
  `b - a`: if that interval lies below zero, the inequality is false.

## What is supported

A term is bounded when it is built from rational numerals (`3`, `1/3`, `2⁻¹`,
`0.25`, casts of numerals) with

* `+`, `-`, `*`, `/`, `⁻¹` (the divisor's interval must not contain 0);
* `x ^ n` for a natural-number literal `n` (`x` must be bounded below by 0);
* `x ^ c` (real power, `Real.rpow`) for a rational `c`: `x ≥ 0` when `c > 0`,
  `x > 0` when `c < 0`; the exponent itself must be a rational numeral
  expression, not an atom;
* `√x` (`Real.sqrt`);
* `Real.exp x` (`|x| ≤ 10000`; large arguments are slow);
* `Real.log x` (`x > 0`);
* `Real.pi` (20 digits at most, from `Real.pi_gt_d20` and `Real.pi_lt_d20`).

Arguments may themselves be such terms (`Real.exp (√2)`, `Real.log (1 + √5)`):
monotonicity carries an interval through each function. Not supported: free
variables (unfold `let`/`set` variables first, e.g. with `simp only [x]`),
`zpow` with a non-rational base, `x ^ y` with an irrational exponent,
trigonometric functions, `Real.cosh` etc. Terms that cannot be bounded are
skipped (and named in `num_ineq`'s error message).

`linarith` treats each atom as a variable, so products of two atoms are
bounded as a whole (`√2 * √3` gets its own bounds), and the bounds of an atom
that occurs in several places with different syntactic forms are computed
for each form.
-/

namespace AFTD.NumBounds

/-! ## Interval lemmas

Every lemma takes all its arguments explicitly, so that the tactic can apply
it to a list of terms and prove the remaining (closed, rational) side
conditions with `norm_num`. -/

theorem add_lo (a b la lb l : ℝ) (ha : la ≤ a) (hb : lb ≤ b) (h : l ≤ la + lb) :
    l ≤ a + b := by linarith
theorem add_hi (a b ua ub u : ℝ) (ha : a ≤ ua) (hb : b ≤ ub) (h : ua + ub ≤ u) :
    a + b ≤ u := by linarith
theorem sub_lo (a b la ub l : ℝ) (ha : la ≤ a) (hb : b ≤ ub) (h : l ≤ la - ub) :
    l ≤ a - b := by linarith
theorem sub_hi (a b ua lb u : ℝ) (ha : a ≤ ua) (hb : lb ≤ b) (h : ua - lb ≤ u) :
    a - b ≤ u := by linarith
theorem neg_lo (a ua l : ℝ) (ha : a ≤ ua) (h : l ≤ -ua) : l ≤ -a := by linarith
theorem neg_hi (a la u : ℝ) (ha : la ≤ a) (h : -la ≤ u) : -a ≤ u := by linarith

theorem mul_lo (a b la ua lb ub l : ℝ) (h1 : la ≤ a) (h2 : a ≤ ua) (h3 : lb ≤ b) (h4 : b ≤ ub)
    (c1 : l ≤ la * lb) (c2 : l ≤ la * ub) (c3 : l ≤ ua * lb) (c4 : l ≤ ua * ub) :
    l ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · have : la * b ≤ a * b := mul_le_mul_of_nonneg_right h1 hb
    rcases le_total 0 la with hl | hl
    · have : la * lb ≤ la * b := mul_le_mul_of_nonneg_left h3 hl
      linarith
    · have : la * ub ≤ la * b := mul_le_mul_of_nonpos_left h4 hl
      linarith
  · have : ua * b ≤ a * b := mul_le_mul_of_nonpos_right h2 hb
    rcases le_total 0 ua with hu | hu
    · have : ua * lb ≤ ua * b := mul_le_mul_of_nonneg_left h3 hu
      linarith
    · have : ua * ub ≤ ua * b := mul_le_mul_of_nonpos_left h4 hu
      linarith

theorem mul_hi (a b la ua lb ub u : ℝ) (h1 : la ≤ a) (h2 : a ≤ ua) (h3 : lb ≤ b) (h4 : b ≤ ub)
    (c1 : la * lb ≤ u) (c2 : la * ub ≤ u) (c3 : ua * lb ≤ u) (c4 : ua * ub ≤ u) :
    a * b ≤ u := by
  rcases le_total 0 b with hb | hb
  · have : a * b ≤ ua * b := mul_le_mul_of_nonneg_right h2 hb
    rcases le_total 0 ua with hu | hu
    · have : ua * b ≤ ua * ub := mul_le_mul_of_nonneg_left h4 hu
      linarith
    · have : ua * b ≤ ua * lb := mul_le_mul_of_nonpos_left h3 hu
      linarith
  · have : a * b ≤ la * b := mul_le_mul_of_nonpos_right h1 hb
    rcases le_total 0 la with hl | hl
    · have : la * b ≤ la * ub := mul_le_mul_of_nonneg_left h4 hl
      linarith
    · have : la * b ≤ la * lb := mul_le_mul_of_nonpos_left h3 hl
      linarith

theorem inv_lo_pos (a la ua l : ℝ) (h1 : la ≤ a) (h2 : a ≤ ua) (hp : 0 < la) (h : l ≤ ua⁻¹) :
    l ≤ a⁻¹ := le_trans h (inv_anti₀ (lt_of_lt_of_le hp h1) h2)
theorem inv_hi_pos (a la u : ℝ) (h1 : la ≤ a) (hp : 0 < la) (h : la⁻¹ ≤ u) : a⁻¹ ≤ u :=
  le_trans (inv_anti₀ hp h1) h
theorem inv_lo_neg (a ua l : ℝ) (h2 : a ≤ ua) (hn : ua < 0) (h : l ≤ ua⁻¹) : l ≤ a⁻¹ :=
  le_trans h ((inv_le_inv_of_neg hn (lt_of_le_of_lt h2 hn)).2 h2)
theorem inv_hi_neg (a la ua u : ℝ) (h1 : la ≤ a) (h2 : a ≤ ua) (hn : ua < 0) (h : la⁻¹ ≤ u) :
    a⁻¹ ≤ u :=
  le_trans ((inv_le_inv_of_neg (lt_of_le_of_lt h2 hn) (lt_of_le_of_lt (le_trans h1 h2) hn)).2 h1) h

theorem div_lo (a b l : ℝ) (h : l ≤ a * b⁻¹) : l ≤ a / b := by rwa [div_eq_mul_inv]
theorem div_hi (a b u : ℝ) (h : a * b⁻¹ ≤ u) : a / b ≤ u := by rwa [div_eq_mul_inv]

theorem pow_lo (a la l : ℝ) (n : ℕ) (h1 : la ≤ a) (h0 : 0 ≤ la) (h : l ≤ la ^ n) :
    l ≤ a ^ n := le_trans h (pow_le_pow_left₀ h0 h1 n)
theorem pow_hi (a la ua u : ℝ) (n : ℕ) (h1 : la ≤ a) (h2 : a ≤ ua) (h0 : 0 ≤ la)
    (h : ua ^ n ≤ u) : a ^ n ≤ u := le_trans (pow_le_pow_left₀ (le_trans h0 h1) h2 n) h

theorem sqrt_lo (a la l : ℝ) (h1 : la ≤ a) (h0 : 0 ≤ l) (h : l ^ 2 ≤ la) : l ≤ √a :=
  (Real.le_sqrt h0 (le_trans (le_trans (sq_nonneg l) h) h1)).2 (le_trans h h1)
theorem sqrt_lo_zero (a l : ℝ) (h : l ≤ 0) : l ≤ √a := le_trans h (Real.sqrt_nonneg a)
theorem sqrt_hi (a ua u : ℝ) (h2 : a ≤ ua) (h0 : 0 ≤ u) (h : ua ≤ u ^ 2) : √a ≤ u :=
  Real.sqrt_le_iff.2 ⟨h0, le_trans h2 h⟩

private theorem exp_nonneg_of_mul_eq {c : ℝ} {p q : ℕ} (hq : 0 < q) (hc : c * q = p) : 0 ≤ c := by
  by_contra hneg
  have h1 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : c * q < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) h1
  have h3 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

private theorem exp_nonpos_of_mul_eq {c : ℝ} {p q : ℕ} (hq : 0 < q) (hc : c * q = -p) :
    c ≤ 0 := by
  by_contra hpos
  have h1 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : 0 < c * q := mul_pos (lt_of_not_ge hpos) h1
  have h3 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

private theorem rpow_pow_pos {x c : ℝ} {p q : ℕ} (hx : 0 ≤ x) (hc : c * q = p) :
    (x ^ c) ^ q = x ^ p := by
  rw [← Real.rpow_natCast (x ^ c) q, ← Real.rpow_mul hx, hc, Real.rpow_natCast]

private theorem rpow_pow_neg {x c : ℝ} {p q : ℕ} (hx : 0 ≤ x) (hc : c * q = -p) :
    (x ^ c) ^ q = (x ^ p)⁻¹ := by
  rw [← Real.rpow_natCast (x ^ c) q, ← Real.rpow_mul hx, hc, Real.rpow_neg hx, Real.rpow_natCast]

/-- `x ^ c ≥ l` for `c = p / q > 0`, certified by `l ^ q ≤ la ^ p`. -/
theorem rpow_lo_pos (a c la l : ℝ) (p q : ℕ) (h1 : la ≤ a) (h0 : 0 ≤ la) (hq : 0 < q)
    (hc : c * q = p) (h : l ^ q ≤ la ^ p) : l ≤ a ^ c := by
  have hl : l ≤ la ^ c :=
    le_of_pow_le_pow_left₀ hq.ne' (Real.rpow_nonneg h0 c) (by rw [rpow_pow_pos h0 hc]; exact h)
  exact le_trans hl (Real.rpow_le_rpow h0 h1 (exp_nonneg_of_mul_eq hq hc))

/-- `x ^ c ≤ u` for `c = p / q > 0`, certified by `ua ^ p ≤ u ^ q`. -/
theorem rpow_hi_pos (a c la ua u : ℝ) (p q : ℕ) (h1 : la ≤ a) (h2 : a ≤ ua) (h0 : 0 ≤ la)
    (hq : 0 < q) (hc : c * q = p) (hu : 0 ≤ u) (h : ua ^ p ≤ u ^ q) : a ^ c ≤ u := by
  have hua : 0 ≤ ua := le_trans h0 (le_trans h1 h2)
  have hu' : ua ^ c ≤ u :=
    le_of_pow_le_pow_left₀ hq.ne' hu (by rw [rpow_pow_pos hua hc]; exact h)
  exact le_trans (Real.rpow_le_rpow (le_trans h0 h1) h2 (exp_nonneg_of_mul_eq hq hc)) hu'

/-- `x ^ c ≥ l` for `c = -p / q < 0`, certified by `l ^ q ≤ (ua ^ p)⁻¹`. -/
theorem rpow_lo_neg (a c la ua l : ℝ) (p q : ℕ) (h1 : la ≤ a) (h2 : a ≤ ua) (h0 : 0 < la)
    (hq : 0 < q) (hc : c * q = -p) (h : l ^ q ≤ (ua ^ p)⁻¹) : l ≤ a ^ c := by
  have ha : 0 < a := lt_of_lt_of_le h0 h1
  have hua : 0 ≤ ua := le_trans ha.le h2
  have hl : l ≤ ua ^ c :=
    le_of_pow_le_pow_left₀ hq.ne' (Real.rpow_nonneg hua c) (by rw [rpow_pow_neg hua hc]; exact h)
  exact le_trans hl (Real.rpow_le_rpow_of_nonpos ha h2 (exp_nonpos_of_mul_eq hq hc))

/-- `x ^ c ≤ u` for `c = -p / q < 0`, certified by `(la ^ p)⁻¹ ≤ u ^ q`. -/
theorem rpow_hi_neg (a c la u : ℝ) (p q : ℕ) (h1 : la ≤ a) (h0 : 0 < la) (hq : 0 < q)
    (hc : c * q = -p) (hu : 0 ≤ u) (h : (la ^ p)⁻¹ ≤ u ^ q) : a ^ c ≤ u := by
  have hu' : la ^ c ≤ u :=
    le_of_pow_le_pow_left₀ hq.ne' hu (by rw [rpow_pow_neg h0.le hc]; exact h)
  exact le_trans (Real.rpow_le_rpow_of_nonpos h0 h1 (exp_nonpos_of_mul_eq hq hc)) hu'

/-- Lower bound on `exp y` from the Taylor polynomial (`Real.exp_bound`). -/
theorem exp_lo_base (y l : ℝ) (n : ℕ) (hy : |y| ≤ 1) (hn : 0 < n)
    (h : l ≤ (∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)) -
      |y| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n))) : l ≤ Real.exp y := by
  have h2 := (abs_sub_le_iff.1 (Real.exp_bound hy hn)).2
  linarith

/-- Upper bound on `exp y` from the Taylor polynomial (`Real.exp_bound`). -/
theorem exp_hi_base (y u : ℝ) (n : ℕ) (hy : |y| ≤ 1) (hn : 0 < n)
    (h : (∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ)) +
      |y| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) ≤ u) : Real.exp y ≤ u := by
  have h2 := (abs_sub_le_iff.1 (Real.exp_bound hy hn)).1
  linarith

theorem exp_sq_lo (t x l l' : ℝ) (hx : 2 * t = x) (h : l ≤ Real.exp t) (h0 : 0 ≤ l)
    (h' : l' ≤ l ^ 2) : l' ≤ Real.exp x := by
  subst hx
  rw [two_mul, Real.exp_add, ← sq]
  exact le_trans h' (pow_le_pow_left₀ h0 h 2)

theorem exp_sq_hi (t x u u' : ℝ) (hx : 2 * t = x) (h : Real.exp t ≤ u) (h' : u ^ 2 ≤ u') :
    Real.exp x ≤ u' := by
  subst hx
  rw [two_mul, Real.exp_add, ← sq]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos t).le h 2) h'

theorem exp_lo (a la l : ℝ) (h1 : la ≤ a) (h : l ≤ Real.exp la) : l ≤ Real.exp a :=
  le_trans h (Real.exp_le_exp.2 h1)
theorem exp_hi (a ua u : ℝ) (h2 : a ≤ ua) (h : Real.exp ua ≤ u) : Real.exp a ≤ u :=
  le_trans (Real.exp_le_exp.2 h2) h

theorem log_lo_of_exp (x l v : ℝ) (hx : 0 < x) (he : Real.exp l ≤ v) (h : v ≤ x) :
    l ≤ Real.log x := (Real.le_log_iff_exp_le hx).2 (le_trans he h)
theorem log_hi_of_exp (x u v : ℝ) (hx : 0 < x) (he : v ≤ Real.exp u) (h : x ≤ v) :
    Real.log x ≤ u := (Real.log_le_iff_le_exp hx).2 (le_trans h he)
theorem log_lo (a la l : ℝ) (h1 : la ≤ a) (h0 : 0 < la) (h : l ≤ Real.log la) :
    l ≤ Real.log a := le_trans h (Real.log_le_log h0 h1)
theorem log_hi (a la ua u : ℝ) (h1 : la ≤ a) (h2 : a ≤ ua) (h0 : 0 < la)
    (h : Real.log ua ≤ u) : Real.log a ≤ u :=
  le_trans (Real.log_le_log (lt_of_lt_of_le h0 h1) h2) h

theorem pi_lo (l : ℝ) (h : l ≤ 3.14159265358979323846) : l ≤ Real.pi :=
  le_trans h Real.pi_gt_d20.le
theorem pi_hi (u : ℝ) (h : 3.14159265358979323847 ≤ u) : Real.pi ≤ u :=
  le_trans Real.pi_lt_d20.le h

/-! ## Exact rational arithmetic (meta level) -/

open Lean Meta Elab Tactic Qq

/-- `10 ^ s` as a rational, for any integer `s`. -/
def pow10 (s : Int) : ℚ :=
  if 0 ≤ s then ((10 ^ s.toNat : ℕ) : ℚ) else 1 / ((10 ^ (-s).toNat : ℕ) : ℚ)

def ndigits (n : ℕ) : ℕ := (toString n).length

/-- Roughly `⌊log₁₀ |q|⌋` (off by at most one). -/
def mag (q : ℚ) : Int := (ndigits q.num.natAbs : Int) - (ndigits q.den : Int)

def qabs (q : ℚ) : ℚ := if q < 0 then -q else q

/-- The largest rational with about `P` significant digits that is `≤ q`. -/
def roundDown (q : ℚ) (P : ℕ) : ℚ :=
  if q == 0 then 0 else
  let sc := pow10 ((P : Int) - mag q)
  ((q * sc).floor : ℚ) / sc

/-- The smallest rational with about `P` significant digits that is `≥ q`. -/
def roundUp (q : ℚ) (P : ℕ) : ℚ := -roundDown (-q) P

/-- `q` in scientific notation with about `d` significant digits, rounded up or down. -/
def fmtQ (q : ℚ) (up : Bool) (d : ℕ := 10) : String :=
  if q == 0 then "0" else
  let r := if up then roundUp q d else roundDown q d
  let s : Int := (d : Int) - mag q
  let ks := toString (qabs r * pow10 s).floor.toNat
  let e : Int := (ks.length : Int) - 1 - s
  let mant := if ks.length > 1 then
      String.ofList (ks.toList.take 1) ++ "." ++ String.ofList (ks.toList.drop 1) else ks
  (if r < 0 then "-" else "") ++ mant ++ "e" ++ toString e

/-- `[lo, hi]` for messages. -/
def fmtI (lo hi : ℚ) : String := s!"[{fmtQ lo false}, {fmtQ hi true}]"

/-- `⌊a ^ (1/q)⌋` by Newton's method from an upper estimate. -/
def iroot (a q : ℕ) : ℕ := Id.run do
  if q ≤ 1 || a < 2 then return a
  let mut g : ℕ := 2 ^ ((a.log2 + 1 + q - 1) / q)
  for _ in [0:100000] do
    let next := ((q - 1) * g + a / g ^ (q - 1)) / q
    if next < g then g := next else break
  while a < g ^ q do g := g - 1
  while (g + 1) ^ q ≤ a do g := g + 1
  return g

/-- For `v ≥ 0`, rationals `l, u ≥ 0` with about `P` significant digits and
`l ^ q ≤ v ≤ u ^ q`. -/
def rootBounds (v : ℚ) (q P : ℕ) : ℚ × ℚ :=
  if v ≤ 0 then (0, 0) else
  let s : Int := (P : Int) - mag v / (q : Int)
  let R := v * pow10 (s * q)
  let k := iroot R.floor.toNat q
  let sc := pow10 s
  let l : ℚ := (k : ℚ) / sc
  (l, if (k : ℚ) ^ q == R then l else ((k + 1 : ℕ) : ℚ) / sc)

/-- The Taylor sum `∑_{m<n} y^m/m!` and Mathlib's remainder bound
`|y|^n (n+1)/(n! n)` (see `Real.exp_bound`). -/
def expSeries (y : ℚ) (n : ℕ) : ℚ × ℚ := Id.run do
  let mut s : ℚ := 0
  let mut t : ℚ := 1
  let mut fact : ℕ := 1
  for m in [0:n] do
    s := s + t
    t := t * y / ((m + 1 : ℕ) : ℚ)
    fact := fact * (m + 1)
  return (s, qabs y ^ n * ((n + 1 : ℕ) : ℚ) / ((fact * n : ℕ) : ℚ))

/-- How `exp x` is computed: `x = y · 2^k` with `|y| ≤ 1/32`, `n` Taylor terms,
`prec` working digits. -/
structure ExpPlan where
  k : ℕ
  y : ℚ
  n : ℕ
  prec : ℕ

def expPlan (x : ℚ) (P : ℕ) : ExpPlan := Id.run do
  let mut k := 0
  let mut a := qabs x
  while a > 1 / 32 do
    a := a / 2
    k := k + 1
  let prec := P + 4 + k / 2
  let y := x / ((2 ^ k : ℕ) : ℚ)
  let mut n := 1
  while (expSeries y n).2 > pow10 (-(prec : Int)) do n := n + 1
  return ⟨k, y, n, prec⟩

/-- `⌊atanh t · S⌋` (approximately) for `0 ≤ t < 1`, in fixed point. -/
def atanhFix (t : ℚ) (S : Int) : Int := Id.run do
  let T : Int := (t * S).floor
  let T2 : Int := T * T / S
  let mut pw := T
  let mut sum : Int := 0
  let mut j : Nat := 0
  for _ in [0:1000000] do
    if pw == 0 then break
    sum := sum + pw / (2 * j + 1 : Nat)
    pw := pw * T2 / S
    j := j + 1
  return sum

/-- `log x` to about `W` decimal places (an estimate, not a bound). -/
def lnApprox (x : ℚ) (W : ℕ) : ℚ := Id.run do
  let S : Int := 10 ^ W
  let mut m := x
  let mut k : Int := 0
  while m > 4 / 3 do
    m := m / 2
    k := k + 1
  while m < 2 / 3 do
    m := m * 2
    k := k - 1
  let ln2 := 2 * atanhFix (1 / 3) S
  let t := (m - 1) / (m + 1)
  let ath := if t < 0 then -atanhFix (-t) S else atanhFix t S
  return ((k * ln2 + 2 * ath : Int) : ℚ) / (S : ℚ)

/-! ## Building proofs -/

/-- The real numeral `n / d` (or `-(n / d)`, `n`) for a rational. -/
def ratLit (q : ℚ) : MetaM Expr := do
  let r := mkConst ``Real
  let n ← mkNumeral r q.num.natAbs
  let e ← if q.den == 1 then pure n else mkAppM ``HDiv.hDiv #[n, ← mkNumeral r q.den]
  if q.num < 0 then mkAppM ``Neg.neg #[e] else pure e

/-- The rational value of a closed real expression, if `norm_num` can compute it. -/
def ratValue? (e : Expr) : MetaM (Option ℚ) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  try
    let r ← Mathlib.Meta.NormNum.derive (α := (q(ℝ) : Q(Type))) e
    return r.toRat
  catch _ => return none

/-- Prove a closed proposition `p` by the tactic `tac`. -/
def proveBy (tac : TSyntax `tactic) (what : String) (p : Expr) : TacticM Expr := do
  let m ← mkFreshExprMVar p
  let run : TacticM (List MVarId) := Tactic.run m.mvarId! (evalTactic tac)
  let gs ← tryCatch run fun ex =>
    throwError "num_bounds: {what} failed on{indentExpr p}\n{ex.toMessageData}"
  unless gs.isEmpty do throwError "num_bounds: {what} did not close{indentExpr p}"
  instantiateMVars m

/-- Prove a closed numerical proposition with `norm_num`. -/
def proveNormNum (p : Expr) : TacticM Expr := do
  proveBy (← `(tactic| norm_num)) "norm_num" p

/-- The side condition of a Taylor bound: expand the sum, then `norm_num`. -/
def proveTaylor (p : Expr) : TacticM Expr := do
  proveBy (← `(tactic| norm_num [Finset.sum_range_succ, Nat.factorial])) "norm_num (Taylor bound)" p

/-- Apply the lemma `nm` to `args`; each `none` is a side condition, proved by `side`. -/
def applyLemma (nm : Name) (args : List (Option Expr))
    (side : Expr → TacticM Expr := proveNormNum) : TacticM Expr := do
  let mut f := mkConst nm
  let mut ty ← inferType f
  for a in args do
    match ty with
    | .forallE _ bty body _ =>
      let v ← match a with
        | some v => pure v
        | none => side bty
      f := mkApp f v
      ty := body.instantiate1 v
    | _ => throwError "num_bounds: too many arguments for {nm}"
  return f

/-- A rational interval for a term, with proofs `loE ≤ e` and `e ≤ hiE`, where
`loE` and `hiE` are `ratLit lo` and `ratLit hi`. -/
structure Bnd where
  lo : ℚ
  hi : ℚ
  loE : Expr
  hiE : Expr
  loPf : Expr
  hiPf : Expr

/-- `l ≤ Real.exp x` for a rational `x`, with `l` about `P` digits. -/
def expLo (x : ℚ) (P : ℕ) : TacticM (ℚ × Expr × Expr) := do
  let pl := expPlan x P
  if qabs x > 10000 then throwError "num_bounds: exp argument {x} is too large"
  let (s, err) := expSeries pl.y pl.n
  let mut l := roundDown (s - err) pl.prec
  let mut lE ← ratLit l
  let mut tE ← ratLit pl.y
  let mut t := pl.y
  let mut pf ← applyLemma ``exp_lo_base [tE, lE, mkNatLit pl.n, none, none, none] proveTaylor
  for _ in [0:pl.k] do
    let t' := 2 * t
    let l' := roundDown (l * l) pl.prec
    let t'E ← ratLit t'
    let l'E ← ratLit l'
    pf ← applyLemma ``exp_sq_lo [tE, t'E, lE, l'E, none, pf, none, none]
    t := t'; tE := t'E; l := l'; lE := l'E
  return (l, lE, pf)

/-- `Real.exp x ≤ u` for a rational `x`, with `u` about `P` digits. -/
def expHi (x : ℚ) (P : ℕ) : TacticM (ℚ × Expr × Expr) := do
  let pl := expPlan x P
  if qabs x > 10000 then throwError "num_bounds: exp argument {x} is too large"
  let (s, err) := expSeries pl.y pl.n
  let mut u := roundUp (s + err) pl.prec
  let mut uE ← ratLit u
  let mut tE ← ratLit pl.y
  let mut t := pl.y
  let mut pf ← applyLemma ``exp_hi_base [tE, uE, mkNatLit pl.n, none, none, none] proveTaylor
  for _ in [0:pl.k] do
    let t' := 2 * t
    let u' := roundUp (u * u) pl.prec
    let t'E ← ratLit t'
    let u'E ← ratLit u'
    pf ← applyLemma ``exp_sq_hi [tE, t'E, uE, u'E, none, pf, none]
    t := t'; tE := t'E; u := u'; uE := u'E
  return (u, uE, pf)

/-- The estimate of `log x` and the margin around it used for the bounds. -/
def logPlan (x : ℚ) (P : ℕ) : ℚ × ℚ × ℕ :=
  let L := lnApprox x (2 * P + 10)
  let δ := max (qabs L * pow10 (-(P : Int))) (pow10 (-(2 * P : Int)))
  (L, δ, (-(mag δ)).toNat + 4)

/-- `l ≤ Real.log x` for a rational `x > 0`, certified by `exp l ≤ x`. -/
def logLo (x : ℚ) (P : ℕ) : TacticM (ℚ × Expr × Expr) := do
  let (L, δ, Pe) := logPlan x P
  let l := roundDown (L - δ / 2) (P + 3)
  let (v, vE, pf) ← expHi l Pe
  unless v ≤ x do throwError "num_bounds: could not certify a lower bound of log {x}"
  let lE ← ratLit l
  let pf ← applyLemma ``log_lo_of_exp [← ratLit x, lE, vE, none, pf, none]
  return (l, lE, pf)

/-- `Real.log x ≤ u` for a rational `x > 0`, certified by `x ≤ exp u`. -/
def logHi (x : ℚ) (P : ℕ) : TacticM (ℚ × Expr × Expr) := do
  let (L, δ, Pe) := logPlan x P
  let u := roundUp (L + δ / 2) (P + 3)
  let (v, vE, pf) ← expLo u Pe
  unless x ≤ v do throwError "num_bounds: could not certify an upper bound of log {x}"
  let uE ← ratLit u
  let pf ← applyLemma ``log_hi_of_exp [← ratLit x, uE, vE, none, pf, none]
  return (u, uE, pf)

def isReal (t : Expr) : Bool := t.isConstOf ``Real

/-- Rational bounds, with proofs, on a closed real term (see the module doc). -/
partial def bound (P : ℕ) (e : Expr) : TacticM Bnd := do
  if let some q ← ratValue? e then
    let qE ← ratLit q
    let lo ← proveNormNum (← mkAppM ``LE.le #[qE, e])
    let hi ← proveNormNum (← mkAppM ``LE.le #[e, qE])
    return ⟨q, q, qE, qE, lo, hi⟩
  let mk (l u : ℚ) (fl : Expr → TacticM Expr) (fu : Expr → TacticM Expr) : TacticM Bnd := do
    let lE ← ratLit l
    let uE ← ratLit u
    return ⟨l, u, lE, uE, ← fl lE, ← fu uE⟩
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P a
    let y ← bound P b
    mk (roundDown (x.lo + y.lo) P) (roundUp (x.hi + y.hi) P)
      (fun lE => applyLemma ``add_lo [a, b, x.loE, y.loE, lE, x.loPf, y.loPf, none])
      (fun uE => applyLemma ``add_hi [a, b, x.hiE, y.hiE, uE, x.hiPf, y.hiPf, none])
  | (``HSub.hSub, #[α, _, _, _, a, b]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P a
    let y ← bound P b
    mk (roundDown (x.lo - y.hi) P) (roundUp (x.hi - y.lo) P)
      (fun lE => applyLemma ``sub_lo [a, b, x.loE, y.hiE, lE, x.loPf, y.hiPf, none])
      (fun uE => applyLemma ``sub_hi [a, b, x.hiE, y.loE, uE, x.hiPf, y.loPf, none])
  | (``Neg.neg, #[α, _, a]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P a
    mk (-x.hi) (-x.lo)
      (fun lE => applyLemma ``neg_lo [a, x.hiE, lE, x.hiPf, none])
      (fun uE => applyLemma ``neg_hi [a, x.loE, uE, x.loPf, none])
  | (``HMul.hMul, #[α, _, _, _, a, b]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P a
    let y ← bound P b
    let cs := [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
    let lo := cs.foldl min (x.lo * y.lo)
    let hi := cs.foldl max (x.lo * y.lo)
    let args := [some a, some b, some x.loE, some x.hiE, some y.loE, some y.hiE]
    let pfs := [some x.loPf, some x.hiPf, some y.loPf, some y.hiPf, none, none, none, none]
    mk (roundDown lo P) (roundUp hi P)
      (fun lE => applyLemma ``mul_lo (args ++ [some lE] ++ pfs))
      (fun uE => applyLemma ``mul_hi (args ++ [some uE] ++ pfs))
  | (``Inv.inv, #[α, _, a]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P a
    if 0 < x.lo then
      mk (roundDown x.hi⁻¹ P) (roundUp x.lo⁻¹ P)
        (fun lE => applyLemma ``inv_lo_pos [a, x.loE, x.hiE, lE, x.loPf, x.hiPf, none, none])
        (fun uE => applyLemma ``inv_hi_pos [a, x.loE, uE, x.loPf, none, none])
    else if x.hi < 0 then
      mk (roundDown x.hi⁻¹ P) (roundUp x.lo⁻¹ P)
        (fun lE => applyLemma ``inv_lo_neg [a, x.hiE, lE, x.hiPf, none, none])
        (fun uE => applyLemma ``inv_hi_neg [a, x.loE, x.hiE, uE, x.loPf, x.hiPf, none, none])
    else
      throwError "num_bounds: the interval {fmtI x.lo x.hi} of an inverted term contains 0"
  | (``HDiv.hDiv, #[α, _, _, _, a, b]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    let x ← bound P (← mkAppM ``HMul.hMul #[a, ← mkAppM ``Inv.inv #[b]])
    return { x with
      loPf := ← applyLemma ``div_lo [a, b, x.loE, x.loPf]
      hiPf := ← applyLemma ``div_hi [a, b, x.hiE, x.hiPf] }
  | (``HPow.hPow, #[α, β, _, _, a, b]) =>
    unless isReal α do throwError "num_bounds: not a real term{indentExpr e}"
    if β.isConstOf ``Nat then
      let some n ← (evalNat b).run | throwError "num_bounds: exponent {b} is not a numeral"
      let x ← bound P a
      unless 0 ≤ x.lo do
        throwError "num_bounds: x ^ {n} needs x ≥ 0, but x ∈ {fmtI x.lo x.hi}"
      mk (roundDown (x.lo ^ n) P) (roundUp (x.hi ^ n) P)
        (fun lE => applyLemma ``pow_lo [a, x.loE, lE, b, x.loPf, none, none])
        (fun uE => applyLemma ``pow_hi [a, x.loE, x.hiE, uE, b, x.loPf, x.hiPf, none, none])
    else if isReal β then
      let some c ← ratValue? b | throwError "num_bounds: real exponent {b} is not rational"
      let p := c.num.natAbs
      let q := c.den
      let pE := mkNatLit p
      let qE := mkNatLit q
      let x ← bound P a
      if 0 < c then
        unless 0 ≤ x.lo do
          throwError "num_bounds: x ^ {c} needs x ≥ 0, but x ∈ {fmtI x.lo x.hi}"
        mk (rootBounds (x.lo ^ p) q P).1 (rootBounds (x.hi ^ p) q P).2
          (fun lE => applyLemma ``rpow_lo_pos
            [a, b, x.loE, lE, pE, qE, x.loPf, none, none, none, none])
          (fun uE => applyLemma ``rpow_hi_pos
            [a, b, x.loE, x.hiE, uE, pE, qE, x.loPf, x.hiPf, none, none, none, none, none])
      else if c < 0 then
        unless 0 < x.lo do
          throwError "num_bounds: x ^ {c} needs x > 0, but x ∈ {fmtI x.lo x.hi}"
        mk (rootBounds (x.hi ^ p)⁻¹ q P).1 (rootBounds (x.lo ^ p)⁻¹ q P).2
          (fun lE => applyLemma ``rpow_lo_neg
            [a, b, x.loE, x.hiE, lE, pE, qE, x.loPf, x.hiPf, none, none, none, none])
          (fun uE => applyLemma ``rpow_hi_neg
            [a, b, x.loE, uE, pE, qE, x.loPf, none, none, none, none, none])
      else throwError "num_bounds: x ^ 0 is not handled (simplify it with `Real.rpow_zero`)"
    else throwError "num_bounds: unsupported power {e}"
  | (``Real.rpow, #[a, b]) =>
    let x ← bound P (← mkAppM ``HPow.hPow #[a, b])
    return x
  | (``Real.sqrt, #[a]) =>
    let x ← bound P a
    let l := if x.lo ≤ 0 then 0 else (rootBounds x.lo 2 P).1
    let u := if x.hi ≤ 0 then 0 else (rootBounds x.hi 2 P).2
    mk l u
      (fun lE => if x.lo ≤ 0 then applyLemma ``sqrt_lo_zero [a, lE, none]
        else applyLemma ``sqrt_lo [a, x.loE, lE, x.loPf, none, none])
      (fun uE => applyLemma ``sqrt_hi [a, x.hiE, uE, x.hiPf, none, none])
  | (``Real.exp, #[a]) =>
    let x ← bound P a
    let (l, lE, pl) ← expLo x.lo P
    let (u, uE, pu) ← expHi x.hi P
    return ⟨l, u, lE, uE, ← applyLemma ``exp_lo [a, x.loE, lE, x.loPf, pl],
      ← applyLemma ``exp_hi [a, x.hiE, uE, x.hiPf, pu]⟩
  | (``Real.log, #[a]) =>
    let x ← bound P a
    unless 0 < x.lo do
      throwError "num_bounds: log x needs x > 0, but x ∈ {fmtI x.lo x.hi}"
    let (l, lE, pl) ← logLo x.lo P
    let (u, uE, pu) ← logHi x.hi P
    return ⟨l, u, lE, uE, ← applyLemma ``log_lo [a, x.loE, lE, x.loPf, none, pl],
      ← applyLemma ``log_hi [a, x.loE, x.hiE, uE, x.loPf, x.hiPf, none, pu]⟩
  | (``Real.pi, #[]) =>
    let P' := min P 20
    mk (roundDown (314159265358979323846 / 10 ^ 20) P') (roundUp (314159265358979323847 / 10 ^ 20) P')
      (fun lE => applyLemma ``pi_lo [lE, none])
      (fun uE => applyLemma ``pi_hi [uE, none])
  | _ => throwError "num_bounds: unsupported term {e}"

/-! ## Finding the atoms -/

/-- Closed real terms that `linarith` would see as atoms (nonlinear in their
non-numeral parts). -/
def isAtom (e : Expr) : MetaM Bool := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return false
  let nonRat (x : Expr) : MetaM Bool := return (← ratValue? x).isNone
  let r ← match e.getAppFnArgs with
    | (``Real.sqrt, #[_]) | (``Real.exp, #[_]) | (``Real.log, #[_]) | (``Real.rpow, #[_, _])
    | (``Real.pi, #[]) => pure true
    | (``HPow.hPow, #[α, β, _, _, a, _]) =>
      pure (isReal α && (isReal β || β.isConstOf ``Nat)) <&&> (if isReal β then pure true else nonRat a)
    | (``HMul.hMul, #[α, _, _, _, a, b]) => pure (isReal α) <&&> nonRat a <&&> nonRat b
    | (``HDiv.hDiv, #[α, _, _, _, _, b]) => pure (isReal α) <&&> nonRat b
    | (``Inv.inv, #[α, _, a]) => pure (isReal α) <&&> nonRat a
    | _ => pure false
  if !r then return false
  return (← ratValue? e).isNone

partial def collect (e : Expr) : StateT (Array Expr) MetaM Unit := do
  match e with
  | .app .. | .const .. =>
    if ← isAtom e then
      unless (← get).contains e do modify (·.push e)
      return
    if e.isApp then
      collect e.getAppFn
      for a in e.getAppArgs do collect a
  | .mdata _ b => collect b
  | .lam _ t b _ | .forallE _ t b _ => collect t; collect b
  | .letE _ t v b _ => collect t; collect v; collect b
  | .proj _ _ b => collect b
  | _ => pure ()

/-- The atoms of the main goal and its hypotheses. -/
def atoms : TacticM (Array Expr) := withMainContext do
  let mut es := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then es := es.push (← instantiateMVars d.type)
  let ((), acc) ← (es.forM collect).run #[]
  return acc

/-- Add `lo ≤ t` and `t ≤ hi` for every atom `t`; returns the bounds added and
the atoms that could not be bounded, with the reason. -/
def numBoundsCore (P : ℕ) : TacticM (Array (Expr × ℚ × ℚ) × Array MessageData) :=
  withMainContext do
    let g ← getMainGoal
    let mut hyps : Array Hypothesis := #[]
    let mut done := #[]
    let mut fails := #[]
    for a in ← atoms do
      try
        let b ← bound P a
        let tl ← mkAppM ``LE.le #[b.loE, a]
        let th ← mkAppM ``LE.le #[a, b.hiE]
        unless (← isDefEq (← inferType b.loPf) tl) && (← isDefEq (← inferType b.hiPf) th) do
          throwError "num_bounds: internal error, proof does not match{indentExpr a}"
        hyps := hyps.push { userName := ← Core.mkFreshUserName `nb, type := tl, value := b.loPf }
        hyps := hyps.push { userName := ← Core.mkFreshUserName `nb, type := th, value := b.hiPf }
        done := done.push (a, b.lo, b.hi)
      catch ex =>
        fails := fails.push m!"{a}: {ex.toMessageData}"
    unless hyps.isEmpty do
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']
    return (done, fails)

/--
`num_bounds` adds rational bounds `lo ≤ t` and `t ≤ hi` for every closed real
term `t` of the goal and hypotheses that `linarith` would treat as an atom:
`√x`, `x ^ (c : ℝ)` with rational `c`, `Real.exp x`, `Real.log x`, `Real.pi`,
and products, quotients, inverses and natural powers of such terms, where the
arguments are built from numerals with `+ - * / ⁻¹` and these functions.
`num_bounds 30` asks for about 30 significant digits (default 15). Every bound
is proved (integer roots, Taylor bounds with remainder, monotonicity, then
`norm_num`). Follow it with `linarith`; or use `num_ineq`, which does both.
Fails only if no atom could be bounded.
-/
syntax (name := numBoundsTac) "num_bounds" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| num_bounds $[$n]?) => do
    let P := n.map (·.getNat) |>.getD 15
    let (done, fails) ← numBoundsCore P
    if done.isEmpty then
      if fails.isEmpty then
        throwError "num_bounds: no term to bound (√, real powers, exp, log, π, or products, \
          quotients and powers of them, with numeric arguments) in the goal or hypotheses"
      else
        throwError "num_bounds: no term could be bounded:\n{MessageData.joinSep fails.toList "\n"}"

/-- Try `num_bounds P; linarith` on the main goal, restoring the state on failure. -/
def tryClose (P : ℕ) (useNlinarith : Bool) : TacticM Bool := do
  let s ← saveState
  try
    let (done, _) ← try numBoundsCore P catch _ => pure (#[], #[])
    if useNlinarith then
      unless done.size ≤ 4 do throwError "too many atoms for nlinarith"
      evalTactic (← `(tactic| nlinarith))
    else
      evalTactic (← `(tactic| linarith))
    return true
  catch _ =>
    s.restore
    return false

/-- What `num_ineq` reports when it fails. -/
def diagnose (P : ℕ) : TacticM MessageData := withMainContext do
  let s ← saveState
  let mut msg := m!""
  try
    let (done, fails) ← numBoundsCore P
    msg := msg ++ m!"\nbounded at {P} digits: {done.size} term(s)"
    for (a, lo, hi) in done do
      msg := msg ++ m!"\n  {a} ∈ {fmtI lo hi}"
    unless fails.isEmpty do
      msg := msg ++ m!"\nnot bounded:\n  {MessageData.joinSep fails.toList "\n  "}"
  catch ex => msg := msg ++ m!"\n{ex.toMessageData}"
  s.restore
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let side? : Option (Expr × Expr) := match t.getAppFnArgs with
    | (``LT.lt, #[_, _, a, b]) | (``LE.le, #[_, _, a, b]) => some (a, b)
    | (``GT.gt, #[_, _, a, b]) | (``GE.ge, #[_, _, a, b]) => some (b, a)
    | _ => none
  if let some (a, b) := side? then
    if (← inferType a).isConstOf ``Real && !a.hasFVar && !b.hasFVar then
      try
        let x ← bound P (← mkAppM ``HSub.hSub #[b, a])
        msg := msg ++ m!"\nright side − left side ∈ {fmtI x.lo x.hi}"
        if x.hi < 0 then msg := msg ++ m!" < 0: the inequality is false."
        else if x.lo ≤ 0 then
          msg := msg ++ m!" (contains 0: the gap is below this precision, or the terms \
            depend on each other in a way interval arithmetic cannot see)"
      catch _ => pure ()
      s.restore
  return msg

/--
`num_ineq` closes a goal `a < b`, `a ≤ b`, `a > b`, `a ≥ b` or `a ≠ b` between
real expressions containing `√x`, `x ^ (c : ℝ)` with rational `c`,
`Real.exp`, `Real.log` and `Real.pi` applied to numeric arguments (and goals
`False` from such hypotheses). It runs `norm_num`, then `num_bounds P;
linarith` for `P` = 10, 20, 40, 80 significant digits, then `nlinarith` when
there are at most four atoms. `num_ineq 200` raises the largest precision
tried to 200. On failure the error lists the bounds it found and an interval
for `b - a`. Unfold definitions first (`simp only [f, Fin.sum_univ_two, ...]`)
so that the numbers are visible.
-/
syntax (name := numIneqTac) "num_ineq" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| num_ineq $[$n]?) => do
    let maxP := n.map (·.getNat) |>.getD 80
    let precs := ([10, 20, 40, 80].filter (· ≤ maxP)) ++
      (if [10, 20, 40, 80].contains maxP then [] else [maxP])
    try evalTactic (← `(tactic| norm_num)) catch _ => pure ()
    if (← getGoals).isEmpty then return
    let attempt : TacticM Bool := do
      for P in precs do
        if ← tryClose P false then return true
      tryClose (precs.getLast?.getD 10) true
    if ← attempt then return
    -- `a ≠ b`: prove `a < b` or `b < a`.
    let t ← whnfR (← instantiateMVars (← getMainTarget))
    if t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Eq 3 then
      for lem in [``ne_of_lt, ``ne_of_gt] do
        let s ← saveState
        try
          let gs ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels lem)
          replaceMainGoal gs
          if ← attempt then return
        catch _ => pure ()
        s.restore
    let msg ← diagnose (min maxP 20)
    throwError "num_ineq: could not prove the goal with bounds at {precs} significant digits \
      followed by linarith.{msg}"

end AFTD.NumBounds
