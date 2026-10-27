import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicHalfMonotoneOfMiddleFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_hierarchy_half_monotone_of_middle_full_prune

Topic: combinatorics   Node: a0a9880dfb4c

Provenance: helper lemma. Uniform conditional structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The middle-bit fullness assumptions and smaller-quarter monotonicity are explicit when used; no optimal-count classification, graph covering value or research advance is claimed.

A compatible hierarchy of tight exact full-coverage dyadic models has monotone endpoint halves at every level, provided every selected middle bit at EVERY level forces a full prune. This is a conditional all-scale classification, not a derivation of those fullness hypotheses from optimal counts.
-/

open Finset

theorem cycle_power_dyadic_hierarchy_half_monotone_of_middle_full_prune
    (M : ℕ) (B : ℕ → ℤ → ℕ → Bool)
    (htight : ∀ r ≤ M, ∀ p, cycle_power_dyadic_class_weight (r+1) (B r p) =
      (range (2^(r+1))).sum (fun a => (B r p a).toNat))
    (hexact : ∀ r ≤ M, ∀ j < r+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (B r (v-(a : ℤ)) a && B r (v-(a : ℤ)) (a+2^(r+1)-2^j)).toNat) = 1)
    (hcover : ∀ r ≤ M, ∀ d : ℕ, 1 ≤ d → d < 2^(r+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(r+1)-d ∧ B r (v-(c : ℤ)) c = true ∧
        B r (v-(c : ℤ)) (c+d) = true)
    (hprune : ∀ r < M, ∀ p a, B r p a = cycle_power_dyadic_b_lift r (B (r+1) p) a)
    (hmid : ∀ r < M, ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 3*2^r →
      B (r+1) p a = true → ∀ i < 2^(r+1), B r p i = true) :
    ∀ r ≤ M, ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^r → B r p b = true → B r p a = true) ∧
      (∀ a b : ℕ, 2^r ≤ a → a ≤ b → b < 2^(r+1) →
        B r p a = true → B r p b = true) := by
  intro r
  induction r with
  | zero =>
    intro hr p
    constructor
    · intro a b hab hb hx
      norm_num at hb
      have he : a=b := by omega
      simpa only [he] using hx
    · intro a b ha hab hb hx
      norm_num at ha hb
      have he : a=b := by omega
      simpa only [he] using hx
  | succ r ih =>
    intro hr
    have hrM : r < M := by omega
    have hH : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
    have hD : 2^(r+2)=4*2^r := by
      rw [show r+2=(r+1)+1 by omega,pow_succ,hH]; omega
    have hB (p : ℤ) : B r p = cycle_power_dyadic_b_lift r (B (r+1) p) :=
      funext (hprune r hrM p)
    have hleft : ∀ (p : ℤ) (a b : ℕ), a ≤ b → b < 2^r →
        B (r+1) p b = true → B (r+1) p a = true := by
      intro p a b hab hb hx
      have ha : a < 2^r := by omega
      have hla : B r p a = B (r+1) p a := by rw [hB]; simp [cycle_power_dyadic_b_lift,ha]
      have hlb : B r p b = B (r+1) p b := by rw [hB]; simp [cycle_power_dyadic_b_lift,hb]
      rw [← hla]
      exact (ih (by omega) p).1 a b hab hb (by simpa only [hlb] using hx)
    have hright : ∀ (p : ℤ) (a b : ℕ), 3*2^r ≤ a → a ≤ b → b < 2^(r+2) →
        B (r+1) p a = true → B (r+1) p b = true := by
      intro p a b ha hab hb hx
      let u := a-2^(r+1)
      let v := b-2^(r+1)
      have hu0 : 2^r ≤ u := by dsimp [u]; omega
      have huv : u ≤ v := by dsimp [u,v]; omega
      have hv : v < 2^(r+1) := by dsimp [v]; omega
      have hua : u+2^(r+1)=a := by dsimp [u]; omega
      have hvb : v+2^(r+1)=b := by dsimp [v]; omega
      have hla : B r p u = B (r+1) p a := by
        rw [hB]; simp only [cycle_power_dyadic_b_lift,if_neg (by omega : ¬u<2^r),hua]
      have hlb : B r p v = B (r+1) p b := by
        rw [hB]; simp only [cycle_power_dyadic_b_lift,if_neg (by omega : ¬v<2^r),hvb]
      rw [← hlb]
      exact (ih (by omega) p).2 u v hu0 huv hv (by simpa only [hla] using hx)
    have hmf : ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 3*2^r →
        B (r+1) p a = true → ∀ i < 2^(r+1),
          cycle_power_dyadic_b_lift r (B (r+1) p) i = true := by
      intro p a ha hb hx i hi
      rw [← hprune r hrM p i]
      exact hmid r hrM p a ha hb hx i hi
    exact cycle_power_dyadic_half_monotone_of_middle_full_prune r (B (r+1))
      (htight (r+1) (by omega)) (hexact (r+1) (by omega)) hmf hleft hright
      (hcover (r+1) (by omega))
