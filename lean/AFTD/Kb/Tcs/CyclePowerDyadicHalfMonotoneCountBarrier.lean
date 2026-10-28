import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_half_monotone_count_barrier

Topic: combinatorics   Node: 881946e4d536

Provenance: helper lemma. Auxiliary-model route barrier for OP-205 / RT-1 following arXiv:2610.15635 Section3; explicit period3 radius4 witness found in experiment7537. Existing radius8 count-variation witnesses already demonstrate the related omission-of-counts obstruction. No graph covering value or research advance claimed.

There exists a3-periodic radius4 Boolean class model with tight class weights, all exact dyadic edge equations, all ordinary edge coverage, and monotone first and second halves, but active count at vertex0 is2, below the putative optimal local lower bound3. This only refutes recovering the pointwise lower bound from these auxiliary assumptions; the original constant optimal-count hypothesis is omitted, so it is not a counterexample to OP-205.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_half_monotone_count_barrier :
    ∃ x : ℤ → ℕ → Bool,
      (∀ p a, x (p+3) a = x p a) ∧
      (∀ p, cycle_power_dyadic_class_weight 2 (x p) =
        (range 4).sum (fun a => (x p a).toNat)) ∧
      (∀ j < 2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+4-2^j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 4 → ∀ v : ℤ,
        ∃ a : ℕ, a < 4-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) ∧
      (∀ p : ℤ,
        (∀ a b : ℕ, a ≤ b → b < 2 → x p b = true → x p a = true) ∧
        (∀ a b : ℕ, 2 ≤ a → a ≤ b → b < 4 →
          x p a = true → x p b = true)) ∧
      (range 4).sum (fun a => (x (-(a : ℤ)) a).toNat) = 2 := by
  let b : ℤ → ℕ → Bool := fun r a =>
    decide (a=0 ∨ a=3 ∨ (r=0 ∧ a<4) ∨ (r=2 ∧ a=2))
  let x : ℤ → ℕ → Bool := fun p => b (p%3)
  have hres (p : ℤ) : p%3=0 ∨ p%3=1 ∨ p%3=2 := by omega
  have hshift (p : ℤ) (a : ℕ) : x (p-(a : ℤ)) = x (p%3-(a : ℤ)) := by
    dsimp [x]
    simp only [Int.sub_emod,Int.emod_emod]
  have htableT : ∀ r : Fin 3, cycle_power_dyadic_class_weight 2 (b (r.val : ℤ)) =
      (range 4).sum (fun a => (b (r.val : ℤ) a).toNat) := by decide
  have htableE : ∀ r : Fin 3, ∀ j : Fin 2,
      (range (2^j.val)).sum (fun a =>
        (x ((r.val : ℤ)-(a : ℤ)) a && x ((r.val : ℤ)-(a : ℤ))
          (a+4-2^j.val)).toNat) = 1 := by decide
  have htableC : ∀ r : Fin 3, ∀ d : Fin 4, 1 ≤ d.val →
      ∃ a : Fin 4, a.val < 4-d.val ∧
        x ((r.val : ℤ)-(a.val : ℤ)) a.val = true ∧
        x ((r.val : ℤ)-(a.val : ℤ)) (a.val+d.val) = true := by decide
  have htableS : ∀ r : Fin 3,
      (∀ a c : Fin 4, a.val ≤ c.val → c.val < 2 →
        b (r.val : ℤ) c.val = true → b (r.val : ℤ) a.val = true) ∧
      (∀ a c : Fin 4, 2 ≤ a.val → a.val ≤ c.val →
        b (r.val : ℤ) a.val = true → b (r.val : ℤ) c.val = true) := by decide
  refine ⟨x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p a
    dsimp [x]
    congr 1
    omega
  · intro p
    have hr : 0 ≤ p%3 := Int.emod_nonneg _ (by decide)
    simpa only [x,Int.toNat_of_nonneg hr] using
      htableT ⟨(p%3).toNat, by omega⟩
  · intro j hj v
    simp_rw [hshift v]
    have hr : 0 ≤ v%3 := Int.emod_nonneg _ (by decide)
    simpa only [Int.toNat_of_nonneg hr] using
      htableE ⟨(v%3).toNat,by omega⟩ ⟨j,hj⟩
  · intro d hd hd4 v
    have hr : 0 ≤ v%3 := Int.emod_nonneg _ (by decide)
    obtain ⟨a,ha,ha₀,ha₁⟩ := htableC ⟨(v%3).toNat,by omega⟩ ⟨d,hd4⟩ hd
    refine ⟨a.val,ha,?_,?_⟩
    · simpa only [hshift v a.val,Int.toNat_of_nonneg hr] using ha₀
    · simpa only [hshift v a.val,Int.toNat_of_nonneg hr] using ha₁
  · intro p
    have hr : 0 ≤ p%3 := Int.emod_nonneg _ (by decide)
    have hs := htableS ⟨(p%3).toNat,by omega⟩
    constructor
    · intro a c hac hc hb
      simpa only [x,Int.toNat_of_nonneg hr] using
        hs.1 ⟨a,by omega⟩ ⟨c,by omega⟩ hac hc (by simpa only [x,Int.toNat_of_nonneg hr] using hb)
    · intro a c ha hac hc hb
      simpa only [x,Int.toNat_of_nonneg hr] using
        hs.2 ⟨a,by omega⟩ ⟨c,by omega⟩ ha hac (by simpa only [x,Int.toNat_of_nonneg hr] using hb)
  · decide
