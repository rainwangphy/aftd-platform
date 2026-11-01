import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleSameCycleCardBounds

/-!
# restricted_cycle_all_same_cycle_of_short

Topic: elementary_number_theory   Node: 3d2b47cbb784

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

If n is less than 2(r+1), any permutation of Fin n avoiding cycle lengths 1 through r has every two points in the same cycle.
-/

theorem restricted_cycle_all_same_cycle_of_short (r n : ℕ) (hn : n < 2 * (r+1))
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ x : Fin n,
      (Finset.univ.filter fun y => σ.SameCycle x y).card ∉ Finset.Icc 1 r) :
    ∀ x y : Fin n, σ.SameCycle x y := by
  classical
  have hlarge (x : Fin n) : r+1 ≤ (Finset.univ.filter fun y => σ.SameCycle x y).card := by
    have hb := (Finset.mem_Icc.mp (restricted_cycle_same_cycle_card_bounds n σ x)).1
    have hx := hσ x
    simp only [Finset.mem_Icc] at hx
    omega
  intro x y
  by_contra hxy
  have hd : Disjoint (Finset.univ.filter fun z => σ.SameCycle x z)
      (Finset.univ.filter fun z => σ.SameCycle y z) := by
    apply Finset.disjoint_left.mpr
    intro z hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hxy (hx.trans hy.symm)
  have hc := Finset.card_union_of_disjoint hd
  have hu : ((Finset.univ.filter fun z => σ.SameCycle x z) ∪
      (Finset.univ.filter fun z => σ.SameCycle y z)).card ≤ n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hx := hlarge x
  have hy := hlarge y
  omega
