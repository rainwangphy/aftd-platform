import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle
import AFTD.Kb.GameTheoryEconomics.AllocationIsEf1
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable
import AFTD.Kb.Tcs.G

/-!
# exists_submodular_instance_no_ef1_envy_freeable_allocation_with_bobw_lottery

Topic: fair_division   Node: 91c3c9840051

Provenance: formalization of a published result. Source: arXiv:2610.14994 (Best-of-both-worlds fair division via subsidies), Theorem 5.1 (the instance: t = (5, 8, 11, 0), u = (9, 1, 0, 10) on goods a, b, c, d, v_1(S) = min(11, t(S)) + min(10, u(S)), v_2, v_3 by rotating a → b → c; lottery uniform on (ac, b, d), (d, ab, c), (a, d, bc)).

There is an instance with three agents and four indivisible goods, each agent having a normalized monotone submodular valuation, in which no complete allocation is both EF1 and envy-freeable, yet some lottery over complete allocations is ex-ante envy-free and supported on EF1 allocations.
-/

def ef1_efable_cex_value (i : Fin 3) (S : Finset (Fin 4)) : ℤ :=
  min 11 (∑ g ∈ S, (![![5, 8, 11, 0], ![11, 5, 8, 0], ![8, 11, 5, 0]] : Fin 3 → Fin 4 → ℤ) i g) +
    min 10 (∑ g ∈ S, (![![9, 1, 0, 10], ![0, 9, 1, 10], ![1, 0, 9, 10]] : Fin 3 → Fin 4 → ℤ) i g)

def ef1_efable_cex_weight (A : Fin 4 → Fin 3) : ℕ :=
  if A = ![0, 1, 0, 2] ∨ A = ![1, 1, 2, 0] ∨ A = ![0, 2, 2, 1] then 1 else 0

def ef1_efable_cex_perms : List (Equiv.Perm (Fin 3)) :=
  [Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2, finRotate 3, (finRotate 3).symm]

theorem ef1_efable_cex_not_envy_freeable_of_perm {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] (v : N → Finset M → ℝ) (A : M → N) (σ : Equiv.Perm N)
    (h : ∑ i, v i (allocation_bundle A i) < ∑ i, v i (allocation_bundle A (σ i))) :
    ¬ allocation_is_envy_freeable v A := by
  rintro ⟨p, -, hp⟩
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hp i (σ i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ p] at hs
  linarith

theorem ef1_efable_cex_ef1_iff (A : Fin 4 → Fin 3) :
    allocation_is_ef1 (fun i S => (ef1_efable_cex_value i S : ℝ)) A ↔
      ∀ i j, ef1_efable_cex_value i (allocation_bundle A j) ≤
          ef1_efable_cex_value i (allocation_bundle A i) ∨
        ∃ g ∈ allocation_bundle A j, ef1_efable_cex_value i ((allocation_bundle A j).erase g) ≤
          ef1_efable_cex_value i (allocation_bundle A i) := by
  simp only [allocation_is_ef1, Int.cast_le]

theorem ef1_efable_cex_key : ∀ A : Fin 4 → Fin 3,
    ¬ (∀ i j, ef1_efable_cex_value i (allocation_bundle A j) ≤
          ef1_efable_cex_value i (allocation_bundle A i) ∨
        ∃ g ∈ allocation_bundle A j, ef1_efable_cex_value i ((allocation_bundle A j).erase g) ≤
          ef1_efable_cex_value i (allocation_bundle A i)) ∨
    ∃ σ ∈ ef1_efable_cex_perms, ∑ i, ef1_efable_cex_value i (allocation_bundle A i) <
      ∑ i, ef1_efable_cex_value i (allocation_bundle A (σ i)) := by
  decide +kernel

theorem ef1_efable_cex_mono : ∀ i (S T : Finset (Fin 4)), S ⊆ T →
    ef1_efable_cex_value i S ≤ ef1_efable_cex_value i T := by
  decide +kernel

theorem ef1_efable_cex_submod : ∀ i (S T : Finset (Fin 4)),
    ef1_efable_cex_value i (S ∪ T) + ef1_efable_cex_value i (S ∩ T) ≤
      ef1_efable_cex_value i S + ef1_efable_cex_value i T := by
  decide +kernel

theorem ef1_efable_cex_support_ef1 : ∀ A : Fin 4 → Fin 3, ef1_efable_cex_weight A ≠ 0 →
    ∀ i j, ef1_efable_cex_value i (allocation_bundle A j) ≤
          ef1_efable_cex_value i (allocation_bundle A i) ∨
        ∃ g ∈ allocation_bundle A j, ef1_efable_cex_value i ((allocation_bundle A j).erase g) ≤
          ef1_efable_cex_value i (allocation_bundle A i) := by
  decide +kernel

theorem ef1_efable_cex_weight_sum : ∑ A : Fin 4 → Fin 3, ef1_efable_cex_weight A = 3 := by
  decide +kernel

theorem ef1_efable_cex_ex_ante : ∀ i j : Fin 3,
    ∑ A : Fin 4 → Fin 3, (ef1_efable_cex_weight A : ℤ) * ef1_efable_cex_value i (allocation_bundle A j) ≤
      ∑ A : Fin 4 → Fin 3, (ef1_efable_cex_weight A : ℤ) * ef1_efable_cex_value i (allocation_bundle A i) := by
  decide +kernel

theorem exists_submodular_instance_no_ef1_envy_freeable_allocation_with_bobw_lottery :
    ∃ v : Fin 3 → Finset (Fin 4) → ℝ,
      (∀ i, v i ∅ = 0) ∧ (∀ i S T, S ⊆ T → v i S ≤ v i T) ∧
      (∀ i S T, v i (S ∪ T) + v i (S ∩ T) ≤ v i S + v i T) ∧
      (∀ A : Fin 4 → Fin 3, ¬ (allocation_is_ef1 v A ∧ allocation_is_envy_freeable v A)) ∧
      ∃ q : (Fin 4 → Fin 3) → ℝ, (∀ A, 0 ≤ q A) ∧ ∑ A, q A = 1 ∧
        (∀ A, q A ≠ 0 → allocation_is_ef1 v A) ∧
        ∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i) := by
  refine ⟨fun i S => (ef1_efable_cex_value i S : ℝ), ?_, ?_, ?_, ?_,
    fun A => (ef1_efable_cex_weight A : ℝ) / 3, ?_, ?_, ?_, ?_⟩
  · intro i
    have : ef1_efable_cex_value i ∅ = 0 := by revert i; decide
    simp [this]
  · intro i S T hST
    dsimp only
    exact_mod_cast ef1_efable_cex_mono i S T hST
  · intro i S T
    dsimp only
    exact_mod_cast ef1_efable_cex_submod i S T
  · rintro A ⟨hef1, hfree⟩
    rcases ef1_efable_cex_key A with h | ⟨σ, -, hσ⟩
    · exact h ((ef1_efable_cex_ef1_iff A).1 hef1)
    · exact ef1_efable_cex_not_envy_freeable_of_perm _ A σ (by exact_mod_cast hσ) hfree
  · intro A; positivity
  · rw [← Finset.sum_div]
    have : ((∑ A : Fin 4 → Fin 3, ef1_efable_cex_weight A : ℕ) : ℝ) = 3 := by
      rw [ef1_efable_cex_weight_sum]; norm_num
    push_cast at this
    rw [this]; norm_num
  · intro A hA
    have hA' : ef1_efable_cex_weight A ≠ 0 := by
      intro h; apply hA; simp [h]
    exact (ef1_efable_cex_ef1_iff A).2 (ef1_efable_cex_support_ef1 A hA')
  · intro i j
    have key := ef1_efable_cex_ex_ante i j
    have e : ∀ k : Fin 3, ∑ A : Fin 4 → Fin 3,
        (ef1_efable_cex_weight A : ℝ) / 3 * (ef1_efable_cex_value i (allocation_bundle A k) : ℝ) =
        ((∑ A : Fin 4 → Fin 3, (ef1_efable_cex_weight A : ℤ) *
          ef1_efable_cex_value i (allocation_bundle A k) : ℤ) : ℝ) / 3 := by
      intro k
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun A _ => ?_
      ring
    rw [e j, e i]
    have : ((∑ A : Fin 4 → Fin 3, (ef1_efable_cex_weight A : ℤ) *
          ef1_efable_cex_value i (allocation_bundle A j) : ℤ) : ℝ) ≤
        ((∑ A : Fin 4 → Fin 3, (ef1_efable_cex_weight A : ℤ) *
          ef1_efable_cex_value i (allocation_bundle A i) : ℤ) : ℝ) := by
      exact_mod_cast key
    linarith
