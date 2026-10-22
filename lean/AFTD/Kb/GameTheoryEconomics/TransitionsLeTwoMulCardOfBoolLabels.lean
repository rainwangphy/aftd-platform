import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# transitions_le_two_mul_card_of_bool_labels

Topic: fair_division   Node: 5c979c6a7935

Provenance: helper lemma. arXiv:2610.27956 Proposition 1

For any positive natural number m with [NeZero m], any type ι, any finite set L of elements of ι, any natural number k, any coloring α : ZMod m → Fin k, and any family of boolean functions s : ι → ZMod m → Bool: if for all i, j in ZMod m, agreement of s ℓ i = s ℓ j for all ℓ ∈ L implies α i = α j, and for every ℓ ∈ L the number of cyclic transitions where s ℓ i ≠ s ℓ (i + 1) is at most 2, then the number of cyclic transitions where α i ≠ α (i + 1) is at most 2 * L.card.
-/

/-- If each label in a finite set L induces at most two transitions along a cyclic sequence of length m, and colorings factor through L, then the total number of transitions is at most 2 * |L|. -/
theorem transitions_le_two_mul_card_of_bool_labels {m : ℕ} [NeZero m] {ι : Type*} (L : Finset ι)
    {k : ℕ} (α : ZMod m → Fin k) (s : ι → ZMod m → Bool)
    (h_alloc : ∀ i j : ZMod m, (∀ ℓ ∈ L, s ℓ i = s ℓ j) → α i = α j)
    (h_two : ∀ ℓ ∈ L, (Finset.univ.filter (fun i : ZMod m => s ℓ i ≠ s ℓ (i + 1))).card ≤ 2) :
    (Finset.univ.filter (fun i : ZMod m => α i ≠ α (i + 1))).card ≤ 2 * L.card := by
  have h_sub : (Finset.univ.filter (fun i : ZMod m => α i ≠ α (i + 1))) ⊆
      L.biUnion (fun ℓ => Finset.univ.filter (fun i : ZMod m => s ℓ i ≠ s ℓ (i + 1))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_biUnion]
    by_contra hcon
    have heq : ∀ ℓ ∈ L, s ℓ i = s ℓ (i + 1) := by
      intro ℓ hℓ
      by_contra hne
      apply hcon
      exact ⟨ℓ, hℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩⟩
    exact hi.2 (h_alloc i (i + 1) heq)
  have h1 := Finset.card_le_card h_sub
  have h2 : (L.biUnion (fun ℓ => Finset.univ.filter (fun i : ZMod m => s ℓ i ≠ s ℓ (i + 1)))).card ≤
      ∑ ℓ ∈ L, (Finset.univ.filter (fun i : ZMod m => s ℓ i ≠ s ℓ (i + 1))).card :=
    Finset.card_biUnion_le
  have h3 : (∑ ℓ ∈ L, (Finset.univ.filter (fun i : ZMod m => s ℓ i ≠ s ℓ (i + 1))).card) ≤ ∑ ℓ ∈ L, 2 :=
    Finset.sum_le_sum fun ℓ hℓ => h_two ℓ hℓ
  simp only [Finset.sum_const, smul_eq_mul] at h3
  linarith
