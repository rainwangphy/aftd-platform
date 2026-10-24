import AFTD.Prelude

/-!
# coprime_residue_small_rectangle

Topic: elementary_number_theory   Node: 4781c6e142cc

Provenance: helper lemma. Supporting modular proof for the two-dimensional cone atom bound, a standard fact described in Combinatorial Commutative Algebra, Example 7.19 (https://pages.uoregon.edu/njp/MS.pdf). Used toward the four-support reduction for OP-197, arXiv:2610.16562 Conjecture 1; no new research-level result is claimed.

If a and b are each coprime to D, are smaller than D, and sum to more than D, then some nonzero k<D has (k*a) mod D<a and (k*b) mod D<=b. Multiplication by each coefficient permutes the residues, and two lower rank sets have intersection size at least two.
-/

open Finset
set_option maxHeartbeats 2000000

theorem coprime_residue_small_rectangle
    (D a b : ℕ) (hD : 0 < D) (ha : a < D) (hb : b < D)
    (hca : Nat.Coprime a D) (hcb : Nat.Coprime b D) (hs : D < a + b) :
    ∃ k : ℕ, k < D ∧ 0 < k ∧ (k * a) % D < a ∧ (k * b) % D ≤ b := by
  classical
  letI : NeZero D := ⟨by omega⟩
  have make_perm : ∀ t : ℕ, Nat.Coprime t D →
      ∃ e : Equiv.Perm (Fin D), ∀ i, (e i).val = (i.val * t) % D := by
    intro t ht
    let f : Fin D → Fin D := fun i => ⟨(i.val * t) % D, Nat.mod_lt _ hD⟩
    have hinj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have hh : Nat.ModEq D (i.val * t) (j.val * t) := congrArg Fin.val hij
      have hc := Nat.ModEq.cancel_right_of_coprime ht.symm hh
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hc
    exact ⟨Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, fun _ => rfl⟩
  obtain ⟨e, he⟩ := make_perm a hca
  obtain ⟨f, hf⟩ := make_perm b hcb
  let A := univ.filter fun i : Fin D => (e i).val < a
  let B := univ.filter fun i : Fin D => (f i).val < b + 1
  have hA : A.card = a := by
    have hmap : A = (univ.filter fun i : Fin D => i.val < a).map e.symm.toEmbedding := by
      ext i
      simp [A]
    rw [hmap, card_map, Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt ha)]
  have hB : B.card = b + 1 := by
    have hmap : B = (univ.filter fun i : Fin D => i.val < b + 1).map f.symm.toEmbedding := by
      ext i
      simp [B]
    rw [hmap, card_map, Fin.card_filter_val_lt, min_eq_right (by omega)]
  have hex : ∃ i : Fin D, i ≠ 0 ∧ (e i).val < a ∧ (f i).val ≤ b := by
    by_contra hnone
    have hsub : A ∩ B ⊆ {0} := by
      intro i hi
      have hiA := (mem_filter.mp (mem_inter.mp hi).1).2
      have hiB := (mem_filter.mp (mem_inter.mp hi).2).2
      by_cases hz : i = 0
      · simp [hz]
      · exact False.elim (hnone ⟨i, hz, hiA, by omega⟩)
    have hint : (A ∩ B).card ≤ 1 := by simpa using card_le_card hsub
    have hunion : (A ∪ B).card ≤ D := by simpa using card_le_univ (A ∪ B)
    have hsum := card_union_add_card_inter A B
    omega
  obtain ⟨i, hi, hiA, hiB⟩ := hex
  refine ⟨i.val, i.isLt, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro hz
    apply hi
    apply Fin.ext
    simpa using hz
  · rwa [he] at hiA
  · rwa [hf] at hiB
