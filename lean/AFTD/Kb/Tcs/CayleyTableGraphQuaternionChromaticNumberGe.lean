import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph
import AFTD.Kb.Tcs.QuaternionOddHasNoCompleteMapping
import AFTD.Kb.Tcs.QuaternionGroupCard

/-!
# cayley_table_graph_quaternion_chromatic_number_ge

Topic: combinatorics   Node: 76c2aec68d2f

Provenance: formalization of a published result. Source: arXiv:2611.13274 Sec. 6

For every integer n ≥ 1, the chromatic number of the Cayley table graph of the generalized quaternion group QuaternionGroup (2 * n + 1) is at least 8 * n + 6.
-/

open scoped Classical

/-- A color class of a coloring of the Cayley table graph is a partial transversal, so has at most
`|G| - 1 = 8n + 3` cells (a full one would be a complete mapping). -/
private lemma cayley_table_graph_quaternion_chromatic_number_ge_pt_card_le (n : ℕ)
    (S : Finset (QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1)))
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 * p.2 ≠ q.1 * q.2) :
    S.card ≤ 8 * n + 3 := by
  have hcard : Fintype.card (QuaternionGroup (2 * n + 1)) = 8 * n + 4 := quaternion_group_card n
  have hinjfst : Set.InjOn (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) => p.1) ↑S := by
    intro p hp q hq hpq
    by_contra hne
    exact (hS p hp q hq hne).1 hpq
  have hSle : S.card ≤ Fintype.card (QuaternionGroup (2 * n + 1)) := by
    calc S.card = (S.image (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) => p.1)).card :=
          (Finset.card_image_of_injOn hinjfst).symm
      _ ≤ Fintype.card (QuaternionGroup (2 * n + 1)) := Finset.card_le_univ _
  have key : S.card ≠ 8 * n + 4 := by
    intro hseq
    have huniv : S.image (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) => p.1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinjfst, hseq, hcard]
    have hex : ∀ x : QuaternionGroup (2 * n + 1), ∃ y, (x, y) ∈ S := by
      intro x
      have hx : x ∈ S.image (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) => p.1) := by
        rw [huniv]; exact Finset.mem_univ x
      obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 hx
      exact ⟨p.2, by simpa [← hpx] using hp⟩
    let θ : QuaternionGroup (2 * n + 1) → QuaternionGroup (2 * n + 1) :=
      fun x => if h : ∃ y, (x, y) ∈ S then h.choose else 1
    have hθ : ∀ x : QuaternionGroup (2 * n + 1), (x, θ x) ∈ S := by
      intro x
      have h := hex x
      simp only [θ, dif_pos h]
      exact h.choose_spec
    have hne_pair : ∀ x y : QuaternionGroup (2 * n + 1), x ≠ y → (x, θ x) ≠ (y, θ y) := by
      intro x y hxy hcon
      exact hxy (by simpa using congrArg Prod.fst hcon)
    have hinj : Function.Injective θ := by
      intro x y hxy
      by_contra hne
      exact (hS _ (hθ x) _ (hθ y) (hne_pair x y hne)).2.1 hxy
    have hbijθ : Function.Bijective θ := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
    have hinjmul : Function.Injective (fun x : QuaternionGroup (2 * n + 1) => x * θ x) := by
      intro x y hxy
      by_contra hne
      exact (hS _ (hθ x) _ (hθ y) (hne_pair x y hne)).2.2 hxy
    have hbijmul : Function.Bijective (fun x : QuaternionGroup (2 * n + 1) => x * θ x) :=
      ⟨hinjmul, Finite.injective_iff_surjective.1 hinjmul⟩
    exact quaternion_odd_has_no_complete_mapping n ⟨θ, hbijθ, hbijmul⟩
  omega

/-- Counting bound: every coloring of the Cayley table graph of `QuaternionGroup (2n+1)` uses at
least `8n + 6` colors. -/
private lemma cayley_table_graph_quaternion_chromatic_number_ge_colorable_bound (n m : ℕ)
    (C : (cayley_table_graph (QuaternionGroup (2 * n + 1))).Coloring (Fin m)) :
    8 * n + 6 ≤ m := by
  have hcard : Fintype.card (QuaternionGroup (2 * n + 1)) = 8 * n + 4 := quaternion_group_card n
  have hfiber : ∀ i : Fin m,
      (Finset.univ.filter (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) =>
        C p = i)).card ≤ 8 * n + 3 := by
    intro i
    apply cayley_table_graph_quaternion_chromatic_number_ge_pt_card_le n
    intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hCpq : C p = C q := by rw [hp, hq]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact C.valid ⟨hpq, Or.inl h⟩ hCpq
    · intro h
      exact C.valid ⟨hpq, Or.inr (Or.inl h)⟩ hCpq
    · intro h
      exact C.valid ⟨hpq, Or.inr (Or.inr h)⟩ hCpq
  have hsum : ∑ i : Fin m,
      (Finset.univ.filter (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) =>
        C p = i)).card
      = Fintype.card (QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1)) := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := C) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)).symm
  have h2 : ∑ _i : Fin m, (8 * n + 3) = m * (8 * n + 3) := by
    simp [Finset.sum_const, Finset.card_univ]
  have hle : (8 * n + 4) * (8 * n + 4) ≤ m * (8 * n + 3) := by
    have hGF : Fintype.card (QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1))
        = (8 * n + 4) * (8 * n + 4) := by rw [Fintype.card_prod, hcard]
    calc (8 * n + 4) * (8 * n + 4)
        = Fintype.card (QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1)) := hGF.symm
      _ = ∑ i : Fin m, (Finset.univ.filter (fun p : QuaternionGroup (2 * n + 1) × QuaternionGroup (2 * n + 1) => C p = i)).card := hsum.symm
      _ ≤ ∑ _i : Fin m, (8 * n + 3) := Finset.sum_le_sum (fun i _ => hfiber i)
      _ = m * (8 * n + 3) := h2
  have hlt : (8 * n + 5) * (8 * n + 3) < (8 * n + 4) * (8 * n + 4) := by nlinarith
  have h5 : 8 * n + 5 < m := Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hlt hle)
  omega

/-- Lower bound of 8n + 6 on the chromatic number of the Cayley table graph of QuaternionGroup (2 * n + 1). -/
theorem cayley_table_graph_quaternion_chromatic_number_ge (n : ℕ) (hn : 1 ≤ n) :
    (8 * n + 6 : ℕ∞) ≤ (cayley_table_graph (QuaternionGroup (2 * n + 1))).chromaticNumber := by
  rw [show (8 * ↑n + 6 : ℕ∞) = ((8 * n + 6 : ℕ) : ℕ∞) by push_cast; ring]
  rw [SimpleGraph.le_chromaticNumber_iff_colorable]
  intro m hm
  obtain ⟨C⟩ := hm
  exact cayley_table_graph_quaternion_chromatic_number_ge_colorable_bound n m C
