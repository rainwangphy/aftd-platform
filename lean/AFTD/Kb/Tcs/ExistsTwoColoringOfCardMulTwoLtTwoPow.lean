import AFTD.Prelude
import AFTD.Kb.Tcs.ExistsNotMemOfSumCardLt

/-!
# exists_two_coloring_of_card_mul_two_lt_two_pow

Topic: combinatorics   Node: ecbc4c950657

Property B (Erdős). Let α be a finite set, let k ≥ 1, and let F be a finite family of subsets of α, each of cardinality at least k. If 2·|F| < 2^k, then there is a Boolean colouring c : α → Bool under which no member of F is monochromatic, that is, for every A ∈ F it is not the case that every element of A has c = true, nor that every element of A has c = false.
-/

/-- Erdős's Property-B bound: a hypergraph with fewer than 2^{k-1} edges, each of size at least k, admits a 2-colouring with no monochromatic edge. -/
theorem exists_two_coloring_of_card_mul_two_lt_two_pow {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 1 ≤ k) (F : Finset (Finset α)) (hsize : ∀ A ∈ F, k ≤ A.card)
    (hcard : F.card * 2 < 2 ^ k) :
    ∃ c : α → Bool, ∀ A ∈ F, ¬ (∀ a ∈ A, c a = true) ∧ ¬ (∀ a ∈ A, c a = false) := by
  classical
  have _ : 1 ≤ k := hk
  have card_const_le : ∀ (A : Finset α) (b : Bool),
      (Finset.univ.filter (fun c : α → Bool => ∀ a ∈ A, c a = b)).card
        ≤ 2 ^ (Fintype.card α - A.card) := by
    intro A b
    rw [← Fintype.card_subtype (fun c : α → Bool => ∀ a ∈ A, c a = b)]
    have hle : Fintype.card {c : α → Bool // ∀ a ∈ A, c a = b}
        ≤ Fintype.card ({x : α // x ∉ A} → Bool) := by
      apply Fintype.card_le_of_injective (fun c => fun x => c.1 x.1)
      intro c1 c2 h
      ext x
      by_cases hx : x ∈ A
      · rw [c1.2 x hx, c2.2 x hx]
      · exact congr_fun h ⟨x, hx⟩
    calc Fintype.card {c : α → Bool // ∀ a ∈ A, c a = b}
        ≤ Fintype.card ({x : α // x ∉ A} → Bool) := hle
      _ = 2 ^ (Fintype.card α - A.card) := by
          rw [Fintype.card_fun, Fintype.card_bool]
          congr 1
          rw [Fintype.card_subtype_compl (fun x : α => x ∈ A)]
          congr 1
          rw [Fintype.card_subtype]
          simp
  let g : Finset α → Finset (α → Bool) := fun A =>
    Finset.univ.filter (fun c : α → Bool =>
      (∀ a ∈ A, c a = true) ∨ (∀ a ∈ A, c a = false))
  by_cases hF : F = ∅
  · subst hF
    exact ⟨fun _ => true, by simp⟩
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨A0, hA0⟩ := hFne
    have hkn : k ≤ Fintype.card α :=
      le_trans (hsize A0 hA0) (Finset.card_le_univ A0)
    have hsum_lt : ∑ b ∈ F.image g, b.card < (Finset.univ : Finset (α → Bool)).card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
      have h1 : ∑ b ∈ F.image g, b.card ≤ ∑ A ∈ F, (g A).card := by
        have hcomp := Finset.sum_comp (s := F) (f := fun b : Finset (α → Bool) => b.card) (g := g)
        rw [hcomp]
        apply Finset.sum_le_sum
        intro b hb
        have hpos : 1 ≤ (F.filter (fun A => g A = b)).card := by
          rw [Finset.one_le_card]
          rcases Finset.mem_image.mp hb with ⟨A, hA, rfl⟩
          exact ⟨A, by simp [hA]⟩
        calc b.card = 1 * b.card := (one_mul _).symm
          _ ≤ (F.filter (fun A => g A = b)).card * b.card := Nat.mul_le_mul_right _ hpos
          _ = (F.filter (fun A => g A = b)).card • b.card := (nsmul_eq_mul _ _).symm
      have h2 : ∑ A ∈ F, (g A).card ≤ F.card * (2 * 2 ^ (Fintype.card α - k)) := by
        have hterm : ∀ A ∈ F, (g A).card ≤ 2 * 2 ^ (Fintype.card α - k) := by
          intro A hA
          have hkA : k ≤ A.card := hsize A hA
          have hsub : Fintype.card α - A.card ≤ Fintype.card α - k :=
            Nat.sub_le_sub_left hkA (Fintype.card α)
          have hpow : 2 ^ (Fintype.card α - A.card) ≤ 2 ^ (Fintype.card α - k) :=
            Nat.pow_le_pow_right (by norm_num) hsub
          have hg : (g A).card ≤
              (Finset.univ.filter (fun c : α → Bool => ∀ a ∈ A, c a = true)).card
              + (Finset.univ.filter (fun c : α → Bool => ∀ a ∈ A, c a = false)).card := by
            change (Finset.univ.filter (fun c : α → Bool =>
                (∀ a ∈ A, c a = true) ∨ (∀ a ∈ A, c a = false))).card ≤ _
            rw [Finset.filter_or]
            exact Finset.card_union_le _ _
          calc (g A).card
              ≤ (Finset.univ.filter (fun c : α → Bool => ∀ a ∈ A, c a = true)).card
                + (Finset.univ.filter (fun c : α → Bool => ∀ a ∈ A, c a = false)).card := hg
            _ ≤ 2 ^ (Fintype.card α - A.card) + 2 ^ (Fintype.card α - A.card) :=
                add_le_add (card_const_le A true) (card_const_le A false)
            _ = 2 * 2 ^ (Fintype.card α - A.card) := by ring
            _ ≤ 2 * 2 ^ (Fintype.card α - k) := Nat.mul_le_mul_left 2 hpow
        calc ∑ A ∈ F, (g A).card ≤ ∑ A ∈ F, (2 * 2 ^ (Fintype.card α - k)) :=
              Finset.sum_le_sum hterm
          _ = F.card * (2 * 2 ^ (Fintype.card α - k)) := by
              rw [Finset.sum_const]
              simp
      have h3 : F.card * (2 * 2 ^ (Fintype.card α - k)) < 2 ^ (Fintype.card α) := by
        rw [← mul_assoc]
        exact lt_of_lt_of_eq
          (Nat.mul_lt_mul_of_pos_right hcard (Nat.two_pow_pos (Fintype.card α - k)))
          (by rw [← Nat.pow_add, Nat.add_sub_of_le hkn])
      exact lt_of_le_of_lt (le_trans h1 h2) h3
    obtain ⟨c, _, hc⟩ := exists_notMem_of_sum_card_lt (Finset.univ : Finset (α → Bool)) (F.image g) hsum_lt
    refine ⟨c, ?_⟩
    intro A hA
    have hmem : g A ∈ F.image g := Finset.mem_image.mpr ⟨A, hA, rfl⟩
    have hnot := hc (g A) hmem
    simp only [g, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
