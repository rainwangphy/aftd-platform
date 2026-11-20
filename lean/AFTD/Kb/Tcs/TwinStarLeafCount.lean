import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLeafCount
import AFTD.Kb.Tcs.TwinStar

/-!
# twin_star_leaf_count

Topic: graphs   Node: a9c75212c637

Provenance: formalization of a published result. Source: arXiv:2611.19473, Lemma 2.7

For any natural number d ≥ 2, the number of leaves graph_leaf_count of the twin-star graph TS_d on Fin d ⊕ Fin d is equal to 2 * d - 2.
-/

open Classical in
private theorem twin_star_leaf_count_nf_inl (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (hi : i.val ≠ 0) :
    (twin_star d).neighborFinset (Sum.inl i) = {Sum.inl ⟨0, by omega⟩} := by
  ext (y | y)
  · rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    dsimp [twin_star, SimpleGraph.fromRel]
    constructor
    · rintro ⟨_, ⟨hi0, -⟩ | ⟨hy0, -⟩⟩
      · contradiction
      · congr 1; ext; exact hy0
    · intro h
      injection h with hy
      subst hy
      refine ⟨by intro h; injection h with h; exact hi (by subst h; rfl), Or.inr ⟨rfl, hi⟩⟩
  · rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    dsimp [twin_star, SimpleGraph.fromRel]
    constructor
    · rintro ⟨-, ⟨hi0, -⟩ | h_false⟩
      · contradiction
      · contradiction
    · intro h; contradiction

open Classical in
private theorem twin_star_leaf_count_nf_inr (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (hi : i.val ≠ 0) :
    (twin_star d).neighborFinset (Sum.inr i) = {Sum.inr ⟨0, by omega⟩} := by
  ext (y | y)
  · rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    dsimp [twin_star, SimpleGraph.fromRel]
    constructor
    · rintro ⟨-, h_false | ⟨hy0, hi0⟩⟩
      · contradiction
      · exact (hi hi0).elim
    · intro h; contradiction
  · rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    dsimp [twin_star, SimpleGraph.fromRel]
    constructor
    · rintro ⟨_, ⟨hi0, -⟩ | ⟨hy0, -⟩⟩
      · contradiction
      · congr 1; ext; exact hy0
    · intro h
      injection h with hy
      subst hy
      refine ⟨by intro h; injection h with h; exact hi (by subst h; rfl), Or.inr ⟨rfl, hi⟩⟩

open Classical in
private theorem twin_star_leaf_count_deg_inl_zero (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (hi : i.val = 0) :
    (twin_star d).degree (Sum.inl i) ≠ 1 := by
  let a : Fin d ⊕ Fin d := Sum.inr ⟨0, by omega⟩
  let b : Fin d ⊕ Fin d := Sum.inl ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; contradiction
  have ha : a ∈ (twin_star d).neighborFinset (Sum.inl i) := by
    rw [SimpleGraph.mem_neighborFinset]
    dsimp [twin_star, SimpleGraph.fromRel, a]
    refine ⟨by intro h; contradiction, Or.inl ⟨hi, rfl⟩⟩
  have hb : b ∈ (twin_star d).neighborFinset (Sum.inl i) := by
    rw [SimpleGraph.mem_neighborFinset]
    dsimp [twin_star, SimpleGraph.fromRel, b]
    refine ⟨?_, Or.inl ⟨hi, by decide⟩⟩
    intro h
    injection h with h
    have : (⟨1, by omega⟩ : Fin d).val = 1 := rfl
    have : i.val = 1 := by rw [h]
    omega
  intro h
  have hsub : {a, b} ⊆ (twin_star d).neighborFinset (Sum.inl i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  change ((twin_star d).neighborFinset (Sum.inl i)).card = 1 at h
  omega

open Classical in
private theorem twin_star_leaf_count_deg_inr_zero (d : ℕ) (hd : 2 ≤ d) (i : Fin d) (hi : i.val = 0) :
    (twin_star d).degree (Sum.inr i) ≠ 1 := by
  let a : Fin d ⊕ Fin d := Sum.inl ⟨0, by omega⟩
  let b : Fin d ⊕ Fin d := Sum.inr ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; contradiction
  have ha : a ∈ (twin_star d).neighborFinset (Sum.inr i) := by
    rw [SimpleGraph.mem_neighborFinset]
    dsimp [twin_star, SimpleGraph.fromRel, a]
    refine ⟨by intro h; contradiction, Or.inr ⟨rfl, hi⟩⟩
  have hb : b ∈ (twin_star d).neighborFinset (Sum.inr i) := by
    rw [SimpleGraph.mem_neighborFinset]
    dsimp [twin_star, SimpleGraph.fromRel, b]
    refine ⟨?_, Or.inl ⟨hi, by decide⟩⟩
    intro h
    injection h with h
    have : (⟨1, by omega⟩ : Fin d).val = 1 := rfl
    have : i.val = 1 := by rw [h]
    omega
  intro h
  have hsub : {a, b} ⊆ (twin_star d).neighborFinset (Sum.inr i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  change ((twin_star d).neighborFinset (Sum.inr i)).card = 1 at h
  omega

open Classical in
/-- The twin-star graph TS_d has exactly 2d - 2 leaves for d ≥ 2. -/
theorem twin_star_leaf_count (d : ℕ) (hd : 2 ≤ d) :
    graph_leaf_count (twin_star d) = 2 * d - 2 := by
  change (Finset.univ.filter (fun v => (twin_star d).degree v = 1)).card = 2 * d - 2
  have h_iff : ∀ v : Fin d ⊕ Fin d,
      ((twin_star d).degree v = 1) ↔ (match v with | .inl i => i.val ≠ 0 | .inr i => i.val ≠ 0) := by
    intro v
    rcases v with i | i
    · dsimp only
      by_cases hi : i.val = 0
      · have hdeg := twin_star_leaf_count_deg_inl_zero d hd i hi
        simp [hi, hdeg]
      · simp [hi]
        have hnf := twin_star_leaf_count_nf_inl d hd i hi
        change ((twin_star d).neighborFinset (Sum.inl i)).card = 1
        rw [hnf, Finset.card_singleton]
    · dsimp only
      by_cases hi : i.val = 0
      · have hdeg := twin_star_leaf_count_deg_inr_zero d hd i hi
        simp [hi, hdeg]
      · simp [hi]
        have hnf := twin_star_leaf_count_nf_inr d hd i hi
        change ((twin_star d).neighborFinset (Sum.inr i)).card = 1
        rw [hnf, Finset.card_singleton]
  have h_filter : Finset.univ.filter (fun v => (twin_star d).degree v = 1) =
      Finset.univ.filter (fun v => match v with | .inl i => i.val ≠ 0 | .inr i => i.val ≠ 0) :=
    Finset.filter_congr (fun v _ => h_iff v)
  rw [h_filter]
  have h_disj : (Finset.univ.filter (fun (v : Fin d ⊕ Fin d) =>
        match v with | .inl i => i.val ≠ 0 | .inr i => i.val ≠ 0)) =
      ((Finset.univ.filter (fun (i : Fin d) => i.val ≠ 0)).disjSum
       (Finset.univ.filter (fun (i : Fin d) => i.val ≠ 0))) := by
    change (Finset.disjSum Finset.univ Finset.univ).filter
      (fun (v : Fin d ⊕ Fin d) => match v with | .inl i => i.val ≠ 0 | .inr i => i.val ≠ 0) = _
    ext (x | y) <;> simp
  rw [h_disj, Finset.card_disjSum]
  have h_add := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
    (p := fun (i : Fin d) => i.val ≠ 0)
  have h_not : (Finset.univ.filter (fun (i : Fin d) => ¬(i.val ≠ 0))) = {⟨0, by omega⟩} := by
    ext ⟨x, hx⟩
    simp [Fin.ext_iff]
  rw [h_not, Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h_add
  omega
