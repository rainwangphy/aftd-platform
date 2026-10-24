import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateSuccStep
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState

/-!
# picking_prefix_state_card_diff_step_of_ne

Topic: fair_division   Node: 0cafebbe0035

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

Suppose two runs of a picking sequence (differing only in agent i's ranking) have allocated sets at time s that differ in at most one element each way, and that turn s is taken by an agent a other than i. Then after turn s+1 the allocated sets again differ in at most one element each way.
-/

theorem picking_prefix_state_card_diff_step_of_ne_aux {G : Type*} [DecidableEq G]
    (A B : Finset G) (p q : G) (hpA : p ∉ A) (hpB : p ∈ B)
    (h1 : (A \ B).card ≤ 1) (h2 : (B \ A).card ≤ 1) :
    (insert p A \ insert q B).card ≤ 1 ∧ (insert q B \ insert p A).card ≤ 1 := by
  constructor
  · refine le_trans (Finset.card_le_card ?_) h1
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hz ⊢
    rcases hz with ⟨rfl | hzA, hzq, hzB⟩
    · exact absurd hpB hzB
    · exact ⟨hzA, hzB⟩
  · have hsub : insert q B \ insert p A ⊆ {q} := by
      intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hz
      rcases hz with ⟨rfl | hzB, hzp, hzA⟩
      · exact Finset.mem_singleton_self _
      · exfalso
        have hz' : z ∈ B \ A := Finset.mem_sdiff.mpr ⟨hzB, hzA⟩
        have hp' : p ∈ B \ A := Finset.mem_sdiff.mpr ⟨hpB, hpA⟩
        exact hzp (Finset.card_le_one.mp h2 z hz' p hp')
    exact (Finset.card_le_card hsub).trans (by simp)

/-- One turn whose active agent is not the deviator preserves the invariant that the two allocated sets differ in at most one element on each side. -/
theorem picking_prefix_state_card_diff_step_of_ne {N G : Type*} [DecidableEq N] [DecidableEq G] [Fintype G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G)
    (s : ℕ) (hseq : seq.length ≤ m) (hsl : s < seq.length) (hsm : s < m)
    (a : N) (ha : seq[s]? = some a) (hne : a ≠ i)
    (h1 : ((picking_prefix_state seq (Function.update rank i r) s).2 \
        (picking_prefix_state seq rank s).2).card ≤ 1)
    (h2 : ((picking_prefix_state seq rank s).2 \
        (picking_prefix_state seq (Function.update rank i r) s).2).card ≤ 1) :
    ((picking_prefix_state seq (Function.update rank i r) (s + 1)).2 \
        (picking_prefix_state seq rank (s + 1)).2).card ≤ 1 ∧
      ((picking_prefix_state seq rank (s + 1)).2 \
        (picking_prefix_state seq (Function.update rank i r) (s + 1)).2).card ≤ 1 := by
  obtain ⟨p, hpA, hA', -, -, k, hk, hbk⟩ :=
    picking_prefix_state_succ_step seq (Function.update rank i r) s hsl hsm a ha
  obtain ⟨q, hqB, hB', -, -, k', hk', hbk'⟩ := picking_prefix_state_succ_step seq rank s hsl hsm a ha
  rw [Function.update_of_ne hne] at hk hbk
  rw [hA', hB']
  set A := (picking_prefix_state seq (Function.update rank i r) s).2
  set B := (picking_prefix_state seq rank s).2
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have hpB : p ∈ B := by rw [← hk]; exact hbk' k hlt
    exact picking_prefix_state_card_diff_step_of_ne_aux A B p q hpA hpB h1 h2
  · have hpq : p = q := by rw [← hk, ← hk', heq]
    subst hpq
    constructor
    · refine le_trans (Finset.card_le_card ?_) h1
      intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hz ⊢
      rcases hz with ⟨rfl | hzA, hzq, hzB⟩
      · exact absurd rfl hzq
      · exact ⟨hzA, hzB⟩
    · refine le_trans (Finset.card_le_card ?_) h2
      intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hz ⊢
      rcases hz with ⟨rfl | hzB, hzq, hzA⟩
      · exact absurd rfl hzq
      · exact ⟨hzB, hzA⟩
  · have hqA : q ∈ A := by rw [← hk']; exact hbk k' hgt
    obtain ⟨c1, c2⟩ := picking_prefix_state_card_diff_step_of_ne_aux B A q p hqB hqA h2 h1
    exact ⟨c2, c1⟩
