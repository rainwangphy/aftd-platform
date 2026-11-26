import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel

/-!
# op309_three_dense_hosts_block_overlap_peeling

Topic: graphs   Node: 3cb5a62a3d80

Provenance: helper lemma. OP-309 girth-seven fixed-forest obstruction, experiment 40461.

A nonempty class set is unpeelable when each of its classes meets at least three hosts that each contain at least three classes from the set.
-/

theorem op309_three_dense_hosts_block_overlap_peeling
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) (hS : S.Nonempty)
    (hclass : ∀ a ∈ S, 3 ≤ (Finset.univ.filter (fun b : B =>
      I.Adj (.inl a) (.inr b) ∧ 3 ≤ (S.filter fun a' => I.Adj (.inl a') (.inr b)).card)).card) :
    ¬ op309_incidence_overlap_five_peel I := by
  classical
  intro hpeel
  obtain ⟨a,ha,_,hw⟩ := hpeel S hS
  let T : Finset B := Finset.univ.filter (fun b : B =>
    I.Adj (.inl a) (.inr b) ∧ 3 ≤ (S.filter fun a' => I.Adj (.inl a') (.inr b)).card)
  let score : B → ℕ := fun b => if I.Adj (.inl a) (.inr b) then
    (S.filter fun a' => I.Adj (.inl a') (.inr b)).card - 1 else 0
  have hterm : ∀ b ∈ T, 2 ≤ score b := by
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    simp only [score, hb'.1, if_true]
    omega
  have hsum : (∑ b ∈ T, 2) ≤ ∑ b ∈ T, score b := by
    exact Finset.sum_le_sum hterm
  have hle : (∑ b ∈ T, score b) ≤ ∑ b : B, score b :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hcard : 3 ≤ T.card := hclass a ha
  have hsum' : 2 * T.card ≤ ∑ b ∈ T, score b := by
    simpa [Nat.mul_comm] using hsum
  change (∑ b : B, score b) ≤ 5 at hw
  omega
