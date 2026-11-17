import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869ExtendColors
import AFTD.Kb.Tcs.Op869GraphExtendPredecessors
import AFTD.Kb.Tcs.Op869ExtendPostdegreeBound
import AFTD.Kb.Tcs.Op869ExtendColorPrefix
import AFTD.Kb.Tcs.Op869ExtendPredecessorsUpdate
import AFTD.Kb.Tcs.Op869ExtendColorsUpdate
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_vertex_padding

Topic: online_algorithms   Node: ce4d8814a42d

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

For a positive colorability bound, a bounded adversary winning position remains winning after padding its entire graph and color history to a larger vertex universe.
-/

/-- For a positive colorability bound, a bounded adversary winning position remains winning after padding its entire graph and color history to a larger vertex universe. -/
theorem op869_bounded_vertex_padding {n m : ℕ} (hnm : n ≤ m) (k t K D : ℕ) (hk : 1 ≤ k)
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (hwin : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k t K D fuel i
      (op869_extend_predecessors hnm P) (op869_extend_colors hnm C) := by
  classical
  induction fuel generalizing i P C with
  | zero => simp [op869_bounded_adversary_forces] at hwin
  | succ fuel ih =>
    by_cases hi : i < n
    · have him : i < m := lt_of_lt_of_le hi hnm
      simp only [op869_bounded_adversary_forces, dif_pos hi] at hwin
      simp only [op869_bounded_adversary_forces, dif_pos him]
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := hwin
      have hv : Fin.castLE hnm (⟨i, hi⟩ : Fin n) = (⟨i, him⟩ : Fin m) := by ext; rfl
      have hupdateP : Function.update (op869_extend_predecessors hnm P) (⟨i, him⟩ : Fin m)
          (S.map (Fin.castLEEmb hnm)) =
          op869_extend_predecessors hnm (Function.update P (⟨i, hi⟩ : Fin n) S) := by
        rw [← hv, ← op869_extend_predecessors_update]
      have hupdateC (c : Finset ℕ) : Function.update (op869_extend_colors hnm C)
          (⟨i, him⟩ : Fin m) c =
          op869_extend_colors hnm (Function.update C (⟨i, hi⟩ : Fin n) c) := by
        rw [← hv, ← op869_extend_colors_update]
      refine ⟨S.map (Fin.castLEEmb hnm), ?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
        exact hS b hb
      · rw [hupdateP, op869_graph_extend_predecessors]
        letI : NeZero k := ⟨by omega⟩
        exact hcolor.map (Fin.castLEEmb hnm)
      · rw [hupdateP]
        exact op869_extend_postdegree_bound hnm _ D hdegree
      · intro c hc hvalid
        have hvalidOld : ∀ a ∈ S, Disjoint (C a) c := by
          intro a ha
          have h := hvalid (Fin.castLE hnm a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
          simpa [op869_extend_colors, a.isLt] using h
        rcases hnext c hc hvalidOld with hsuccess | hrec
        · left
          rw [hupdateC, op869_extend_color_prefix hnm _ i hi]
          exact hsuccess
        · right
          rw [hupdateP, hupdateC]
          exact ih (i + 1) _ _ hrec
    · simp [op869_bounded_adversary_forces, hi] at hwin
