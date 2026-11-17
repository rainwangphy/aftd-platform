import AFTD.Prelude
import AFTD.Kb.Tcs.Op869PredecessorPostdegree
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869MemExtendPredecessors

/-!
# op869_extend_postdegree

Topic: online_algorithms   Node: 45842f1d709d

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

An original vertex has the same post-degree after padding.
-/

/-- An original vertex has the same post-degree after padding. -/
theorem op869_extend_postdegree {n m : ℕ} (h : n ≤ m) (P : Fin n → Finset (Fin n)) (a : Fin n) :
    op869_predecessor_postdegree (op869_extend_predecessors h P) (Fin.castLE h a) =
      op869_predecessor_postdegree P a := by
  classical
  have hset : (Finset.univ.filter (fun y : Fin m => Fin.castLE h a < y ∧
      Fin.castLE h a ∈ op869_extend_predecessors h P y)) =
      (Finset.univ.filter (fun y : Fin n => a < y ∧ a ∈ P y)).map (Fin.castLEEmb h) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨hay, hmem⟩
      obtain ⟨a', b, ha, hb, hab⟩ := (op869_mem_extend_predecessors h P (Fin.castLE h a) y).mp hmem
      have haa : a' = a := Fin.castLE_injective h ha
      subst a'
      refine ⟨b, ⟨?_, hab⟩, hb⟩
      rw [← hb] at hay
      exact hay
    · rintro ⟨b, ⟨hab, hmem⟩, rfl⟩
      exact ⟨hab, (op869_mem_extend_predecessors h P _ _).mpr ⟨a, b, rfl, rfl, hmem⟩⟩
  unfold op869_predecessor_postdegree
  rw [hset, Finset.card_map]
