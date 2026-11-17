import AFTD.Prelude
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_block_postdegree_le_target_union

Topic: online_algorithms   Node: 230667f7339e

Provenance: helper lemma. Offline size and post-degree accounting in arXiv:2610.41516 Lemma 2.5.

If every later neighbor is in the vertex’s block or in its block’s one target-owner group, and those two groups have bounded sizes, then its post-degree is bounded by the sum of their sizes.
-/

/-- Post-degree control from one target owner per block. -/
theorem op869_block_postdegree_le_target_union {n : ℕ} {V B : Type} [DecidableEq V] [DecidableEq B]
    (P : Fin n → Finset (Fin n)) (block : Fin n → B) (owner : B → V)
    (target : B → Option V) (blockBound ownerBound : ℕ)
    (hblock : ∀ b, (Finset.univ.filter (fun x => block x = b)).card ≤ blockBound)
    (howner : ∀ v, (Finset.univ.filter (fun x => owner (block x) = v)).card ≤ ownerBound)
    (hedge : ∀ x y, x < y → x ∈ P y →
      block y = block x ∨ target (block x) = some (owner (block y))) :
    ∀ x, op869_predecessor_postdegree P x ≤ blockBound + ownerBound := by
  classical
  intro x
  let A := Finset.univ.filter (fun y : Fin n => block y = block x)
  let T := Finset.univ.filter (fun y : Fin n => target (block x) = some (owner (block y)))
  have hA : A.card ≤ blockBound := hblock (block x)
  have hT : T.card ≤ ownerBound := by
    cases ht : target (block x) with
    | none => simp [T, ht]
    | some v => simpa [T, ht, eq_comm] using howner v
  have hsub : (Finset.univ.filter (fun y : Fin n => x < y ∧ x ∈ P y)) ⊆ A ∪ T := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hedge x y hy.1 hy.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  calc
    op869_predecessor_postdegree P x ≤ (A ∪ T).card := Finset.card_le_card hsub
    _ ≤ A.card + T.card := Finset.card_union_le _ _
    _ ≤ blockBound + ownerBound := Nat.add_le_add hA hT
