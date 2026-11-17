import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BlockPostdegreeLeTargetUnion
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_block_postdegree_from_block_counts

Topic: online_algorithms   Node: 31f7ea09d10d

Provenance: helper lemma. Offline size and post-degree accounting in arXiv:2610.41516 Lemma 2.5.

If each block has at most B vertices, each owner has at most R blocks, and every later cross-edge points from a block to its one target owner, then every vertex has post-degree at most B+RB.
-/

/-- The block-count post-degree bound used by the fold simulation. -/
theorem op869_block_postdegree_from_block_counts {n : ℕ} {V B : Type} [Fintype B] [DecidableEq V] [DecidableEq B]
    (P : Fin n → Finset (Fin n)) (block : Fin n → B) (owner : B → V)
    (target : B → Option V) (blockBound blocksPerOwner : ℕ)
    (hblock : ∀ b, (Finset.univ.filter (fun x => block x = b)).card ≤ blockBound)
    (howners : ∀ v, (Finset.univ.filter (fun b => owner b = v)).card ≤ blocksPerOwner)
    (hedge : ∀ x y, x < y → x ∈ P y →
      block y = block x ∨ target (block x) = some (owner (block y))) :
    ∀ x, op869_predecessor_postdegree P x ≤ blockBound + blocksPerOwner * blockBound := by
  classical
  apply op869_block_postdegree_le_target_union P block owner target blockBound (blocksPerOwner * blockBound) hblock
  · intro v
    let S := Finset.univ.filter (fun b : B => owner b = v)
    let F := fun b : B => Finset.univ.filter (fun x : Fin n => block x = b)
    have hsub : (Finset.univ.filter (fun x : Fin n => owner (block x) = v)) ⊆ S.biUnion F := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_biUnion.mpr ⟨block x, by simp [S, hx], by simp [F]⟩
    calc
      (Finset.univ.filter (fun x : Fin n => owner (block x) = v)).card ≤ (S.biUnion F).card := Finset.card_le_card hsub
      _ ≤ S.card * blockBound := Finset.card_biUnion_le_card_mul S F blockBound (fun b hb => hblock b)
      _ ≤ blocksPerOwner * blockBound := Nat.mul_le_mul_right _ (howners v)
  · exact hedge
