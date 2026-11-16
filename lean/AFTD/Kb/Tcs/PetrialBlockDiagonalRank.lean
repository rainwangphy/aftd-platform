import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialRankSchurInvertible

/-!
# petrial_block_diagonal_rank

Topic: combinatorics   Node: 7b404ba95916

Provenance: helper lemma. Matrix-rank helper for the disjoint-cut product in OP-1239.

Over a field, the rank of a block diagonal matrix with square finite blocks A and D equals the sum of the ranks of A and D.
-/

open Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_block_diagonal_rank {K m n : Type*} [Field K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (D : Matrix n n K) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  classical
  let e : LinearMap.ker (Matrix.mulVecLin (Matrix.fromBlocks A 0 0 D)) ≃ₗ[K]
      (LinearMap.ker A.mulVecLin × LinearMap.ker D.mulVecLin) := {
    toFun := fun x => (⟨fun i => x.1 (Sum.inl i), by
      have hx := x.2
      change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) x.1 = 0 at hx
      change A.mulVec (fun i => x.1 (Sum.inl i)) = 0
      funext i
      have hi := congrFun hx (Sum.inl i)
      simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using hi⟩,
      ⟨fun i => x.1 (Sum.inr i), by
      have hx := x.2
      change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) x.1 = 0 at hx
      change D.mulVec (fun i => x.1 (Sum.inr i)) = 0
      funext i
      have hi := congrFun hx (Sum.inr i)
      simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using hi⟩)
    invFun := fun p => ⟨Sum.elim p.1.1 p.2.1, by
      have hA := p.1.2
      have hD := p.2.2
      change A.mulVec p.1.1 = 0 at hA
      change D.mulVec p.2.1 = 0 at hD
      change Matrix.mulVec (Matrix.fromBlocks A 0 0 D) (Sum.elim p.1.1 p.2.1) = 0
      funext i
      cases i with
      | inl i => simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using congrFun hA i
      | inr i => simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using congrFun hD i⟩
    left_inv := fun x => by
      apply Subtype.ext
      funext i
      cases i <;> rfl
    right_inv := fun p => by
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    map_add' := fun x y => by
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    map_smul' := fun c x => by
      apply Prod.ext <;> apply Subtype.ext <;> rfl
  }
  have he : Module.finrank K (LinearMap.ker (Matrix.mulVecLin (Matrix.fromBlocks A 0 0 D))) =
      Module.finrank K (LinearMap.ker A.mulVecLin) + Module.finrank K (LinearMap.ker D.mulVecLin) := by
    simpa using e.finrank_eq
  have h := (Matrix.mulVecLin (Matrix.fromBlocks A 0 0 D)).finrank_range_add_finrank_ker
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hD := D.mulVecLin.finrank_range_add_finrank_ker
  change (Matrix.fromBlocks A 0 0 D).rank + _ = _ at h
  change A.rank + _ = _ at hA
  change D.rank + _ = _ at hD
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h hA hD
  omega
