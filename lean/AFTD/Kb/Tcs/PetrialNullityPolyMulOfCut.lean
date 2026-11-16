import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialNullityPolyCoeffEqPetrialCoeff
import AFTD.Kb.Tcs.PetrialBlockDiagonalRank
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_nullity_poly_mul_of_cut

Topic: combinatorics   Node: 58085656a7c6

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

If no edge of G joins a vertex of s to a vertex outside s, then the nullity generating polynomial of G is the product of the nullity generating polynomials of the induced subgraphs on s and on its complement.
-/

open Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Op1239Cut

noncomputable def cutLeft {V : Type*} [Fintype V] [DecidableEq V]
    (s : Set V) [DecidablePred (· ∈ s)] (F : Finset V) : Finset s :=
  Finset.univ.filter (fun x => x.1 ∈ F)
noncomputable def cutRight {V : Type*} [Fintype V] [DecidableEq V]
    (s : Set V) [DecidablePred (· ∈ s)] (F : Finset V) : Finset (sᶜ : Set V) :=
  Finset.univ.filter (fun x => x.1 ∈ F)

theorem petrial_cut_rank {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (hcut : ∀ a b : V, a ∈ s → b ∉ s → ¬ G.Adj a b) (F : Finset V) :
    (petrial_matrix G F).rank =
      (petrial_matrix (G.induce s) (cutLeft s F)).rank +
      (petrial_matrix (G.induce sᶜ) (cutRight s F)).rank := by
  classical
  let e := Equiv.Set.sumCompl s
  let M := (petrial_matrix G F).submatrix e e
  have hM : M = Matrix.fromBlocks (petrial_matrix (G.induce s) (cutLeft s F)) 0 0
      (petrial_matrix (G.induce sᶜ) (cutRight s F)) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (petrial_matrix G F) i.1 j.1 = (petrial_matrix (G.induce s) (cutLeft s F)) i j
        simp [petrial_matrix, cutLeft, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Subtype.ext_iff]
      | inr j =>
        change (petrial_matrix G F) i.1 j.1 = 0
        have hn : ¬G.Adj i.1 j.1 := hcut i.1 j.1 i.2 j.2
        have hne : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
        simp [petrial_matrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, hn, hne]
    | inr i =>
      cases j with
      | inl j =>
        change (petrial_matrix G F) i.1 j.1 = 0
        have hn : ¬G.Adj i.1 j.1 := fun h => hcut j.1 i.1 j.2 i.2 h.symm
        have hne : i.1 ≠ j.1 := fun h => i.2 (h.symm ▸ j.2)
        simp [petrial_matrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, hn, hne]
      | inr j =>
        change (petrial_matrix G F) i.1 j.1 = (petrial_matrix (G.induce sᶜ) (cutRight s F)) i j
        simp [petrial_matrix, cutRight, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Subtype.ext_iff]
  rw [← Matrix.rank_submatrix (petrial_matrix G F) e e, ← show M.rank = _ from rfl, hM,
    petrial_block_diagonal_rank]

noncomputable def cutEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (s : Set V) [DecidablePred (· ∈ s)] : Finset V ≃ Finset s × Finset (sᶜ : Set V) where
  toFun F := (cutLeft s F, cutRight s F)
  invFun p := p.1.image Subtype.val ∪ p.2.image Subtype.val
  left_inv F := by
    ext x
    by_cases hx : x ∈ s
    · simp [cutLeft, cutRight, hx]
    · simp [cutLeft, cutRight, hx]
  right_inv p := by
    rcases p with ⟨a,b⟩
    apply Prod.ext
    · ext x
      have hx : (x : V) ∈ s := x.property
      simp [cutLeft, cutRight, hx]
    · ext x
      have hx : (x : V) ∉ s := x.property
      simp [cutLeft, cutRight, hx]

end Op1239Cut
open Op1239Cut

/-- The nullity polynomial is multiplicative over a vertex cut with no crossing edges: it is the product of the polynomials of the two induced subgraphs. -/
theorem petrial_nullity_poly_mul_of_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)]
    (hcut : ∀ a b : V, a ∈ s → b ∉ s → ¬ G.Adj a b) :
    petrial_nullity_poly G
      = petrial_nullity_poly (G.induce s) * petrial_nullity_poly (G.induce sᶜ) := by
  classical
  have hc : Fintype.card V = Fintype.card s + Fintype.card (sᶜ : Set V) := by
    simpa using (Fintype.card_congr (Equiv.Set.sumCompl s)).symm
  unfold petrial_nullity_poly
  calc
    (∑ F : Finset V, (Polynomial.X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix G F).rank)) =
      ∑ p : Finset s × Finset (sᶜ : Set V),
        ((Polynomial.X : Polynomial ℕ) ^ (Fintype.card s - (petrial_matrix (G.induce s) p.1).rank)) *
        ((Polynomial.X : Polynomial ℕ) ^ (Fintype.card (sᶜ : Set V) - (petrial_matrix (G.induce sᶜ) p.2).rank)) := by
          apply Fintype.sum_equiv (cutEquiv s)
          intro F
          change (Polynomial.X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix G F).rank) =
            ((Polynomial.X : Polynomial ℕ) ^ (Fintype.card s - (petrial_matrix (G.induce s) (cutLeft s F)).rank)) *
            ((Polynomial.X : Polynomial ℕ) ^ (Fintype.card (sᶜ : Set V) - (petrial_matrix (G.induce sᶜ) (cutRight s F)).rank))
          rw [← pow_add, petrial_cut_rank G s hcut F, hc]
          congr 1
          have h1 := (petrial_matrix (G.induce s) (cutLeft s F)).rank_le_card_width
          have h2 := (petrial_matrix (G.induce sᶜ) (cutRight s F)).rank_le_card_width
          omega
    _ = (∑ F : Finset s, (Polynomial.X : Polynomial ℕ) ^ (Fintype.card s - (petrial_matrix (G.induce s) F).rank)) *
        (∑ F : Finset (sᶜ : Set V), (Polynomial.X : Polynomial ℕ) ^ (Fintype.card (sᶜ : Set V) - (petrial_matrix (G.induce sᶜ) F).rank)) := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
