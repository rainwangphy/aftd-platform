import AFTD.Prelude
import AFTD.Kb.Tcs.IsBraidSolution
import AFTD.Kb.Tcs.PosetEdgeBraidMap

/-!
# poset_edge_braid_map_is_braid_solution

Topic: combinatorics   Node: e8abdfbcb2d4

Provenance: formalization of a published result. Source: arXiv:2611.15540, Theorem 3.3

For any partially ordered set P with decidable equality, poset_edge_braid_map satisfies the braid equation.
-/

private def poset_edge_braid_map_is_braid_solution_t {P : Type*} [PartialOrder P] [DecidableEq P]
    (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) : P × ZMod 2 :=
  if z = ((l : P × P).1, 0) then ((l : P × P).2, 1)
  else if z = ((l : P × P).2, 1) then ((l : P × P).1, 0) else z

private lemma poset_edge_braid_map_is_braid_solution_t_invol {P : Type*} [PartialOrder P] [DecidableEq P]
    (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) :
    poset_edge_braid_map_is_braid_solution_t l (poset_edge_braid_map_is_braid_solution_t l z) = z := by
  unfold poset_edge_braid_map_is_braid_solution_t
  split_ifs with h1 h2 h3 h4 h5 h6 <;> subst_vars <;> simp_all

private lemma poset_edge_braid_map_is_braid_solution_R_ii {P : Type*} [PartialOrder P] [DecidableEq P]
    (l l' : {p : P × P // p.1 ≤ p.2}) :
    poset_edge_braid_map (Sum.inl l, Sum.inl l') = (Sum.inl l, Sum.inl l') := rfl

private lemma poset_edge_braid_map_is_braid_solution_R_vv {P : Type*} [PartialOrder P] [DecidableEq P]
    (z z' : P × ZMod 2) :
    poset_edge_braid_map (Sum.inr z, Sum.inr z') = (Sum.inr z, Sum.inr z') := rfl

private lemma poset_edge_braid_map_is_braid_solution_R_iv {P : Type*} [PartialOrder P] [DecidableEq P]
    (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) :
    poset_edge_braid_map (Sum.inl l, Sum.inr z)
      = (Sum.inr (poset_edge_braid_map_is_braid_solution_t l z), Sum.inl l) := rfl

private lemma poset_edge_braid_map_is_braid_solution_R_vi {P : Type*} [PartialOrder P] [DecidableEq P]
    (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) :
    poset_edge_braid_map (Sum.inr z, Sum.inl l)
      = (Sum.inl l, Sum.inr (poset_edge_braid_map_is_braid_solution_t l z)) := rfl

/-- The poset bipartite map E_P is a solution of the braid equation. -/
theorem poset_edge_braid_map_is_braid_solution {P : Type*} [PartialOrder P] [DecidableEq P] :
    is_braid_solution (@poset_edge_braid_map P _ _) := by
  unfold is_braid_solution
  funext x
  obtain ⟨a, b, c⟩ := x
  rcases a with l1 | z1 <;> rcases b with l2 | z2 <;> rcases c with l3 | z3 <;>
    simp only [Function.comp_apply,
      poset_edge_braid_map_is_braid_solution_R_ii,
      poset_edge_braid_map_is_braid_solution_R_vv,
      poset_edge_braid_map_is_braid_solution_R_iv,
      poset_edge_braid_map_is_braid_solution_R_vi,
      poset_edge_braid_map_is_braid_solution_t_invol]
