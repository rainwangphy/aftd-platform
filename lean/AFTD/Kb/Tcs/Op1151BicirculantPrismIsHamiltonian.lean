import AFTD.Prelude

/-!
# op_1151_bicirculant_prism_is_hamiltonian

Topic: graphs   Node: 0f8b3d08991e

Provenance: formalization of a published result. Source: arXiv:2611.05531 Sec. 1

The triangular prism bicirculant graph B(3; {1, -1}, {0}, {1, -1}) on vertex set (Fin 2) × (ZMod 3) is Hamiltonian.
-/

/-- The triangular prism bicirculant graph B(3; {1, -1}, {0}, {1, -1}) on vertex set (Fin 2) × (ZMod 3) is Hamiltonian. -/
theorem op_1151_bicirculant_prism_is_hamiltonian :
    (SimpleGraph.fromRel fun (u v : Fin 2 × ZMod 3) =>
      (u.1 = 0 ∧ v.1 = 0 ∧ v.2 - u.2 ∈ ({1, -1} : Finset (ZMod 3))) ∨
      (u.1 = 1 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({1, -1} : Finset (ZMod 3))) ∨
      (u.1 = 0 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({0} : Finset (ZMod 3)))).IsHamiltonian := by
  let G : SimpleGraph (Fin 2 × ZMod 3) := SimpleGraph.fromRel fun (u v : Fin 2 × ZMod 3) =>
      (u.1 = 0 ∧ v.1 = 0 ∧ v.2 - u.2 ∈ ({1, -1} : Finset (ZMod 3))) ∨
      (u.1 = 1 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({1, -1} : Finset (ZMod 3))) ∨
      (u.1 = 0 ∧ v.1 = 1 ∧ v.2 - u.2 ∈ ({0} : Finset (ZMod 3)))
  change G.IsHamiltonian
  let v0 : Fin 2 × ZMod 3 := (0, 0)
  let v1 : Fin 2 × ZMod 3 := (0, 1)
  let v2 : Fin 2 × ZMod 3 := (0, 2)
  let v3 : Fin 2 × ZMod 3 := (1, 2)
  let v4 : Fin 2 × ZMod 3 := (1, 1)
  let v5 : Fin 2 × ZMod 3 := (1, 0)
  let h01 : G.Adj v0 v1 := by decide
  let h12 : G.Adj v1 v2 := by decide
  let h23 : G.Adj v2 v3 := by decide
  let h34 : G.Adj v3 v4 := by decide
  let h45 : G.Adj v4 v5 := by decide
  let h50 : G.Adj v5 v0 := by decide
  let p : G.Walk v0 v0 :=
    SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h23
      (SimpleGraph.Walk.cons h34 (SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h50 SimpleGraph.Walk.nil)))))
  have h_trail : p.IsTrail := SimpleGraph.Walk.IsTrail.mk (by decide : p.edges.Nodup)
  have h_circuit : p.IsCircuit := SimpleGraph.Walk.IsCircuit.mk h_trail (by decide : p ≠ SimpleGraph.Walk.nil)
  have h_cycle : p.IsCycle := SimpleGraph.Walk.IsCycle.mk h_circuit (by decide : p.support.tail.Nodup)
  have h_ham : p.tail.IsHamiltonian := by
    rw [SimpleGraph.Walk.IsHamiltonian]
    decide
  have hp : p.IsHamiltonianCycle := SimpleGraph.Walk.IsHamiltonianCycle.mk h_cycle h_ham
  intro h
  exact ⟨v0, p, hp⟩
