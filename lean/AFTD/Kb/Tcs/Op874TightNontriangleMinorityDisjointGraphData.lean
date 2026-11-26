import AFTD.Prelude

/-!
# op874_tight_nontriangle_minority_disjoint_graph_data

Topic: graphs   Node: 2cd8cba746d7

Provenance: helper lemma. Nontriangle minority-palette obstruction for OP-874; https://arxiv.org/abs/2610.41950.

The graph is simple cubic with Hamiltonian factor, a 1:2 locally maximal matching-constant cut, and no triangle containing either minority matching edge.
-/

theorem op874_tight_nontriangle_minority_disjoint_graph_data :
    let E : Finset (Sym2 (Fin 12)) := {s((0 : Fin 12),5),s(0,11),s(0,1),s(1,6),s(1,9),s(2,10),s(2,9),s(2,3),s(3,7),s(3,5),s(4,6),s(4,11),s(4,5),s(6,7),s(7,8),s(8,10),s(8,9),s(10,11)}
    let M : Finset (Sym2 (Fin 12)) := {s((0 : Fin 12),1),s(2,3),s(4,5),s(6,7),s(8,9),s(10,11)}
    let bit : Fin 12 → Bool := ![false,false,false,false,true,true,true,true,true,true,true,true]
    let P : Fin 12 → Fin 12 := ![0,5,3,7,8,10,2,9,1,6,4,11]
    let F : Finset (Sym2 (Fin 12)) := Finset.univ.image (fun i : Fin 12 => s(P i,P (i+1)))
    let same : Fin 12 → ℕ := fun v => (F.filter fun edge =>
      ∃ z : Fin 12, edge = s(v,z) ∧ bit v = bit z).card
    (∀ edge ∈ E, ¬ edge.IsDiag) ∧ (∀ v : Fin 12, (E.filter fun edge => v ∈ edge).card = 3) ∧
    Function.Injective P ∧ M ⊆ E ∧
    (∀ v : Fin 12, (M.filter fun edge => v ∈ edge).card = 1) ∧
    E = F ∪ M ∧ Disjoint F M ∧
    (∀ u v : Fin 12, s(u,v) ∈ M → bit u = bit v ∧ same u + same v = if bit u then 2 else 0) ∧
    (∀ u v z : Fin 12, s(u,v) ∈ M → bit u = false → s(u,z) ∈ E → s(v,z) ∉ E) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
