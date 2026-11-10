import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_exists_support_maximum_triangle_packing

Topic: graphs   Node: a6cbdd0a8420

Provenance: helper lemma. Finite support-maximal selection used in the general pair-stable forced-K4 reduction; no novelty claim.

Every finite graph has a maximum triangle packing whose vertex support has maximum cardinality among all maximum triangle packings.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem simple_graph_exists_support_maximum_triangle_packing (n : ℕ) (G : SimpleGraph (Fin n)) : ∃ P : Finset (Finset (Fin n)), (∀ t ∈ P, G.IsNClique 3 t) ∧ (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧ P.card = simple_graph_triangle_packing_number G ∧ ∀ Q : Finset (Finset (Fin n)), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → (Q.biUnion id).card ≤ (P.biUnion id).card := by
  classical
  let A : Set ℕ := {k | ∃ P : Finset (Finset (Fin n)),
    (∀ t ∈ P, G.IsNClique 3 t) ∧
    (P : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ P.card = k}
  have hne : A.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hbdd : BddAbove A := by
    refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro k ⟨P, _, _, rfl⟩
    exact Finset.card_le_univ P
  obtain ⟨P₀,h₀tri,h₀pair,h₀card⟩ := Nat.sSup_mem hne hbdd
  have h₀max : P₀.card = simple_graph_triangle_packing_number G := by
    change P₀.card = simple_graph_triangle_packing_number G at h₀card
    exact h₀card
  let F : Finset (Finset (Finset (Fin n))) := Finset.univ.filter (fun P =>
    (∀ t ∈ P, G.IsNClique 3 t) ∧
    (P : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧
    P.card = simple_graph_triangle_packing_number G)
  have hF : F.Nonempty := by
    refine ⟨P₀, ?_⟩
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h₀tri,h₀pair,h₀max⟩
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image F (fun P => (P.biUnion id).card) hF
  have hP' : (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧
      P.card = simple_graph_triangle_packing_number G := by
    simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and] using hP
  refine ⟨P,hP'.1,hP'.2.1,hP'.2.2, ?_⟩
  intro Q hQtri hQpair hQcard
  apply hmax Q
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hQtri,hQpair,hQcard.trans hP'.2.2⟩
