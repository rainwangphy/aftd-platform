import AFTD.Prelude

/-!
# is_kst_code

Topic: combinatorics   Node: 2d9d1bd058aa

Provenance: formalization of a published result. Source: arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Section 1

A family C of simple graphs on vertex set [n] is a K_{s,t}-code if for every two distinct graphs G, G' in C and every pair of disjoint subsets A, B of [n] with |A| = s and |B| = t, the symmetric difference of G and G' is not the complete bipartite graph between A and B.
-/

/-- A family of graphs on Fin n is a K_{s,t}-code if the symmetric difference of any two distinct members is not a complete bipartite graph with parts of sizes s and t. -/
def is_kst_code (s t n : ℕ) (C : Set (SimpleGraph (Fin n))) : Prop := ∀ ⦃G G' : SimpleGraph (Fin n)⦄, G ∈ C → G' ∈ C → G ≠ G' →
    ∀ (A B : Finset (Fin n)), Disjoint A B → A.card = s → B.card = t →
      symmDiff G G' ≠ (⊤ : SimpleGraph (Fin n)).between (A : Set (Fin n)) (B : Set (Fin n))
