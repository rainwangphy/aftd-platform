import AFTD.Prelude

/-!
# op1370_split_biintersecting_shatterer_shadow_counterexample

Topic: combinatorics   Node: b7215abe57bc

Provenance: helper lemma. A counterexample to a witness-shadow coverage shortcut toward OP-1370, arXiv:2611.12199 Conjecture 4.3.

There are nonempty strongly cross-incomparable families F and G of subsets of Fin 6 whose union is both intersecting and co-intersecting and is nonconstant in every coordinate, together with a set R shattered by F∪G, such that R is not simultaneously contained in a member of F∪G and disjoint from a member of G, and R is not simultaneously disjoint from a member of F∪G and contained in a member of F.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem op1370_split_biintersecting_shatterer_shadow_counterexample : ∃ F G : Finset (Finset (Fin 6)), ∃ R : Finset (Fin 6), F.Nonempty ∧ G.Nonempty ∧ (∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A) ∧ (∀ A ∈ F ∪ G, ∀ B ∈ F ∪ G, (A ∩ B).Nonempty ∧ A ∪ B ≠ Finset.univ) ∧ (∀ x : Fin 6, (∃ A ∈ F ∪ G, x ∈ A) ∧ (∃ B ∈ F ∪ G, x ∉ B)) ∧ R ∈ (F ∪ G).shatterer ∧ ¬ ((∃ A ∈ F ∪ G, R ⊆ A) ∧ (∃ B ∈ G, Disjoint R B)) ∧ ¬ ((∃ A ∈ F ∪ G, Disjoint R A) ∧ (∃ B ∈ F, R ⊆ B)) := by
  refine ⟨{{0, 1, 3}}, {{0, 2, 4}, {1, 2, 5}}, {2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
