import AFTD.Prelude

/-!
# op869_predecessor_postdegree

Topic: online_algorithms   Node: 2fd989bb7e72

Provenance: helper lemma. arXiv:2610.41516, Section 2.2, post-degree controlled adaptive t-fold coloring simulation.

The post-degree of a vertex in an ordered predecessor presentation is the number of later vertices that list it as a predecessor.
-/

def op869_predecessor_postdegree {n : ℕ} (P : Fin n → Finset (Fin n)) (a : Fin n) : ℕ :=
  (Finset.univ.filter (fun b : Fin n => a < b ∧ a ∈ P b)).card
