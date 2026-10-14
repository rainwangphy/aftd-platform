import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming

/-!
# simple_graph_is_k_star_forming_mono

Topic: graphs   Node: adf613e4a562

Provenance: helper lemma. Monotonicity used implicitly in arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination) (Lemma 2.2 and the minimality arguments).

Every superset of a k-star-forming set is k-star-forming.
-/

theorem simple_graph_is_k_star_forming_mono {V : Type*} (G : SimpleGraph V)
    (k : ℕ) {S T : Finset V} (hST : S ⊆ T) (hS : simple_graph_is_k_star_forming G k S) :
    simple_graph_is_k_star_forming G k T := by
  intro v hv
  obtain ⟨c, L, hc, hL, hcard, hadj, hvc⟩ := hS v (fun h => hv (hST h))
  exact ⟨c, L, hc.imp_right (fun h => hST h), fun x hx => (hL x hx).imp_right (fun h => hST h),
    hcard, hadj, hvc⟩
