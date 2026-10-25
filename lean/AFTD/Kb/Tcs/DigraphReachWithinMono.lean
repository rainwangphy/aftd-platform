import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReachWithin

/-!
# digraph_reach_within_mono

Topic: graphs   Node: c5f828056508

Provenance: helper lemma. monotonicity of digraph_reach_within, used for oriented_diameter_bound_holds_mono

Reachability within k steps implies reachability within any k' >= k steps.
-/

theorem digraph_reach_within_mono {V : Type*} (D : Digraph V) {k k' : ℕ} (hk : k ≤ k') (u v : V)
    (h : digraph_reach_within D k u v) : digraph_reach_within D k' u v := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Or.inl ih
