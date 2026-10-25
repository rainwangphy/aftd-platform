import AFTD.Prelude
import AFTD.Kb.Tcs.OrientedDiameterBoundHolds
import AFTD.Kb.Tcs.DigraphReachWithinMono
import AFTD.Kb.Tcs.DigraphReachWithin
import AFTD.Kb.Tcs.IsGraphOrientation
import AFTD.Kb.Tcs.HasStrongOrientationOfDiameterLe

/-!
# oriented_diameter_bound_holds_mono

Topic: graphs   Node: 5044e9ae6d54

Provenance: helper lemma. monotonicity of oriented_diameter_bound_holds (OP-119)

If every connected bridgeless graph of diameter d has a strong orientation of diameter at most k, the same holds for every k' >= k (f(d) <= k implies f(d) <= k').
-/

theorem oriented_diameter_bound_holds_mono {d k k' : ℕ} (hk : k ≤ k')
    (h : oriented_diameter_bound_holds d k) : oriented_diameter_bound_holds d k' := by
  intro n G hc hb hd
  obtain ⟨D, hD, hr⟩ := h n G hc hb hd
  exact ⟨D, hD, fun u v => digraph_reach_within_mono D hk u v (hr u v)⟩
