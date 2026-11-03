import AFTD.Prelude

/-!
# truncation_exposed_pair

Topic: graphs   Node: 0f3389c27158

Provenance: formalization of a published result. Source: arXiv:2610.41950 (Strong edge-colourings of truncations of cubic graphs), Section 2: the exposed pair P_v(e) = I_v \ {h_v(e)} of a local state

For a multigraph given by ends : E → Sym2 V and colour assignments c h : V → E → Ω (c v e is the external colour at the port (v, e), h v e the colour of the internal edge of Δ_v opposite the port (v, e)), the exposed pair at the port (v, e) is the set P_v(e) = I_v \ {h v e} : Set Ω, where I_v is the set of colours ω with c v f ≠ ω for every edge f with v ∈ ends f. In Lean: {ω | (∀ f, v ∈ ends f → c v f ≠ ω) ∧ ω ≠ h v e}.
-/

def truncation_exposed_pair {V E Ω : Type*} (ends : E → Sym2 V) (c h : V → E → Ω)
    (v : V) (e : E) : Set Ω :=
  {ω | (∀ f, v ∈ ends f → c v f ≠ ω) ∧ ω ≠ h v e}
