import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# truncation_exposed_pair_not_mem

Topic: graphs   Node: a8f58df8ec8d

Provenance: helper lemma. sanity lemma for truncation_exposed_pair

Sanity: the internal colour h_v(e) opposite the port (v, e) is not in the exposed pair P_v(e).
-/

theorem truncation_exposed_pair_not_mem {V E Ω : Type*} (ends : E → Sym2 V) (c h : V → E → Ω)
    (v : V) (e : E) : h v e ∉ truncation_exposed_pair ends c h v e :=
  fun hm => hm.2 rfl
