import AFTD.Prelude
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.Tcs.SkewZeroForcingClosure
import AFTD.Kb.Tcs.SkewZeroForced
import AFTD.Kb.Tcs.SzfMultiForced

/-!
# szf_multigraph_closure_indicator

Topic: graphs   Node: 63c3e0ac27ec

Provenance: helper lemma. sanity lemma for szf_multigraph_closure (arXiv:2611.15741 Section 1)

On a graph without parallel edges (multiplicities 0 or 1, given by neighbourhood sets N), the multigraph skew zero forcing closure coincides with the set-based skew zero forcing closure.
-/

theorem szf_multigraph_closure_indicator {V : Type*} (N : V → Set V) [∀ u, DecidablePred (· ∈ N u)]
    (S : Set V) :
    szf_multigraph_closure (fun u v => if v ∈ N u then 1 else 0) S = skew_zero_forcing_closure N S := by
  ext v
  constructor
  · intro h
    induction h with
    | init v hv => exact SkewZeroForced.init _ hv
    | step u w huw hf ih =>
        apply SkewZeroForced.step u w
        · simpa using huw
        · intro x hx hxw
          exact ih x hxw (by simp [hx])
  · intro h
    induction h with
    | init v hv => exact SzfMultiForced.init _ hv
    | step u w hw hf ih =>
        apply SzfMultiForced.step u w
        · simpa using hw
        · intro x hxw hxne
          exact ih x (by
            by_contra hx
            simp [hx] at hxne) hxw
