import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverServes

/-!
# uniform_kserver_det_alg_serves

Topic: online_algorithms   Node: e921b1877ff8

Provenance: formalization of a published result. Source: arXiv:2610.37192 Sec. 6

A deterministic online algorithm A taking a request list to a configuration serves requests if for every list of earlier requests ρ and current request r, the configuration A (ρ ++ [r]) serves r (meaning A (ρ ++ [r]) i = r i for some coordinate i).
-/

/-- A deterministic online algorithm serves requests if it serves the latest request on every sequence. -/
def uniform_kserver_det_alg_serves {k : ℕ} {M : Fin k → Type*}
    (A : List (∀ i, M i) → (∀ i, M i)) : Prop :=
  ∀ (ρ : List (∀ i, M i)) (r : ∀ i, M i), uniform_kserver_serves (A (ρ ++ [r])) r
