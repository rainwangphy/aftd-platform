import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover

/-!
# simple_graph_has_equivalence_cover_pullback

Topic: combinatorics   Node: 602719f20e82

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

Let G and H be simple graphs on arbitrary types V and W, t a natural number, and f an injective map from V to W such that G adjacency is equivalent to H adjacency of the images. If H has an equivalence cover with t layers, then G has an equivalence cover with t layers.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_has_equivalence_cover_pullback
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (t : ℕ)
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v))
    (hcover : simple_graph_has_equivalence_cover H t) :
    simple_graph_has_equivalence_cover G t := by
  classical
  obtain ⟨c, hc, hcov⟩ := hcover
  let R : Fin t → Setoid V := fun s => Setoid.ker (fun u => c s (f u))
  let d : Fin t → V → V := fun s u => (Quotient.mk (R s) u).out
  have hd (s : Fin t) (u : V) : c s (f (d s u)) = c s (f u) :=
    Quotient.mk_out (s := R s) u
  have he (s : Fin t) (u v : V) : d s u = d s v ↔ c s (f u) = c s (f v) := by
    constructor
    · intro h
      exact (hd s u).symm.trans ((congrArg (fun a => c s (f a)) h).trans (hd s v))
    · intro h
      exact congrArg Quotient.out (Quotient.sound (s := R s) h)
  refine ⟨d, ?_, ?_⟩
  · intro s u v huv heq
    exact (hadj u v).mpr (hc s (f u) (f v) (fun h => huv (hf h)) ((he s u v).mp heq))
  · intro u v huv
    obtain ⟨s, hs⟩ := hcov (f u) (f v) ((hadj u v).mp huv)
    exact ⟨s, (he s u v).mpr hs⟩
