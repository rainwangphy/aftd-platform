import AFTD.Prelude
import AFTD.Kb.Tcs.IsVeDominating
import AFTD.Kb.Tcs.GammaVe
import AFTD.Kb.Tcs.IsV0

/-!
# is_fix_v0

Topic: graphs   Node: 75e36c51aab7

Provenance: formalization of a published result. Source: arXiv:2610.26912 Section 1

A vertex v of a finite simple graph G belongs to V_fix^0(G) if v is in V^0(G) and v belongs to every minimum vertex-edge dominating set S of G.
-/

/-- A vertex belongs to V_fix^0(G) if removing it preserves gamma_ve and it belongs to every minimum ve-dominating set. -/
def is_fix_v0 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) : Prop := is_v0 G v ∧ ∀ S : Finset V, is_ve_dominating G (S : Set V) ∧ S.card = gamma_ve G → v ∈ S
