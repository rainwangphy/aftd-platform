import AFTD.Prelude
import AFTD.Kb.Tcs.IsBipartiteLocallyEncodable

/-!
# bipartite_universally_locally_encodable

Topic: quantum   Node: e18535ccac14

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.1

A bipartite quantum system of dimension dA × dB is universally locally encodable if every state ψ in EuclideanSpace ℂ (Fin dA × Fin dB) with ‖ψ‖ = 1 is locally encodable.
-/

/-- A bipartite quantum system of dimension dA × dB is universally locally encodable if every normalized pure state is locally encodable. -/
def bipartite_universally_locally_encodable (dA dB : ℕ) : Prop := ∀ ψ : EuclideanSpace ℂ (Fin dA × Fin dB), ‖ψ‖ = 1 →
    is_bipartite_locally_encodable ψ
