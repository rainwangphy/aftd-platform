import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStrongEdgeColoring
import AFTD.Kb.Tcs.MultigraphTruncation

/-!
# truncation_local_states_define_strong_coloring

Topic: graphs   Node: edf39c64d4e3

Provenance: formalization of a published result. Source: arXiv:2610.41950 (Strong edge-colourings of truncations of cubic graphs), Section 2 / Lemma 2.1: 'these states define a strong edge-colouring of T(G)'

The local states (c, h), with c h : V → E → Ω, define a strong edge-colouring of the truncation multigraph_truncation ends: there is χ : Sym2 {p : V × E // p.1 ∈ ends p.2} → Ω such that (1) simple_graph_is_strong_edge_coloring (multigraph_truncation ends) χ; (2) for distinct ports p ≠ q on the same edge of G (p.1.2 = q.1.2, an external edge), χ s(p, q) = c p.1.1 p.1.2, the external colour prescribed at the port p (stated for both orders, so the two ends must prescribe the same colour); (3) for three pairwise distinct ports p, q, r at the same vertex of G (p.1.1 = q.1.1 and p.1.1 = r.1.1), the internal edge s(p, q) gets χ s(p, q) = h r.1.1 r.1.2, the colour prescribed for the internal edge opposite the port r.
-/

def truncation_local_states_define_strong_coloring {V E Ω : Type*} (ends : E → Sym2 V)
    (c h : V → E → Ω) : Prop :=
  ∃ χ : Sym2 {p : V × E // p.1 ∈ ends p.2} → Ω,
    simple_graph_is_strong_edge_coloring (multigraph_truncation ends) χ ∧
    (∀ p q : {p : V × E // p.1 ∈ ends p.2}, p ≠ q → p.1.2 = q.1.2 →
      χ s(p, q) = c p.1.1 p.1.2) ∧
    (∀ p q r : {p : V × E // p.1 ∈ ends p.2}, p ≠ q → p ≠ r → q ≠ r →
      p.1.1 = q.1.1 → p.1.1 = r.1.1 → χ s(p, q) = h r.1.1 r.1.2)
