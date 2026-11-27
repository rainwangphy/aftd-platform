import AFTD.Prelude
import AFTD.Kb.Tcs.IsConnectionSet
import AFTD.Kb.Tcs.ConnectionDensity

/-!
# intersection_density

Topic: combinatorics   Node: b90caf54b2ee

Provenance: formalization of a published result. Source: arXiv:2611.26732 (connected Cayley approximation of power graphs of finite groups), definition of ρ(G) before Theorem 1.3.

For a finite group G, intersection_density G : ℚ is the unrestricted intersection density ρ(G): the maximum of connection_density G S (that is, (∑_{s∈S} c_G(s)) / (|G|·|S|), the knowledge-base definitions connection_density and c, equal to I(G,S)/(|G||S|/2)) over the finite set of all S : Finset G with is_connection_set G S (identity-free, inverse-closed, nonempty), taken with Finset.sup' (classical decidability). If there is no such S (the trivial group) the value is 0. It is the version of connected_intersection_density without the requirement that S generate G.
-/

noncomputable def intersection_density (G : Type*) [Group G] [Fintype G] : ℚ :=
  open Classical in
  if h : ((Finset.univ : Finset (Finset G)).filter (fun S => is_connection_set G S)).Nonempty then
    ((Finset.univ : Finset (Finset G)).filter (fun S => is_connection_set G S)).sup' h
      (connection_density G)
  else 0
