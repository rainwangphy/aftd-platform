import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeneratingConnectionSet
import AFTD.Kb.Tcs.ConnectionDensity
import AFTD.Kb.Tcs.C

/-!
# connected_intersection_density

Topic: combinatorics   Node: 7fd489f0e6c2

Provenance: formalization of a published result. Source: arXiv:2611.26732, Definition 1.4 (equation (2)); the value 0 for the trivial group is a Lean convention, the paper excludes it

For a finite group $G$ (`[Group G] [Fintype G]`), `connected_intersection_density G : ℚ` is the connected intersection density $\rho_{\mathrm{gen}}(G)$: the maximum of `connection_density G S` (that is, $\frac{1}{|G||S|}\sum_{s\in S} c_G(s)$ with $c_G(s) = |\{g : g \in \langle sg\rangle \lor sg \in \langle g\rangle\}|$, the knowledge-base definitions `connection_density` and `c`) over the finite set of all `S : Finset G` with `is_generating_connection_set G S` (identity-free, inverse-closed, generating $G$), taken with `Finset.sup'` (classical decidability). If that set of connection sets were empty the value would be $0$; it never is ($G \setminus \{1\}$ qualifies). For the trivial group the only admissible set is empty and the value is $0$ (the paper leaves the trivial group out).
-/

noncomputable def connected_intersection_density (G : Type*) [Group G] [Fintype G] : ℚ :=
  open Classical in
  if h : ((Finset.univ : Finset (Finset G)).filter (fun S => is_generating_connection_set G S)).Nonempty then
    ((Finset.univ : Finset (Finset G)).filter (fun S => is_generating_connection_set G S)).sup' h
      (connection_density G)
  else 0
