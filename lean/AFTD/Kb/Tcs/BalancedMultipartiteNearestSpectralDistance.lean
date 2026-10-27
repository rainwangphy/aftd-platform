import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedCompleteMultipartiteGraph
import AFTD.Kb.Tcs.SimpleGraphAdjEigenvaluesSorted
import AFTD.Kb.Tcs.SpectralDistanceL2Sq

/-!
# balanced_multipartite_nearest_spectral_distance

Topic: graphs   Node: 017a64191673

Provenance: original. Related work: Open problem OP-546 (posed in this knowledge base). arXiv:2610.18636 shows that a rank-four graph H_{3,n} beats the conjectured complete-tripartite nearest competitor of K_{n,n,n}, at squared spectral distance tending to 1/2 = 2((3-2)/(3-1))^2. It gives upper bounds on the unrestricted nearest distance and an asymptotic classification among complete multipartite competitors only. The unrestricted limit for r >= 4 is open; experiments 6265 and 6273 support the value 2((r-2)/(r-1))^2.

For natural numbers r and n, balanced_multipartite_nearest_spectral_distance r n = c_r(n) is the infimum in ℝ (a minimum over a finite set when some H exists) of d_2^2(T, H) = Σ_i (λ_i(T) − λ_i(H))² over all simple graphs H on Fin (r * n) not isomorphic to T = balanced_complete_multipartite_graph r n, with λ the adjacency eigenvalues sorted nonincreasingly (spectral_distance_l2_sq of simple_graph_adj_eigenvalues_sorted).
-/

noncomputable def balanced_multipartite_nearest_spectral_distance (r n : ℕ) : ℝ := sInf {d : ℝ | ∃ H : SimpleGraph (Fin (r * n)), ¬ Nonempty (balanced_complete_multipartite_graph r n ≃g H) ∧ d = spectral_distance_l2_sq (simple_graph_adj_eigenvalues_sorted (balanced_complete_multipartite_graph r n)) (simple_graph_adj_eigenvalues_sorted H)}
