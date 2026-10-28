import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionMassCriterion
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_number_complete_graph_large_odd_multiple_three_eq

Topic: graphs   Node: b34b5ffada6a

Provenance: original. Related work: arXiv:2610.22142, Section 6 conjecture and Theorems 3.4 and 3.5 (the paper proves equality for 3<=n<=12); existing AFTD case n=279. Uniform permutation-event argument with elementary binomial bounds extends equality to an infinite family. Literature checked 2026-10-28 at https://arxiv.org/abs/2610.22142 and searches for the paper title, wild number minimum proper coloring, and wild number 279.

For every odd integer q>=100001, every natural number k equal to the chromatic number of the line graph of the complete graph K_(3q), and every proper edge coloring c of K_(3q) with colors Fin k, the wild number equals 2q. Equivalently, the conjectured equality holds for every n>=300003 with n congruent to 3 modulo 6, for every minimum proper edge coloring.
-/

theorem wild_number_complete_graph_large_odd_multiple_three_eq (q k : ℕ)
    (hq : 100001 ≤ q) (hodd : q % 2 = 1)
    (hk : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin (3 * q))) c = 2 * q := by
  obtain ⟨m, hm⟩ := w279_missing_vertex_equiv (3 * q) k (by omega) (by omega) hk c
  have hk' : k = 3 * q := by simpa using Fintype.card_congr m
  subst k
  obtain ⟨hp, hv⟩ := wild_triple_partition_large_order_mass_bound q hq hodd
  have hu := wild_triple_partition_mass_criterion (by omega : 3 ≤ q) hodd hp hv c m hm
  have hl := wild_number_complete_graph_min_proper_coloring_ge (3 * q) (3 * q) (by omega) hk c
  have he : 4 * ((3 * q + 1) / 2) / 3 = 2 * q := by omega
  rw [he] at hl
  exact le_antisymm hu hl
