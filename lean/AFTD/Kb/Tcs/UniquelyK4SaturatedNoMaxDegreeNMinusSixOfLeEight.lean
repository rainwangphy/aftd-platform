import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated
import AFTD.Kb.Tcs.UniquelyK4SaturatedMaxDegreeGeThree

/-!
# uniquely_k4_saturated_no_max_degree_n_minus_six_of_le_eight

Topic: graphs   Node: e85dd9be85d5

Provenance: helper lemma. arXiv:2611.13656 Sec. 3

For every natural number n with 4 ≤ n ≤ 8 and every simple graph G on Fin n, if G is uniquely K_4-saturated, then the maximum degree of G is not equal to n - 6.
-/

open scoped Classical in
/-- No uniquely K_4-saturated simple graph on n vertices with 4 ≤ n ≤ 8 has maximum degree n - 6. -/
theorem uniquely_k4_saturated_no_max_degree_n_minus_six_of_le_eight
    (n : ℕ) (hn : 4 ≤ n) (hn8 : n ≤ 8) (G : SimpleGraph (Fin n))
    (hG : is_uniquely_clique_saturated G 4) :
    G.maxDegree ≠ n - 6 := by
  have h3 : 3 ≤ G.maxDegree :=
    uniquely_k4_saturated_max_degree_ge_three G (by simpa using hn) hG
  omega
