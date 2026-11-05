import AFTD.Prelude
import AFTD.Kb.Tcs.OneDimApTiles

/-!
# one_dim_ap_tile_count

Topic: combinatorics   Node: 455b137d4206

Provenance: formalization of a published result. Source: arXiv:2611.05321 Definition 1.4

For a natural number n, one_dim_ap_tile_count n is the cardinality of one_dim_ap_tiles n, representing the number T_AP(n, 1) of arithmetic progression tiles in {1, ..., n}.
-/

/-- The number T_AP(n, 1) of arithmetic progression tiles in {1, ..., n}. -/
noncomputable def one_dim_ap_tile_count (n : ℕ) : ℕ :=
  (one_dim_ap_tiles n).card
