import AFTD.Prelude
import AFTD.Kb.Tcs.IsApTileStep

/-!
# one_dim_ap_tiles

Topic: combinatorics   Node: 5776c7aa857a

Provenance: formalization of a published result. Source: arXiv:2611.05321 Definition 1.4

For a natural number n, one_dim_ap_tiles n is the finset of all subsets A of Finset.Icc 1 n such that there exists a positive natural number k for which A is an arithmetic progression tile with step k.
-/

/-- The set of all subsets of {1, ..., n} that tile ℤ by an arithmetic progression. -/
noncomputable def one_dim_ap_tiles (n : ℕ) : Finset (Finset ℕ) :=
  open scoped Classical in
  ((Finset.Icc 1 n).powerset).filter (fun A =>
    ∃ (k : ℕ) (hk : 0 < k),
      letI : NeZero k := ⟨ne_of_gt hk⟩
      is_ap_tile_step k A)
