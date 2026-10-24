import AFTD.Prelude

/-!
# restrictedSumset

Topic: combinatorics   Node: d9b4062e8ba9

Provenance: helper lemma. step towards restricted_diff_card_le_of_missing

The k-fold restricted sumset Σ_k(A) of a finite subset A of an abelian group: the set of all sums of k pairwise distinct elements of A.
-/

/-- The k-fold restricted sumset of a finset: sums of k distinct elements. -/
def restrictedSumset {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (k : ℕ) : Finset G := (A.powersetCard k).image (fun s => ∑ x ∈ s, x)
