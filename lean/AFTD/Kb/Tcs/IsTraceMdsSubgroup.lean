import AFTD.Prelude

/-!
# is_trace_mds_subgroup

Topic: information   Node: 77e8d56e870e

Provenance: formalization of a published result. Source: arXiv:2610.28047 Lemma 2.9

A subgroup H of L^x satisfies the MDS property of dimension k over F if every subset of H of size at most k is linearly independent over F.
-/

/-- A subgroup of the multiplicative group of a field extension has the MDS property if every subset of size at most k is linearly independent over the base field. -/
def is_trace_mds_subgroup (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L] (H : Subgroup Lˣ) (k : ℕ) : Prop := ∀ (S : Finset H), S.card ≤ k →
    LinearIndependent F (fun (u : S) => ((u.1 : Lˣ) : L))
