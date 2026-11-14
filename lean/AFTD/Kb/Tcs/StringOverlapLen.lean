import AFTD.Prelude

/-!
# string_overlap_len

Topic: approximation   Node: 8a553eadbf8d

Provenance: formalization of a published result. Source: arXiv:2611.16573, Section 2

For two lists x, y : List Γ over an arbitrary alphabet type Γ with decidable equality (strings are lists of letters, not Lean Strings), string_overlap_len x y is the largest natural number k with k < x.length and k < y.length (both strict, so the overlap is proper) such that the last k entries of x equal the first k entries of y, and 0 if no such k exists.
-/

/-- Length of the overlap ov(x, y): the longest v with x = u v and y = v w for nonempty u, w. -/
def string_overlap_len {Γ : Type*} [DecidableEq Γ] (x y : List Γ) : ℕ :=
  Nat.findGreatest
    (fun k => k < x.length ∧ k < y.length ∧ x.drop (x.length - k) = y.take k)
    (min x.length y.length)
