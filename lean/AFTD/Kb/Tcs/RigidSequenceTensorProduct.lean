import AFTD.Prelude

/-!
# rigid_sequence_tensor_product

Topic: combinatorics   Node: 6e50356eb4f4

Provenance: formalization of a published result. Source: arXiv:2610.35819 Definition 4.2

Given natural numbers n and m, a natural number t, a family of types G(i) with decidable equality for each i in Fin t, and a sequence S(i) in Multiset (G(i)) for each i in Fin t, the tensor product of the sequences S is the multiset of dependent functions x : (i : Fin t) → G(i) supported on the product of the supports of S(i). For each coordinate i in Fin t, x(i) is heavy if its count in S(i) equals n - 1, and light if its count in S(i) is strictly positive, at most m - 1, and not equal to n - 1. The multiplicity of a tuple x is n - 1 if every coordinate x(i) is heavy; m - 1 if exactly one coordinate is light and all other t - 1 coordinates are heavy; and 0 otherwise.
-/

/-- The tensor product of sequences S_1, ..., S_t consisting of tuples with at most one light coordinate, with multiplicity n-1 if all heavy and m-1 otherwise. -/
noncomputable def rigid_sequence_tensor_product (n m : ℕ) {t : ℕ} {G : Fin t → Type*}
    [∀ i, DecidableEq (G i)] (S : (i : Fin t) → Multiset (G i)) :
    Multiset ((i : Fin t) → G i) := open Classical in
  (Fintype.piFinset (fun i => (S i).toFinset)).sum fun x =>
    let is_h (i : Fin t) := (S i).count (x i) = n - 1
    let is_l (i : Fin t) := 0 < (S i).count (x i) ∧ (S i).count (x i) ≤ m - 1 ∧ ¬ is_h i
    let mult :=
      if (∀ i, is_h i ∨ is_l i) then
        let light_coords := Finset.filter is_l Finset.univ
        if light_coords.card = 0 then
          n - 1
        else if light_coords.card = 1 then
          m - 1
        else
          0
      else
        0
    Multiset.replicate mult x
