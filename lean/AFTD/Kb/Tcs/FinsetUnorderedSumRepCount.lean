import AFTD.Prelude

/-!
# finset_unordered_sum_rep_count

Topic: combinatorics   Node: 441856cfc96b

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Sec. 1 (definition of r_{A,2}); defined in any additive commutative monoid, the paper works in F_p.

r_{A,2}(s): the number of unordered pairs {a, b} (a = b allowed) of elements of A with a + b = s.
-/

/-- The number of ways to write `s` as `a + b` with `{a, b}` an unordered pair from `A`, repetition allowed: `r_{A,2}(s)`. -/
def finset_unordered_sum_rep_count {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) (s : G) : ℕ :=
  (A.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = s)).card
