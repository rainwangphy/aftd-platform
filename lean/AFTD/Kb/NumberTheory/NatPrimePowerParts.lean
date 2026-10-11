import AFTD.Prelude

/-!
# nat_prime_power_parts

Topic: elementary_number_theory   Node: 6ec9d8a37fe1

Provenance: formalization of a published result. Source: arXiv:2610.11098 (An improved lower bound for separating words by permutation automata), Lemma 2.3 (the set S(q) of maximal prime-power divisors of q).

S(q): the set of maximal prime-power divisors of q, i.e. p^(v_p(q)) for each prime p dividing q.
-/

/-- The maximal prime-power divisors of `q`: `p ^ (multiplicity of p in q)` for each prime factor `p` of `q`. -/
def nat_prime_power_parts (q : ℕ) : Finset ℕ :=
  q.primeFactors.image (fun p => p ^ q.factorization p)
