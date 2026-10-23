import AFTD.Prelude
import AFTD.Kb.Tcs.SubgroupRigidityOrderOfMds
import AFTD.Kb.Tcs.OrderRigidityArithmeticConsequences
import AFTD.Kb.Tcs.IsTraceMdsSubgroup

/-!
# cyclic_mds_subgroup_rigidity

Topic: information   Node: 7cd27bebd3c7

Provenance: formalization of a published result. Source: arXiv:2610.28047 Theorem 3.1 -- Length Bounds for Irreducible Cyclic MDS Codes

Theorem 3.1 of arXiv:2610.28047: Let F be a finite field of cardinality q and L a field extension of F of degree k. Let H be a cyclic subgroup of Lˣ of order n with 2 ≤ k ≤ n - 2. If every subset of H of size at most k is linearly independent over F (is_trace_mds_subgroup F H k), then for every divisor d > 1 of n, the multiplicative order of q modulo d is k; in particular, every prime l dividing n satisfies ord_l(q) = k and k ∣ l - 1; n is odd; gcd(n, q - 1) = 1; gcd(n, k) = 1; and n = m * k + 1 for some integer m ≥ 2.
-/

/-- Theorem 3.1 of arXiv:2610.28047: Subgroup rigidity for irreducible cyclic MDS codes in the trace realization. -/
theorem cyclic_mds_subgroup_rigidity {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L]
    (q n k : ℕ) (H : Subgroup Lˣ) [Fintype H] (hH_cyc : IsCyclic H) (hH_card : Fintype.card H = n)
    (hq : Fintype.card F = q) (hdim : Module.finrank F L = k) (hk : 2 ≤ k) (hkn : k ≤ n - 2)
    (h_mds : is_trace_mds_subgroup F H k) :
    (∀ d : ℕ, d ∣ n → 1 < d → orderOf (q : ZMod d) = k) ∧
    (∀ l : ℕ, Nat.Prime l → l ∣ n → orderOf (q : ZMod l) = k ∧ k ∣ l - 1) ∧
    Odd n ∧ Nat.gcd n (q - 1) = 1 ∧ Nat.gcd n k = 1 ∧ ∃ m ≥ 2, n = m * k + 1 := by
  have h1 : ∀ d : ℕ, d ∣ n → 1 < d → orderOf (q : ZMod d) = k :=
    subgroup_rigidity_order_of_mds q n k H hH_cyc hH_card hq hdim hk hkn h_mds
  obtain ⟨h2, h3, h4, h5, h6⟩ := order_rigidity_arithmetic_consequences q n k hk hkn h1
  exact ⟨h1, h2, h3, h4, h5, h6⟩
