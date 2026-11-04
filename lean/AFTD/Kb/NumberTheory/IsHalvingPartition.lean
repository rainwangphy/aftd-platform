import AFTD.Prelude

/-!
# is_halving_partition

Topic: elementary_number_theory   Node: 294bbf0d9db4

Provenance: formalization of a published result. Source: arXiv:2611.01243 Definition 1

A sequence of positive integers $(p_1, \dots, p_k)$ is a halving partition of $n \ge 1$ if $p_1 \in \{\lfloor n/2 \rfloor, \lceil n/2 \rceil\}$, $p_i \in \{\lfloor p_{i-1}/2 \rfloor, \lceil p_{i-1}/2 \rceil\}$ for $2 \le i \le k$, and $\sum_{i=1}^k p_i = n$; the empty sequence is the unique halving partition of $0$.
-/

/-- Predicate that a list of positive integers is a halving partition of n. -/
def is_halving_partition (n : ℕ) (p : List ℕ) : Prop := (∀ x ∈ p, 0 < x) ∧ p.sum = n ∧
  match p with
  | [] => n = 0
  | p1 :: _ =>
    (p1 = n / 2 ∨ p1 = (n + 1) / 2) ∧
    List.IsChain (fun x y => y = x / 2 ∨ y = (x + 1) / 2) p
