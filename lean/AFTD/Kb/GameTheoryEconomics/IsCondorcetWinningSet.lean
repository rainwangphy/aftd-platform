import AFTD.Prelude

/-!
# is_condorcet_winning_set

Topic: social_choice   Node: ecbb333d7d58

Provenance: formalization of a published result. Source: Condorcet winning sets (Social Choice and Welfare 44(3):493-517, 2015), definition of Condorcet winning sets and Condorcet dimension

With n voters holding strict rankings of m candidates, S is a Condorcet winning set if for every candidate a ∉ S, strictly fewer than n/2 voters rank a above every member of S (equivalently, a strict majority prefers some member of S to a).
-/

/-- A Condorcet winning set in the election where voter `v` ranks candidate `c` at position `P v c` (position 0 is the top): for every candidate `a` outside `S`, strictly fewer than half of the voters rank `a` above every member of `S`. -/
def is_condorcet_winning_set {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    Prop :=
  ∀ a, a ∉ S → 2 * (Finset.univ.filter fun v => ∀ b ∈ S, P v a < P v b).card < n
