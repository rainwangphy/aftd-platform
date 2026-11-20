import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IncidenceOverlapFivePeel
import AFTD.Kb.Tcs.Potential

/-!
# op309_overlap_peel_host_pair_potential_bound

Topic: graphs   Node: 79f46b8f5461

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

For every finite set of classes satisfying overlap-five peeling, the sum over hosts of d(d−1) is at most ten times the number of classes, where d is the number of classes in that set incident with the host.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace In1099PeelPotential

def degree {A B : Type*} [DecidableEq A] (I : SimpleGraph (A ⊕ B))
    [DecidableRel I.Adj] (S : Finset A) (b : B) : Nat :=
  (S.filter fun a => I.Adj (.inl a) (.inr b)).card

def potential {A B : Type*} [DecidableEq A] [Fintype B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) : Nat :=
  ∑ b : B, degree I S b * (degree I S b - 1)

theorem twice_choose_step (n : Nat) : (n+1)*((n+1)-1) = n*(n-1)+2*n := by
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel]; ring

theorem potential_erase {A B : Type*} [DecidableEq A] [Fintype B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj] (S : Finset A) (a : A) (ha : a ∈ S) :
    potential I S = potential I (S.erase a) +
      2 * (∑ b : B, if I.Adj (.inl a) (.inr b) then degree I S b - 1 else 0) := by
  classical
  unfold potential
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : I.Adj (.inl a) (.inr b)
  · have hmem : a ∈ S.filter (fun a => I.Adj (.inl a) (.inr b)) := Finset.mem_filter.mpr ⟨ha,hab⟩
    have hc : degree I (S.erase a) b + 1 = degree I S b := by
      unfold degree
      rw [Finset.filter_erase]
      exact Finset.card_erase_add_one hmem
    have heq := twice_choose_step (degree I (S.erase a) b)
    simp only [hab, if_true]
    rw [← hc]
    simpa using heq
  · have hc : degree I (S.erase a) b = degree I S b := by
      unfold degree
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
      simp [hab]
    simp only [hab, if_false, mul_zero, add_zero, hc]

end In1099PeelPotential
open In1099PeelPotential

theorem op309_overlap_peel_host_pair_potential_bound {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (I : SimpleGraph (A ⊕ B)) [DecidableRel I.Adj]
    (hpeel : op309_incidence_overlap_five_peel I) (S : Finset A) :
    potential I S ≤ 10 * S.card := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hs : S.Nonempty
    · obtain ⟨a,ha,_,hweight⟩ := hpeel S hs
      have hi := ih (S.erase a) (Finset.erase_ssubset ha)
      have heq := In1099PeelPotential.potential_erase I S a ha
      have hc := Finset.card_erase_add_one ha
      unfold In1099PeelPotential.degree at heq
      omega
    · have h0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      simp [In1099PeelPotential.potential,In1099PeelPotential.degree]
