import AFTD.Prelude

/-!
# wild_optimal_partition_fiber_excess

Topic: graphs   Node: e03684a9effd

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

A partition of n vertices into floor(n/3) labeled blocks, each of size at least three, has total excess over three equal to n mod3, and every block has size at most five.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_optimal_partition_fiber_excess {n : ℕ} (p : Fin n → Fin (n/3))
    (hmin : ∀ t, 3 ≤ ((Finset.univ : Finset (Fin n)).filter (fun v => p v = t)).card) :
    (∑ t : Fin (n/3), (((Finset.univ : Finset (Fin n)).filter (fun v => p v = t)).card-3)) = n%3 ∧
      ∀ t, ((Finset.univ : Finset (Fin n)).filter (fun v => p v = t)).card ≤ 5 := by
  classical
  let d : Fin (n/3) → ℕ := fun t => ((Finset.univ : Finset (Fin n)).filter fun v => p v=t).card
  have hsum : (∑ t : Fin (n/3), d t) = n := by
    have hi := Finset.card_eq_sum_card_fiberwise (f := p) (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin (n/3)))) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ,Fintype.card_fin] using hi.symm
  have he : (∑ t : Fin (n/3), d t) = (∑ t : Fin (n/3), (d t-3)) + 3*(n/3) := by
    calc _ = ∑ t : Fin (n/3), ((d t-3)+3) := Finset.sum_congr rfl (fun t _ => by have := hmin t; change 3 ≤ d t at this; omega)
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; norm_cast <;> omega
  have htotal : (∑ t : Fin (n/3), (d t-3)) = n%3 := by omega
  refine ⟨htotal,?_⟩
  intro t
  have hi := Finset.single_le_sum (a := t) (s := (Finset.univ : Finset (Fin (n/3))))
    (f := fun t => d t-3) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [htotal] at hi
  change d t ≤ 5
  omega
