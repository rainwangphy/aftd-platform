import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_exact_rank_boundary_successor

Topic: combinatorics   Node: 7cf84a413dad

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

For an exact dyadic-rank matching with both parent implications, if a root selects the last lower offset2q-1 and the edge one unit longer than that rank is covered, its owner has offset a<q and root at least p+q. Unless a=q-1, it also owns the next exact-rank edge. This is uniform in the radius and rank, with no count or periodicity assumption.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_exact_rank_boundary_successor
    (D q : ℕ) (hq : 0 < q) (hD : 2*q < D)
    (x : ℤ → ℕ → Bool)
    (hparent : ∀ r a, a < 2*q →
      (a < q → x r (a+D-2*q) = true → x r a = true) ∧
      (q ≤ a → x r a = true → x r (a+D-2*q) = true))
    (hexact : ∀ v : ℤ, (Finset.range (2*q)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-2*q)).toNat) = 1)
    (p : ℤ) (hboundary : x p (2*q-1) = true)
    (hcover : ∃ a : ℕ, a < 2*q-1 ∧
      x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) a = true ∧
      x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) (a+(D-2*q+1)) = true) :
    ∃ a : ℕ, a < q ∧
      p+(q : ℤ) ≤ p+((2*q-1 : ℕ) : ℤ)-(a : ℤ) ∧
      x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) a = true ∧
      x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) (a+(D-2*q+1)) = true ∧
      (a+1 < q → x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) (a+1) = true ∧
        x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) (a+1+D-2*q) = true) := by
  obtain ⟨a,ha,hlo,hhi⟩ := hcover
  have hb : 2*q-1 < 2*q := by omega
  have hlast := (hparent p (2*q-1) hb).2 (by omega) hboundary
  have haq : a < q := by
    by_contra hn
    have hap := (hparent (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) a (by omega)).2 (by omega) hlo
    have hu := cycle_power_exact_pair_unique D (2*q) x hexact
      (p+((2*q-1 : ℕ) : ℤ)) a (2*q-1) (by omega) hb
      hlo hap (by simpa using hboundary) (by simpa using hlast)
    omega
  refine ⟨a,haq,by omega,hlo,hhi,?_⟩
  intro hn
  have hhi' : x (p+((2*q-1 : ℕ) : ℤ)-(a : ℤ)) (a+1+D-2*q) = true := by
    convert hhi using 1 <;> congr 1 <;> omega
  exact ⟨(hparent _ (a+1) (by omega)).1 hn hhi',hhi'⟩
