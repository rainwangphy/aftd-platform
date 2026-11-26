import AFTD.Prelude

/-!
# op1957_four_shore_other_counts_sum_identity

Topic: graphs   Node: c5ff78bee8f6

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore other counts sum identity.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_other_counts_sum_identity
    (g : Fin 4 → Fin 4 → ℕ) (eb : ℕ) (j forbidden : Fin 4) :
    (∑ t ∈ (Finset.univ : Finset (Fin 4)).erase forbidden,
      ((∑ i : Fin 4, g i t) + (if t=1 then eb else 0) - g j t)) =
    (∑ i ∈ (Finset.univ : Finset (Fin 4)).erase j,
      ∑ t ∈ (Finset.univ : Finset (Fin 4)).erase forbidden, g i t) +
      (if forbidden=1 then 0 else eb) := by
  classical
  have e0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have e1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have e2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have e3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  fin_cases j <;> fin_cases forbidden <;> simp [Fin.sum_univ_four,e0,e1,e2,e3] <;> omega
