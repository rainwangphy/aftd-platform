import AFTD.Prelude

/-!
# op874_all_maxcuts_hamiltonian_have_three_mono_edges

Topic: graphs   Node: 92e7ad91c6c4

Provenance: helper lemma. Maximum-cut palette obstruction for OP-874, using the local compatibility criterion in https://arxiv.org/abs/2610.41950.

On the fourteen-cycle with the displayed matching, the maximum matching-constant cut has value ten and every maximum cut contains a run of three same-bit factor edges.
-/

theorem op874_all_maxcuts_hamiltonian_have_three_mono_edges :
    let mate : Fin 14 → Fin 14 := ![5,10,7,12,9,0,11,2,13,4,1,6,3,8]
    let pair : Fin 14 → Fin 7 := ![0,1,2,3,4,0,5,2,6,4,1,5,3,6]
    let score : (Fin 7 → Bool) → ℕ := fun t =>
      Finset.univ.sum (fun v : Fin 14 => if t (pair v) ≠ t (pair (v+1)) then 1 else 0)
    (∀ v, mate (mate v) = v ∧ mate v ≠ v ∧ mate v ≠ v+1 ∧ mate v ≠ v-1 ∧ pair (mate v) = pair v) ∧
    (∀ t : Fin 7 → Bool, score t ≤ 10) ∧
    (∃ t : Fin 7 → Bool, score t = 10) ∧
    (∀ t : Fin 7 → Bool, score t = 10 → ∃ i : Fin 14,
      ∀ j : Fin 4, t (pair (i + Fin.ofNat 14 j.val)) = t (pair i)) := by
  exact ⟨by decide, by decide, by decide, by decide⟩
