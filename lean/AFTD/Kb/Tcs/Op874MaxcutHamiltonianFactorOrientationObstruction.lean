import AFTD.Prelude

/-!
# op874_maxcut_hamiltonian_factor_orientation_obstruction

Topic: graphs   Node: 5dc7629a9ee4

Provenance: helper lemma. Maximum-cut and local-state obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

For an explicitly specified ten-cycle and matching, an all-mixed globally maximum cut defeats both orientations of the factor cycle as a uniform low-port rule.
-/

theorem op874_maxcut_hamiltonian_factor_orientation_obstruction :
    let mate : Fin 10 → Fin 10 := ![2,3,0,1,7,8,9,4,5,6]
    let pair : Fin 10 → Fin 5 := ![0,1,0,1,2,3,4,2,3,4]
    let q : Fin 5 → Bool := ![true,false,true,false,false]
    let bit : Fin 10 → Bool := fun v => q (pair v)
    let degree : Fin 10 → ℕ := fun v =>
      (if bit v = bit (v+1) then 1 else 0) +
      (if bit v = bit (v-1) then 1 else 0)
    let score : (Fin 5 → Bool) → ℕ := fun t =>
      Finset.univ.sum (fun v : Fin 10 => if t (pair v) ≠ t (pair (v+1)) then 1 else 0)
    let next := fun (o : Bool) (v : Fin 10) => if o then v+1 else v-1
    (∀ v, mate (mate v) = v ∧ mate v ≠ v ∧ mate v ≠ v+1 ∧
      mate v ≠ v-1 ∧ bit (mate v) = bit v ∧ degree v + degree (mate v) ≤ 2) ∧
    score q = 8 ∧ (∀ t : Fin 5 → Bool, score t ≤ 8) ∧
    (∀ o : Bool, ∃ v : Fin 10,
      bit v = bit (next o v) ∧ bit (mate v) = bit (next o (mate v))) := by
  exact ⟨by decide, by decide, by decide, by decide⟩
