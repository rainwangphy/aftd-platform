import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4

/-!
# energy_filter_quartic_cycle_tsum_eq_s4

Topic: statistical_mechanics   Node: 0b159c0178c6

Provenance: helper lemma. OP-892: shifted quartic reindexing and dominated convergence.

If the absolute quartic cycle is summable and each convolution is summable, its signed sum equals the lattice convolution-square constant.
-/

theorem energy_filter_quartic_cycle_tsum_eq_s4 (a : ℤ → ℝ)
    (hab : Summable (fun p : ℤ × ℤ × ℤ =>
      |a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)|))
    (hconv : ∀ m : ℤ, Summable (fun j : ℤ => a j * a (m - j))) :
    (∑' p : ℤ × ℤ × ℤ,
      a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)) =
      energy_filter_sequence_lattice_s4 a := by
  let Q : ℤ × ℤ × ℤ → ℝ := fun p =>
    a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)
  let G : ℤ × ℤ × ℤ → ℝ := fun p =>
    (a p.2.1 * a (p.1 - p.2.1)) * (a p.2.2 * a (p.1 - p.2.2))
  let e : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) := {
    toFun := fun p => (p.1 + p.2.2, p.1, p.2.1)
    invFun := fun p => (p.2.1, p.2.2, p.1 - p.2.1)
    left_inv := by intro p; rcases p with ⟨u,v,w⟩; simp
    right_inv := by intro p; rcases p with ⟨m,u,v⟩; simp }
  have hQ : Summable Q := by apply Summable.of_abs; simpa [Q] using hab
  have heq : ∀ p, Q (e.symm p) = G p := by
    intro p
    rcases p with ⟨m,u,v⟩
    dsimp [Q,G,e]
    have hid : u - v + (m - u) = m - v := by omega
    rw [hid]
    ring
  have hG : Summable G := by
    have h := (e.symm.summable_iff).2 hQ
    convert h using 1
    funext p
    exact (heq p).symm
  have hsum : (∑' p, Q p) = ∑' p, G p := by
    calc
      (∑' p, Q p) = ∑' p, Q (e.symm p) := (e.symm.tsum_eq Q).symm
      _ = ∑' p, G p := tsum_congr heq
  change (∑' p, Q p) = _
  rw [hsum]
  unfold energy_filter_sequence_lattice_s4
  rw [hG.tsum_prod]
  apply tsum_congr
  intro m
  have hm : Summable (fun p : ℤ × ℤ =>
      (a p.1 * a (m - p.1)) * (a p.2 * a (m - p.2))) := by
    simpa [G] using hG.prod_factor m
  have hs := (hconv m).tsum_mul_tsum (hconv m) hm
  simpa [G, pow_two] using hs.symm
