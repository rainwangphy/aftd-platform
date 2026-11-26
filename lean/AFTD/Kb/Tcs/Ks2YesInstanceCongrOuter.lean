import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2YesInstance
import AFTD.Kb.Tcs.Ks2InstanceOuter
import AFTD.Kb.Tcs.Ks2InstanceVector

/-!
# ks2_yes_instance_congr_outer

Topic: np_completeness   Node: 04c2e3a757c0

Provenance: helper lemma. Helper for OP-2182: with ks2_distinct_phase_twist it shows that re-phasing an instance to make its vectors distinct keeps validity and the answer.

The yes-instance property depends on the encoded vectors only through their outer products: for all c, α, d and lists vs, vs' of encoded vectors, if the list of outer products ks2_instance_outer d p' for p' in vs' equals the list of outer products ks2_instance_outer d p for p in vs, then ks2_yes_instance c α d vs' holds if and only if ks2_yes_instance c α d vs holds.
-/

theorem ks2_yes_instance_congr_outer (c : ℝ) (α : ℚ) (d : ℕ) (vs vs' : List (ℚ × List (ℚ × ℚ)))
    (h : vs'.map (ks2_instance_outer d) = vs.map (ks2_instance_outer d)) :
    ks2_yes_instance c α d vs' ↔ ks2_yes_instance c α d vs := by
  have key : ∀ (us ws : List (ℚ × List (ℚ × ℚ))),
      us.map (ks2_instance_outer d) = ws.map (ks2_instance_outer d) →
      ks2_yes_instance c α d us → ks2_yes_instance c α d ws := by
    intro us ws h ⟨h0, h1, h2, s, hs, h3⟩
    have hnorm : ∀ p, (∑ j, ‖ks2_instance_vector d p j‖ ^ 2 : ℝ) =
        (Matrix.trace (ks2_instance_outer d p)).re := by
      intro p
      simp [ks2_instance_outer, Matrix.trace, Matrix.vecMulVec_apply, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
    have hz : ∀ (s : List Bool) (xs : List (ℚ × List (ℚ × ℚ))),
        List.zipWith (fun b p => (if b then (1 : ℂ) else -1) • ks2_instance_outer d p) s xs =
        List.zipWith (fun b (M : Matrix (Fin d) (Fin d) ℂ) => (if b then (1 : ℂ) else -1) • M) s
          (xs.map (ks2_instance_outer d)) := by
      intro s xs; rw [List.zipWith_map_right]
    have hlen : us.length = ws.length := by simpa using congrArg List.length h
    refine ⟨h0, ?_, by rw [← h]; exact h2, s, by omega, by rw [hz, ← h, ← hz]; exact h3⟩
    intro q hq
    have : ks2_instance_outer d q ∈ us.map (ks2_instance_outer d) := by
      rw [h]; exact List.mem_map_of_mem hq
    obtain ⟨p, hp, hpq⟩ := List.mem_map.mp this
    rw [hnorm, ← hpq, ← hnorm]; exact h1 p hp
  exact ⟨key _ _ h, key _ _ h.symm⟩
