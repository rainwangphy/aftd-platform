import AFTD.Prelude
import AFTD.Kb.Tcs.VAmpDamping
import AFTD.Kb.Tcs.PAmpDamping

/-!
# amp_damping_generator

Topic: quantum   Node: a5a9ba7a68bd

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1), the map G

The $\mathbb{C}$-linear map $G : M_d(\mathbb{C}) \to M_d(\mathbb{C})$ (bundled as a linear endomorphism, for $d \ge 2$), $G(X) = V X V^\dagger - \tfrac12(PX + XP)$, where $V = |0\rangle\langle 1|$ and $P = |1\rangle\langle 1|$.
-/

/-- The amplitude-damping generator G(X) = V X V† - (1/2)(P X + X P) on d × d complex matrices, with V = |0⟩⟨1| and P = |1⟩⟨1|. -/
noncomputable def amp_damping_generator (d : ℕ) (h : 2 ≤ d) : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  (LinearMap.mulLeft ℂ (v_amp_damping d h)).comp (LinearMap.mulRight ℂ (star (v_amp_damping d h)))
  - (1/2 : ℂ) • (LinearMap.mulLeft ℂ (p_amp_damping d h) + LinearMap.mulRight ℂ (p_amp_damping d h))
