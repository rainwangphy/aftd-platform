import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingShiftCompletelyPositive
import AFTD.Kb.Tcs.AmpDampingShiftTracePreservingOnlyIf
import AFTD.Kb.Tcs.AmpDampingShiftTrace
import AFTD.Kb.Tcs.AmpDampingShiftSpectralMinRe
import AFTD.Kb.Tcs.AmpDampingShiftSpectralMaxRe
import AFTD.Kb.Tcs.HasKrausRepresentation
import AFTD.Kb.Tcs.SuperopExp
import AFTD.Kb.Tcs.IsTracePreservingLinearMap
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.SpectralMinRe
import AFTD.Kb.Tcs.SpectralMaxRe

/-!
# amp_damping_shift_sharp_spectral_bound

Topic: quantum   Node: 7803b76061b0

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1)

Fix $d \ge 2$, $V = |0\rangle\langle 1|$, $P = |1\rangle\langle 1|$, $G(X) = VXV^\dagger - \tfrac12(PX + XP)$ and $L_c = G + c\,\mathrm{id}$ ($c \in \mathbb{R}$). Then $e^{tL_c}$ is completely positive for all $t \ge 0$, trace-preserving for some $t > 0$ only if $c = 0$, $\operatorname{Tr} L_c = cd^2 - d$, $m(L_c) = c - 1$, $s(L_c) = c$, and hence $\operatorname{Tr} L_c = d\,m(L_c) + (d^2 - d)\,s(L_c)$.
-/

theorem amp_damping_shift_sharp_spectral_bound (d : ℕ) (h : 2 ≤ d) (c : ℝ) :
    (∀ t : ℝ, 0 ≤ t → has_kraus_representation d (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t)) ∧
    (∀ t : ℝ, 0 < t → is_trace_preserving_linear_map d (superop_exp d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) t) → c = 0) ∧
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (amp_damping_generator d h + (c : ℂ) • LinearMap.id) = (c : ℂ) * (d : ℂ) ^ 2 - d ∧
    spectral_min_re d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) = c - 1 ∧ spectral_max_re d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) = c ∧
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (amp_damping_generator d h + (c : ℂ) • LinearMap.id) =
      (d : ℂ) * (spectral_min_re d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) : ℂ) + ((d : ℂ) ^ 2 - d) * (spectral_max_re d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) : ℂ) := by
  refine ⟨fun t ht => amp_damping_shift_completely_positive d h c t ht,
    fun t ht htp => amp_damping_shift_trace_preserving_only_if d h c t ht htp,
    amp_damping_shift_trace d h c, amp_damping_shift_spectral_min_re d h c,
    amp_damping_shift_spectral_max_re d h c, ?_⟩
  rw [amp_damping_shift_trace, amp_damping_shift_spectral_min_re, amp_damping_shift_spectral_max_re]
  push_cast
  ring
