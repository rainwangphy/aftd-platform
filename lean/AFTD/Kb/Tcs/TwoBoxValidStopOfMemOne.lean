import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# two_box_valid_stop_of_mem_one

Topic: online_algorithms   Node: 37d9b1d325b8

Provenance: helper lemma. step towards two_box_counterexample_family

If a valid policy execution has box 1 in its already-opened list and at least one round has elapsed, then the remaining policy is `stop`.
-/

/-- Once box 1 has been opened (and at least one round has elapsed), no valid policy can continue: box 0 is already past its deadline. -/
theorem two_box_valid_stop_of_mem_one (M : ℕ) (hM : 1 < M) (opened : List (Fin 2)) (π : AdaptivePolicy 2)
    (hv : IsValidPolicyAux (two_box_deadline_inst M hM) rfl opened π) (h1 : (1 : Fin 2) ∈ opened)
    (h2 : 1 ≤ opened.length) : π = AdaptivePolicy.stop := by
  cases π with
  | stop => rfl
  | openBox b cont =>
    rw [IsValidPolicyAux.eq_def] at hv
    obtain ⟨hb, hd, -⟩ := hv
    fin_cases b
    · simp only [two_box_deadline_inst, ↓reduceIte, Fin.zero_eta] at hd
      omega
    · exact absurd h1 hb
