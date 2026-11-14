import AFTD.Prelude
import AFTD.Kb.Tcs.RcSubstringFree
import AFTD.Kb.Tcs.TgreedyRcOutput
import AFTD.Kb.Tcs.MgreedyRcStep
import AFTD.Kb.Tcs.ScsRcOpt
import AFTD.Kb.Tcs.GreedyRcStep

/-!
# tgreedy_rc_two_point_five_approx_of_parts

Topic: approximation   Node: 5e2e05abddf9

Provenance: helper lemma. arXiv:2611.16573, Theorem 2 (TGREEDY-RC is a 2.5-approximation): the assembly of tgreedy_rc_two_point_five_approx from the four steps mgreedy_rc_output_rc_substring_free, greedy_rc_compression_half (Lemma 9), mgreedy_rc_output_length_sum_le_three_opt (Theorem 1) and mgreedy_rc_output_scs_rc_opt_le_two_opt, taken as hypotheses

If t is an output of TGREEDY-RC on S, every MGREEDY-RC output T from S is RC-substring-free, GREEDY-RC from any RC-substring-free T to {t} satisfies 2|t| ≤ Σ_{u∈T}|u| + scs_rc_opt cm T, and every MGREEDY-RC output T from S has Σ_{u∈T}|u| ≤ 3·scs_rc_opt cm S and scs_rc_opt cm T ≤ 2·scs_rc_opt cm S, then 2|t| ≤ 5·scs_rc_opt cm S.
-/

theorem tgreedy_rc_two_point_five_approx_of_parts {Γ : Type*} [DecidableEq Γ] (cm : Γ → Γ)
    (S : Finset (List Γ)) (t : List Γ) (ht : tgreedy_rc_output cm S t)
    (hT : ∀ T : Finset (List Γ), Relation.ReflTransGen (mgreedy_rc_step cm) (S, ∅) (∅, T) →
      rc_substring_free cm T)
    (hcomp : ∀ T : Finset (List Γ), rc_substring_free cm T →
      Relation.ReflTransGen (greedy_rc_step cm) T {t} →
      2 * t.length ≤ (∑ u ∈ T, u.length) + scs_rc_opt cm T)
    (hsum : ∀ T : Finset (List Γ), Relation.ReflTransGen (mgreedy_rc_step cm) (S, ∅) (∅, T) →
      (∑ u ∈ T, u.length) ≤ 3 * scs_rc_opt cm S)
    (hopt : ∀ T : Finset (List Γ), Relation.ReflTransGen (mgreedy_rc_step cm) (S, ∅) (∅, T) →
      scs_rc_opt cm T ≤ 2 * scs_rc_opt cm S) :
    2 * t.length ≤ 5 * scs_rc_opt cm S := by
  obtain ⟨T, h1, h2⟩ := ht
  have a := hcomp T (hT T h1) h2
  have b := hsum T h1
  have c := hopt T h1
  omega
