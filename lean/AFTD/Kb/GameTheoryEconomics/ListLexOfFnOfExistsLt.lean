import AFTD.Prelude

/-!
# list_lex_ofFn_of_exists_lt

Topic: fair_division   Node: 394f5ed69803

Provenance: helper lemma. step towards round_robin_phi_lex_strict_increase

If two vectors on Fin m agree on all coordinates before t and the first vector is strictly smaller at coordinate t, then their list representations are strictly ordered by List.Lex (<).
-/

/-- For functions f, g on Fin m, if they agree on all indices before t and f t < g t, then List.ofFn f is strictly less than List.ofFn g in the lexicographic ordering List.Lex (· < ·). -/
theorem list_lex_ofFn_of_exists_lt {m : ℕ} (f g : Fin m → ℕ)
    (t : Fin m)
    (heq : ∀ s : Fin m, s < t → f s = g s)
    (hlt : f t < g t) :
    List.Lex (· < ·) (List.ofFn f) (List.ofFn g) := by
  induction m with
  | zero =>
      exact Fin.elim0 t
  | succ m ih =>
      rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
      · rw [List.ofFn_succ, List.ofFn_succ]
        exact List.Lex.rel hlt
      · rw [List.ofFn_succ, List.ofFn_succ]
        have h0 : f 0 = g 0 := heq 0 (Fin.succ_pos t')
        rw [h0]
        apply List.Lex.cons
        apply ih
        · intro s hs
          exact heq s.succ (Fin.succ_lt_succ_iff.mpr hs)
        · exact hlt
