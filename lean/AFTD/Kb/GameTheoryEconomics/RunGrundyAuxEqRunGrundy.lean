import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunGrundy
import AFTD.Kb.GameTheoryEconomics.RunGrundyAux
import AFTD.Kb.GameTheoryEconomics.RunBoundary
import AFTD.Kb.GameTheoryEconomics.RunMoveLegal
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# run_grundy_aux_eq_run_grundy

Topic: combinatorial_games   Node: 6ead9cbcfe0f

Provenance: helper lemma. scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:430

For any natural numbers n and k with k + 1 ≤ n, and any boundary conditions α and β, run_grundy_aux n k α β equals run_grundy k α β.
-/

-- The option list of a run of length k, parameterized by a Grundy function γ.
def run_grundy_aux_eq_run_grundy_opt_list (k : ℕ) (γ : ℕ → RunBoundary → RunBoundary → ℕ) (α β : RunBoundary) : List ℕ :=
  (List.range k).flatMap fun idx =>
    let j := idx + 1
    ([RunBoundary.blocked_in, RunBoundary.blocked_out].filterMap fun δ =>
      if run_move_legal k α β j δ = true then
        some (γ (j - 1) α δ ^^^ γ (k - j) δ β) else none)

-- One-step unfolding of run_grundy_aux at a successor depth.
lemma run_grundy_aux_eq_run_grundy_aux_succ_eq (n k : ℕ) (α β : RunBoundary) :
    run_grundy_aux (n+1) k α β =
      if k = 0 then 0 else nat_mex_list (run_grundy_aux_eq_run_grundy_opt_list k (run_grundy_aux n) α β) := by
  rw [show run_grundy_aux (n+1) k α β = run_grundy_aux._f (n+1) ⟨run_grundy_aux n, (Nat.brecOn.go n run_grundy_aux._f).2⟩ k α β from rfl]
  rfl

-- The option list only depends on the values of γ at indices below k.
lemma run_grundy_aux_eq_run_grundy_opt_list_congr (k : ℕ) (γ γ' : ℕ → RunBoundary → RunBoundary → ℕ) (α β : RunBoundary)
    (h : ∀ i, i < k → ∀ δ ε, γ i δ ε = γ' i δ ε) :
    run_grundy_aux_eq_run_grundy_opt_list k γ α β = run_grundy_aux_eq_run_grundy_opt_list k γ' α β := by
  unfold run_grundy_aux_eq_run_grundy_opt_list
  apply List.flatMap_congr
  intro idx hidx
  apply List.filterMap_congr
  intro δ hδ
  have hidx' : idx < k := by simpa using hidx
  have hj2 : k - (idx + 1) < k := by omega
  have h1 := h idx hidx' α δ
  have h2 := h (k - (idx + 1)) hj2 δ β
  by_cases hc : run_move_legal k α β (idx + 1) δ = true
  · simp [hc, h1, h2]
  · simp [hc]

-- Strong induction: run_grundy_aux n k agrees with run_grundy k once the depth bound exceeds k.
lemma run_grundy_aux_eq_run_grundy_aux_strong (n : ℕ) :
    ∀ (k : ℕ) (α β : RunBoundary), k + 1 ≤ n → run_grundy_aux n k α β = run_grundy k α β := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k α β hn
    cases n with
    | zero => omega
    | succ m =>
      cases k with
      | zero =>
        have h1 : run_grundy_aux (m+1) 0 α β = 0 := by
          rw [run_grundy_aux_eq_run_grundy_aux_succ_eq]; simp
        have h2 : run_grundy 0 α β = 0 := by
          rw [show run_grundy 0 α β = run_grundy_aux ((0:ℕ)+1) 0 α β from rfl, run_grundy_aux_eq_run_grundy_aux_succ_eq]
          simp
        rw [h1, h2]
      | succ k' =>
        rw [run_grundy_aux_eq_run_grundy_aux_succ_eq m (k'+1) α β]
        rw [show run_grundy (k'+1) α β = run_grundy_aux (k'+1+1) (k'+1) α β from rfl]
        rw [run_grundy_aux_eq_run_grundy_aux_succ_eq (k'+1) (k'+1) α β]
        simp only [Nat.succ_ne_zero, if_false]
        apply congrArg nat_mex_list
        apply run_grundy_aux_eq_run_grundy_opt_list_congr
        intro i hi δ ε
        have hi1 : i + 1 ≤ k' + 1 := by omega
        have h1 : run_grundy_aux m i δ ε = run_grundy i δ ε := ih m (by omega) i δ ε (by omega)
        have h2 : run_grundy_aux (k'+1) i δ ε = run_grundy i δ ε := ih (k'+1) (by omega) i δ ε hi1
        rw [h1, h2]

/-- The auxiliary Grundy value run_grundy_aux n k α β equals run_grundy k α β for all n ≥ k + 1. -/
theorem run_grundy_aux_eq_run_grundy (n k : ℕ) (α β : RunBoundary) (hn : k + 1 ≤ n) :
    run_grundy_aux n k α β = run_grundy k α β := run_grundy_aux_eq_run_grundy_aux_strong n k α β hn
