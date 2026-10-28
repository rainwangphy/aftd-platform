import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformOpt
import AFTD.Kb.Tcs.GenKServerUniformPathCost

/-!
# gen_k_server_uniform_opt_singleton

Topic: online_algorithms   Node: dc41d75a6d4b

Provenance: helper lemma. Sanity check of gen_k_server_uniform_opt (arXiv:2610.37192, Sec. 2): one request costs 0 if the start serves it and 1 otherwise

For k ≥ 1 and configurations a, r : Fin k → Fin m, the offline optimum of the single request r from a is 0 if a i = r i for some i, and 1 otherwise.
-/

theorem gen_k_server_uniform_opt_singleton {k m : ℕ} (hk : 0 < k) (a r : Fin k → Fin m) :
    gen_k_server_uniform_opt a [r] = if ∃ i, a i = r i then 0 else 1 := by
  open Finset in
  split_ifs with h
  · dsimp [gen_k_server_uniform_opt]
    have h0 : 0 ∈ {c | ∃ os : List (Fin k → Fin m),
        List.Forall₂ (fun o r' => ∃ i, o i = r' i) os [r] ∧ gen_k_server_uniform_path_cost a os = c} := by
      refine ⟨[a], ?_, ?_⟩
      · exact List.Forall₂.cons h List.Forall₂.nil
      · simp [gen_k_server_uniform_path_cost, hammingDist_self]
    have le : sInf {c | ∃ os : List (Fin k → Fin m),
        List.Forall₂ (fun o r' => ∃ i, o i = r' i) os [r] ∧ gen_k_server_uniform_path_cost a os = c} ≤ 0 :=
      Nat.sInf_le h0
    omega
  · dsimp [gen_k_server_uniform_opt]
    have hne : a ⟨0, hk⟩ ≠ r ⟨0, hk⟩ := by
      intro heq
      apply h
      exact ⟨⟨0, hk⟩, heq⟩
    let y := Function.update a ⟨0, hk⟩ (r ⟨0, hk⟩)
    have hy_serves : ∃ i, y i = r i := by
      use ⟨0, hk⟩
      dsimp [y]
      rw [Function.update_self]
    have hy_dist : hammingDist a y = 1 := by
      dsimp [hammingDist]
      have heq : (filter (fun i => a i ≠ y i) univ) = {⟨0, hk⟩} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        by_cases hi : i = ⟨0, hk⟩
        · subst hi
          dsimp [y]
          simp [Function.update_self, hne]
        · dsimp [y]
          simp [hi]
      rw [heq]
      simp
    have h1 : 1 ∈ {c | ∃ os : List (Fin k → Fin m),
        List.Forall₂ (fun o r' => ∃ i, o i = r' i) os [r] ∧ gen_k_server_uniform_path_cost a os = c} := by
      refine ⟨[y], ?_, ?_⟩
      · exact List.Forall₂.cons hy_serves List.Forall₂.nil
      · simp [gen_k_server_uniform_path_cost, hy_dist]
    have hle : sInf {c | ∃ os : List (Fin k → Fin m),
        List.Forall₂ (fun o r' => ∃ i, o i = r' i) os [r] ∧ gen_k_server_uniform_path_cost a os = c} ≤ 1 :=
      Nat.sInf_le h1
    have hge : 1 ≤ sInf {c | ∃ os : List (Fin k → Fin m),
        List.Forall₂ (fun o r' => ∃ i, o i = r' i) os [r] ∧ gen_k_server_uniform_path_cost a os = c} := by
      apply le_csInf ⟨1, h1⟩
      rintro c ⟨os, hos, rfl⟩
      obtain ⟨y', rfl, hy⟩ : ∃ y', os = [y'] ∧ ∃ i, y' i = r i := by
        cases hos with
        | cons hy hnil =>
          cases hnil
          exact ⟨_, rfl, hy⟩
      simp only [gen_k_server_uniform_path_cost, add_zero]
      by_contra! hc
      have hc0 : hammingDist a y' = 0 := by omega
      have heq := eq_of_hammingDist_eq_zero hc0
      subst heq
      exact h hy
    omega
