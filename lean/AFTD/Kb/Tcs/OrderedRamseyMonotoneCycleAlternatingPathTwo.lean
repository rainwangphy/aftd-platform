import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedRamseyNumber
import AFTD.Kb.Tcs.MonotoneCycle
import AFTD.Kb.Tcs.AlternatingPath
import AFTD.Kb.Tcs.OrderedRamseyProp
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.HasOrderedCopy
import AFTD.Kb.Tcs.AlternatingPathVertex
import AFTD.Kb.Tcs.Order

/-!
# ordered_ramsey_monotone_cycle_alternating_path_two

Topic: graphs   Node: 338c995ceae9

Provenance: helper lemma. arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 5

For all integers k ≥ 3, the ordered Ramsey number of the monotone cycle MC_k and the alternating path AP_2 is equal to k.
-/

/-- The ordered Ramsey number of the monotone cycle MC_k versus the alternating path AP_2 is k for all k ≥ 3. -/
theorem ordered_ramsey_monotone_cycle_alternating_path_two
    (k : ℕ) (hk : 3 ≤ k) :
    ordered_ramsey_number (monotone_cycle k) (alternating_path 2) = k := by
  have _ := hk
  open SimpleGraph in
  have halt : alternating_path 2 = ⊤ := by
    ext a b
    simp [alternating_path, SimpleGraph.fromRel, alternating_path_vertex]
    fin_cases a <;> fin_cases b <;> decide
  have hupper : ordered_ramsey_prop (monotone_cycle k) (alternating_path 2) k := by
    intro G
    by_cases h : G = ⊤
    · left
      subst h
      use id
      refine ⟨strictMono_id, ?_⟩
      intro u v huv
      rw [SimpleGraph.top_adj]
      exact huv.ne
    · right
      have hne : ∃ u v : Fin k, u < v ∧ ¬ G.Adj u v := by
        by_contra! hall
        apply h
        ext u v
        constructor
        · intro huv
          rw [SimpleGraph.top_adj]
          exact huv.ne
        · intro huv
          rw [SimpleGraph.top_adj] at huv
          rcases lt_trichotomy u v with hlt | heq | hgt
          · exact hall u v hlt
          · exfalso; exact huv heq
          · rw [G.adj_comm]
            exact hall v u hgt
      rcases hne with ⟨u, v, hlt, hnotadj⟩
      let f : Fin 2 → Fin k := fun x => if x = 0 then u else v
      use f
      constructor
      · intro x y hxy
        fin_cases x <;> fin_cases y
        · exfalso; exact lt_irrefl _ hxy
        · dsimp [f]
          exact hlt
        · exfalso; revert hxy; decide
        · exfalso; exact lt_irrefl _ hxy
      · intro x y hxy
        rw [halt, SimpleGraph.top_adj] at hxy
        rw [SimpleGraph.compl_adj]
        constructor
        · fin_cases x <;> fin_cases y
          · exfalso; exact hxy rfl
          · dsimp [f]
            exact hlt.ne
          · dsimp [f]
            exact hlt.ne'
          · exfalso; exact hxy rfl
        · fin_cases x <;> fin_cases y
          · exfalso; exact hxy rfl
          · dsimp [f]
            exact hnotadj
          · dsimp [f]
            rw [G.adj_comm]
            exact hnotadj
          · exfalso; exact hxy rfl
  have hlower : ∀ M < k, ¬ ordered_ramsey_prop (monotone_cycle k) (alternating_path 2) M := by
    intro M hM hprop
    have h := hprop ⊤
    rcases h with ⟨f, hf_mono, hf_adj⟩ | ⟨g, hg_mono, hg_adj⟩
    · have hinj : Function.Injective f := hf_mono.injective
      have hle := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_fin] at hle
      omega
    · have h01 : (alternating_path 2).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
        rw [halt, SimpleGraph.top_adj]
        decide
      have hadj := hg_adj h01
      simp only [compl_top] at hadj
      exact hadj
  dsimp [ordered_ramsey_number]
  have hnonempty : (Set.Nonempty {n | ordered_ramsey_prop (monotone_cycle k) (alternating_path 2) n}) :=
    ⟨k, hupper⟩
  rw [csInf_eq_iff hnonempty]
  refine ⟨hupper, ?_⟩
  intro M hM
  by_contra! hlt
  exact hlower M hlt hM
