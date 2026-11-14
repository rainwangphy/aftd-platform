import AFTD.Prelude
import AFTD.Kb.Tcs.RegularBipartiteHasPerfectMatching
import AFTD.Kb.Tcs.UniquelyK4SaturatedMaxDegreeSixOrderTwelve
import AFTD.Kb.Tcs.Order

/-!
# regular_bipartite_decompose_perfect_matchings

Topic: graphs   Node: a92b897dcc43

Provenance: helper lemma. Regular bipartite graph decomposition used in arXiv:2609.35280, Section 3.1, from repeated perfect matching removal.

Every d-regular finite bipartite simple graph decomposes into d spanning one-regular subgraphs: every edge appears in exactly one of them.
-/

open SimpleGraph Finset
open scoped Classical

theorem regular_bipartite_decompose_perfect_matchings {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) (hreg : G.IsRegularOfDegree d) (hbip : G.IsBipartite) : ∃ F : Fin d → SimpleGraph V, (∀ i, (F i).IsRegularOfDegree 1 ∧ F i ≤ G) ∧ ∀ u v, G.Adj u v ↔ ∃! i, (F i).Adj u v := by
  classical
  induction d generalizing G with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro u v
      constructor
      · intro huv
        have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
        have hz : G.degree u = 0 := hreg u
        omega
      · rintro ⟨i, _, _⟩
        exact Fin.elim0 i
  | succ d ih =>
    obtain ⟨M, hM⟩ := regular_bipartite_has_perfect_matching G (Nat.succ_pos d) hreg hbip
    let P : SimpleGraph V := M.spanningCoe
    let R : SimpleGraph V := G \ P
    letI : DecidableRel R.Adj := Classical.decRel R.Adj
    have hp_le : P ≤ G := M.spanningCoe_le
    have hp_reg : P.IsRegularOfDegree 1 := by
      intro v
      change M.spanningCoe.degree v = 1
      rw [M.degree_spanningCoe]
      exact (Subgraph.isPerfectMatching_iff_forall_degree.mp hM) v
    have hr_le : R ≤ G := sdiff_le
    have hr_bip : R.IsBipartite := Colorable.mono_left hr_le hbip
    have hr_reg : R.IsRegularOfDegree d := by
      intro v
      have hs : P.neighborFinset v ⊆ G.neighborFinset v := by
        intro w hw
        exact (G.mem_neighborFinset v w).mpr (hp_le ((P.mem_neighborFinset v w).mp hw))
      have hgc : (G.neighborFinset v).card = d + 1 := by
        rw [card_neighborFinset_eq_degree]
        exact hreg v
      have hpc : (P.neighborFinset v).card = 1 := by
        rw [card_neighborFinset_eq_degree]
        exact hp_reg v
      change (G \ P).degree v = d
      rw [← card_neighborFinset_eq_degree,
          neighborFinset_sdiff, Finset.card_sdiff_of_subset hs, hgc, hpc]
      omega
    obtain ⟨F, hFreg, hFedges⟩ := ih R hr_reg hr_bip
    let F' : Fin (d+1) → SimpleGraph V := Fin.cons P F
    have hFzero : F' 0 = P := by simp [F']
    have hFsucc (i : Fin d) : F' i.succ = F i := by simp [F']
    refine ⟨F', ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero =>
        change P.IsRegularOfDegree 1 ∧ P ≤ G
        exact ⟨hp_reg, hp_le⟩
      | succ j =>
        rw [hFsucc]
        exact ⟨(hFreg j).1, (hFreg j).2.trans hr_le⟩
    · intro u v
      constructor
      · intro huv
        by_cases hpuv : P.Adj u v
        · refine ⟨0, ?_, ?_⟩
          · simpa [hFzero] using hpuv
          · intro i hi
            induction i using Fin.cases with
            | zero => rfl
            | succ j =>
              rw [hFsucc] at hi
              have hr : R.Adj u v := (hFreg j).2 hi
              have hn : ¬ P.Adj u v := (sdiff_adj G P u v).mp hr |>.2
              exact False.elim (hn hpuv)
        · have hr : R.Adj u v := (sdiff_adj G P u v).mpr ⟨huv, hpuv⟩
          obtain ⟨j, hj, hjuniq⟩ := (hFedges u v).mp hr
          refine ⟨j.succ, ?_, ?_⟩
          · simpa [hFsucc] using hj
          · intro i hi
            induction i using Fin.cases with
            | zero =>
              have : P.Adj u v := by simpa [hFzero] using hi
              exact False.elim (hpuv this)
            | succ k =>
              rw [hFsucc] at hi
              exact congrArg Fin.succ (hjuniq k hi)
      · rintro ⟨i, hi, _⟩
        induction i using Fin.cases with
        | zero =>
          rw [hFzero] at hi
          exact hp_le hi
        | succ j =>
          rw [hFsucc] at hi
          exact hr_le ((hFreg j).2 hi)
