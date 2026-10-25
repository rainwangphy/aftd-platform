import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_optimal_deviation_two_outsiders

Topic: equilibria   Node: cdf315d7ace0

Provenance: helper lemma. Structural helper for OP-89, arXiv:2610.04948 Sec. 4 Question 2. It formalizes the coalition-complement reduction outlined in an earlier session; it does not settle existence of a stable optimum.

Any strong deviation from a welfare-optimal coloring leaves at least two players outside its coalition.
-/

theorem maxcut_optimal_deviation_two_outsiders {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (S : Finset V) (hopt : is_maxcut_optimal G σ)
    (hdev : is_maxcut_strong_deviation G σ S τ) : 2 ≤ Sᶜ.card := by
  classical
  obtain ⟨hne, hout, hgain⟩ := hdev
  have hgains : ∑ v ∈ S, maxcut_utility G σ v + S.card ≤
      ∑ v ∈ S, maxcut_utility G τ v := by
    have := Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hgain v hv)
    simpa [Finset.sum_add_distrib] using this
  have hσ := Finset.sum_add_sum_compl S (maxcut_utility G σ)
  have hτ := Finset.sum_add_sum_compl S (maxcut_utility G τ)
  have hop := hopt τ
  change (∑ v, maxcut_utility G τ v) ≤ (∑ v, maxcut_utility G σ v) at hop
  have hpos : 0 < S.card := Finset.card_pos.mpr hne
  by_contra hc
  have hle : Sᶜ.card ≤ 1 := by omega
  by_cases he : Sᶜ = ∅
  · simp only [he, Finset.sum_empty] at hσ hτ
    omega
  · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hsingle : Sᶜ = {w} := by
      ext v
      constructor
      · intro hv
        simp only [Finset.mem_singleton]
        exact Finset.card_le_one.mp hle v hv w hw
      · intro hv
        have hvw : v = w := Finset.mem_singleton.mp hv
        simpa [hvw] using hw
    simp only [hsingle, Finset.sum_singleton] at hσ hτ
    let A := Finset.univ.filter fun v => G.Adj w v ∧ σ v ≠ σ w
    have hsub : A ⊆ S := by
      intro v hv
      by_contra hvs
      have hvw : v = w := by
        have : v ∈ Sᶜ := Finset.mem_compl.mpr hvs
        simpa [hsingle] using this
      have ha := (Finset.mem_filter.mp hv).2.1
      subst v
      exact G.loopless.irrefl w ha
    have hbound : maxcut_utility G σ w ≤ S.card := Finset.card_le_card hsub
    have hzero : maxcut_utility G τ w = 0 := by omega
    have hfull : A = S := Finset.eq_of_subset_of_card_le hsub (by
      change S.card ≤ maxcut_utility G σ w
      omega)
    have hconst : ∀ v, τ v = τ w := by
      intro v
      by_cases hv : v ∈ S
      · have ha : G.Adj w v := (Finset.mem_filter.mp (hfull.symm ▸ hv)).2.1
        by_contra hne
        have hmem : v ∈ Finset.univ.filter (fun z => G.Adj w z ∧ τ z ≠ τ w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hne⟩
        have hempty : (Finset.univ.filter fun z => G.Adj w z ∧ τ z ≠ τ w) = ∅ :=
          Finset.card_eq_zero.mp hzero
        simpa [hempty] using hmem
      · have : v = w := by
          have := Finset.mem_compl.mpr hv
          simpa [hsingle] using this
        simp [this]
    obtain ⟨v, hv⟩ := hne
    have hgainv := hgain v hv
    have hu : maxcut_utility G τ v = 0 := by simp [maxcut_utility, hconst]
    omega
