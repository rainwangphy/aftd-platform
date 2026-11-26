import AFTD.Prelude
import AFTD.Kb.Tcs.Op874LocallyMaximalMatchingCutBalance

/-!
# op874_locally_maximal_cut_tight_structure

Topic: graphs   Node: ebc41bb81a9c

Provenance: helper lemma. Equality case of the matching-cut balance count for OP-874; https://arxiv.org/abs/2610.41950.

At equality in the 1:2 balance bound for a locally maximal matching cut, every matching pair in the larger bit class has exactly two same-bit factor incidences, and every pair in the smaller class has none.
-/

theorem op874_locally_maximal_cut_tight_structure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hsub : M ⊆ G.edgeFinset)
    (hperfect : ∀ v : V, ∃! e : Sym2 V, e ∈ M ∧ v ∈ e)
    (b : V → Bool) (hmatching : ∀ u v, G.Adj u v → s(u,v) ∈ M → b u = b v)
    (hcut : ∀ u v, G.Adj u v → s(u,v) ∈ M →
      ((G.neighborFinset u).filter fun w => b w = b u ∧ s(u,w) ∉ M).card +
      ((G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M).card ≤ 2)
    (htight : (Finset.univ.filter fun v : V => b v = true).card =
      2 * (Finset.univ.filter fun v : V => b v = false).card) :
    ∀ u v, G.Adj u v → s(u,v) ∈ M →
      ((G.neighborFinset u).filter fun w => b w = b u ∧ s(u,w) ∉ M).card +
      ((G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M).card =
        if b u then 2 else 0 := by
  classical
  let me : V → Sym2 V := fun v => Classical.choose (hperfect v)
  have me_mem : ∀ v, me v ∈ M := fun v => (Classical.choose_spec (hperfect v)).1.1
  have v_mem_me : ∀ v, v ∈ me v := fun v => (Classical.choose_spec (hperfect v)).1.2
  have me_uniq : ∀ v e, e ∈ M → v ∈ e → e = me v := fun v e he hv =>
    (Classical.choose_spec (hperfect v)).2 e ⟨he, hv⟩
  let mate : V → V := fun v => Sym2.Mem.other (v_mem_me v)
  have me_eq : ∀ v, me v = s(v, mate v) := fun v => (Sym2.other_spec (v_mem_me v)).symm
  have mate_mem_me : ∀ v, mate v ∈ me v := fun v => Sym2.other_mem (v_mem_me v)
  have match_mem : ∀ v, s(v, mate v) ∈ M := by
    intro v; rw [← me_eq v]; exact me_mem v
  have match_adj : ∀ v, G.Adj v (mate v) := by
    intro v
    have h : s(v, mate v) ∈ G.edgeFinset := hsub (match_mem v)
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
  have b_mate : ∀ v, b (mate v) = b v :=
    fun v => (hmatching v (mate v) (match_adj v) (match_mem v)).symm
  have me_mate : ∀ v, me (mate v) = me v :=
    fun v => (me_uniq (mate v) (me v) (me_mem v) (mate_mem_me v)).symm
  have mate_invol : ∀ v, mate (mate v) = v := by
    intro v
    have h1 : s(mate v, mate (mate v)) = me (mate v) := by
      simpa [mate] using (Sym2.other_spec (mate_mem_me (mate v))).symm
    have h2 : me (mate v) = s(mate v, v) := by rw [me_mate v, me_eq v, Sym2.eq_swap]
    exact (Sym2.congr_right).mp (h1.trans h2)
  have unique_match_nbhd : ∀ v w, G.Adj v w → s(v,w) ∈ M → w = mate v := by
    intro v w _ hmem
    have heq : s(v,w) = me v := me_uniq v (s(v,w)) hmem (by simp)
    rw [me_eq v] at heq
    exact (Sym2.congr_right).mp heq
  let sameInc : V → ℕ := fun v =>
    (Finset.univ.filter fun w : V => G.Adj v w ∧ b w = b v ∧ s(v,w) ∉ M).card
  let oppInc : V → ℕ := fun v =>
    (Finset.univ.filter fun w : V => G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M).card
  have hfilter2 : ∀ v,
      (G.neighborFinset v).filter (fun w => s(v,w) ∉ M) = (G.neighborFinset v).erase (mate v) := by
    intro v
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hwn, hnm⟩
      exact ⟨fun h => hnm (h ▸ match_mem v), hwn⟩
    · rintro ⟨hne, hwn⟩
      exact ⟨hwn, fun hmem =>
        hne (unique_match_nbhd v w ((SimpleGraph.mem_neighborFinset G v w).mp hwn) hmem)⟩
  have nonmatch_deg : ∀ v, (Finset.univ.filter fun w : V => G.Adj v w ∧ s(v,w) ∉ M).card = 2 := by
    intro v
    have h1 : (Finset.univ.filter fun w : V => G.Adj v w ∧ s(v,w) ∉ M) =
        (G.neighborFinset v).filter (fun w => s(v,w) ∉ M) := by
      rw [SimpleGraph.neighborFinset_eq_filter]
      ext w; simp
    rw [h1, hfilter2 v, Finset.card_erase_of_mem]
    · have h2 : (G.neighborFinset v).card = 3 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hcubic.degree_eq v]
      omega
    · rw [SimpleGraph.mem_neighborFinset]
      exact match_adj v
  have same_add_opp : ∀ v, sameInc v + oppInc v = 2 := by
    intro v
    simp only [sameInc, oppInc]
    let A : Finset V := Finset.univ.filter fun w : V => G.Adj v w ∧ s(v,w) ∉ M
    have hsame : (Finset.univ.filter fun w : V => G.Adj v w ∧ b w = b v ∧ s(v,w) ∉ M) =
        A.filter (fun w => b w = b v) := by
      simp [A, Finset.filter_filter, and_assoc, and_comm]
    have hopp : (Finset.univ.filter fun w : V => G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M) =
        A.filter (fun w => ¬ b w = b v) := by
      simp [A, Finset.filter_filter, and_assoc, and_comm, Ne]
    rw [hsame, hopp, Finset.card_filter_add_card_filter_not]
    exact nonmatch_deg v
  have same_eq : ∀ v, sameInc v =
      ((G.neighborFinset v).filter fun w => b w = b v ∧ s(v,w) ∉ M).card := by
    intro v
    simp only [sameInc]
    rw [SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext w
    simp
  have hcut' : ∀ v, sameInc v + sameInc (mate v) ≤ 2 := by
    intro v
    have h1 := hcut v (mate v) (match_adj v) (match_mem v)
    rw [← same_eq v, ← same_eq (mate v)] at h1
    exact h1
  have pair_opp : ∀ v, 2 ≤ oppInc v + oppInc (mate v) := by
    intro v
    have h1 := hcut' v
    have h2 := same_add_opp v
    have h3 := same_add_opp (mate v)
    omega
  let S : Finset V := Finset.univ.filter (fun v => b v = false)
  let T : Finset V := Finset.univ.filter (fun v => b v = true)
  have hSmate : ∀ v ∈ S, mate v ∈ S := by
    intro v hv
    have hv' : b v = false := by simpa [S] using hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [b_mate v]; exact hv'
  have hTmate : ∀ v ∈ T, mate v ∈ T := by
    intro v hv
    have hv' : b v = true := by simpa [T] using hv
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [b_mate v]; exact hv'
  have hsum_inv : ∀ A : Finset V, (∀ v ∈ A, mate v ∈ A) →
      ∑ v ∈ A, oppInc (mate v) = ∑ v ∈ A, oppInc v := by
    intro A hA
    refine Finset.sum_nbij' mate mate hA hA (fun v _ => mate_invol v) (fun v _ => mate_invol v)
      (fun v _ => rfl)
  have hcard2' : ∀ A : Finset V, ∑ _v ∈ A, (2:ℕ) = 2 * A.card := by
    intro A
    induction A using Finset.induction with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, ih, Finset.card_insert_of_notMem ha]; ring
  have hA_le : ∀ A : Finset V, (∀ v ∈ A, mate v ∈ A) → A.card ≤ ∑ v ∈ A, oppInc v := by
    intro A hA
    have h1 : ∑ v ∈ A, (oppInc v + oppInc (mate v)) =
        ∑ v ∈ A, oppInc v + ∑ v ∈ A, oppInc v := by
      rw [Finset.sum_add_distrib, hsum_inv A hA]
    have h2 : ∑ v ∈ A, (2:ℕ) ≤ ∑ v ∈ A, (oppInc v + oppInc (mate v)) :=
      Finset.sum_le_sum fun v _ => pair_opp v
    have h3 : ∑ v ∈ A, (2:ℕ) = 2 * A.card := hcard2' A
    omega
  have hB_le : ∀ A : Finset V, ∑ v ∈ A, oppInc v ≤ 2 * A.card := by
    intro A
    have h2 : ∑ v ∈ A, oppInc v ≤ ∑ v ∈ A, (2:ℕ) := by
      refine Finset.sum_le_sum fun v _ => ?_
      have h := same_add_opp v
      omega
    have h3 : ∑ v ∈ A, (2:ℕ) = 2 * A.card := hcard2' A
    omega
  let g : V → V → ℕ := fun v w =>
    (if (G.Adj v w ∧ s(v,w) ∉ M) then (1:ℕ) else 0)
  have gsymm : ∀ v w : V, g v w = g w v := by
    intro v w
    by_cases h : G.Adj v w
    · by_cases hm : s(v,w) ∈ M
      · have hm' : s(w,v) ∈ M := by rwa [Sym2.eq_swap]
        simp [g, h, h.symm, hm, hm']
      · have hm' : s(w,v) ∉ M := by rwa [Sym2.eq_swap]
        simp [g, h, h.symm, hm, hm']
    · have h' : ¬ G.Adj w v := fun hh => h hh.symm
      simp [g, h, h']
  have fiberS : ∀ v ∈ S, oppInc v = ∑ w ∈ T, g v w := by
    intro v hv
    have hbv : b v = false := by simpa [S] using hv
    show (Finset.univ.filter fun w : V => G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M).card = ∑ w ∈ T, g v w
    rw [Finset.card_filter]
    have step : (∑ w ∈ Finset.univ, (if (G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M) then (1:ℕ) else 0))
        = ∑ w ∈ T, (if (G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M) then (1:ℕ) else 0) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro w _ hw
      have hbw : ¬ (b w = true) := fun h => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩)
      have hne : ¬ (b w ≠ b v) := by cases hw' : b w <;> simp_all
      simp [hne]
    rw [step]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hbw : b w = true := by simpa [T] using hw
    show (if (G.Adj v w ∧ b w ≠ b v ∧ s(v,w) ∉ M) then (1:ℕ) else 0) = g v w
    simp [g, hbv, hbw]
  have fiberT : ∀ w ∈ T, oppInc w = ∑ v ∈ S, g w v := by
    intro w hw
    have hbw : b w = true := by simpa [T] using hw
    show (Finset.univ.filter fun v : V => G.Adj w v ∧ b v ≠ b w ∧ s(w,v) ∉ M).card = ∑ v ∈ S, g w v
    rw [Finset.card_filter]
    have step : (∑ v ∈ Finset.univ, (if (G.Adj w v ∧ b v ≠ b w ∧ s(w,v) ∉ M) then (1:ℕ) else 0))
        = ∑ v ∈ S, (if (G.Adj w v ∧ b v ≠ b w ∧ s(w,v) ∉ M) then (1:ℕ) else 0) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro v _ hv
      have hbv : ¬ (b v = false) := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hne : ¬ (b v ≠ b w) := by cases hv' : b v <;> simp_all
      simp [hne]
    rw [step]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hbv : b v = false := by simpa [S] using hv
    show (if (G.Adj w v ∧ b v ≠ b w ∧ s(w,v) ∉ M) then (1:ℕ) else 0) = g w v
    simp [g, hbv, hbw]
  have hcross : ∑ v ∈ S, oppInc v = ∑ w ∈ T, oppInc w := by
    have e1 : ∑ v ∈ S, oppInc v = ∑ v ∈ S, ∑ w ∈ T, g v w :=
      Finset.sum_congr rfl fun v hv => fiberS v hv
    have e2 : ∑ v ∈ S, ∑ w ∈ T, g v w = ∑ w ∈ T, ∑ v ∈ S, g v w := Finset.sum_comm
    have e3 : ∑ w ∈ T, ∑ v ∈ S, g v w = ∑ w ∈ T, ∑ v ∈ S, g w v := by
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
      exact gsymm v w
    have e4 : ∑ w ∈ T, ∑ v ∈ S, g w v = ∑ w ∈ T, oppInc w :=
      Finset.sum_congr rfl fun w hw => (fiberT w hw).symm
    exact e1.trans (e2.trans (e3.trans e4))
  have htight' : T.card = 2 * S.card := by
    simpa [S, T] using htight
  have hXeq : ∑ v ∈ S, oppInc v = 2 * S.card := by
    have h1 : T.card ≤ ∑ v ∈ S, oppInc v := by
      rw [hcross]; exact hA_le T hTmate
    have h2 : ∑ v ∈ S, oppInc v ≤ 2 * S.card := hB_le S
    omega
  have hXeqT : ∑ v ∈ T, oppInc v = T.card := by
    rw [← hcross, hXeq, ← htight']
  have hS_opp2 : ∀ v ∈ S, oppInc v = 2 := by
    have hle : ∀ v ∈ S, oppInc v ≤ (2:ℕ) := by
      intro v _; have := same_add_opp v; omega
    have hsum2 : ∑ v ∈ S, oppInc v = ∑ v ∈ S, (2:ℕ) := by
      rw [hXeq, hcard2' S]
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum2
  have hS_same0 : ∀ v ∈ S, sameInc v = 0 := by
    intro v hv
    have h1 := same_add_opp v
    have h2 := hS_opp2 v hv
    omega
  have hTpair : ∀ v ∈ T, sameInc v + sameInc (mate v) = 2 := by
    have hle : ∀ w ∈ T, (2:ℕ) ≤ oppInc w + oppInc (mate w) := fun w _ => pair_opp w
    have hall : ∀ w ∈ T, oppInc w + oppInc (mate w) = 2 := by
      have hsum_eq : ∑ w ∈ T, (2:ℕ) = ∑ w ∈ T, (oppInc w + oppInc (mate w)) := by
        rw [Finset.sum_add_distrib, hsum_inv T hTmate, hXeqT, hcard2' T]
        ring
      intro w hw
      exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq w hw).symm
    intro v hv
    have h1 := same_add_opp v
    have h2 := same_add_opp (mate v)
    have h3 := hall v hv
    omega
  intro u v hAdj hmem
  have hv : v = mate u := unique_match_nbhd u v hAdj hmem
  rw [← same_eq u, ← same_eq v, hv]
  cases hb : b u with
  | false =>
      have huS : u ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      have h1 := hS_same0 u huS
      have h2 := hS_same0 (mate u) (hSmate u huS)
      rw [h1, h2]
      simp
  | true =>
      have huT : u ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      have h := hTpair u huT
      simpa using h
