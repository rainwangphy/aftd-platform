import AFTD.Prelude
import AFTD.Kb.Tcs.C

/-!
# cluster_weight_cancellation_individual_permutation

Topic: combinatorics   Node: 669501539114

Provenance: formalization of a published result. Source: arXiv:2611.28063 (The Rotation Strategy Wins Penney's game for Permutations), Lemma 3.1. Stated for an arbitrary finite set T ⊆ [0,d] containing 0 and d in place of the target starts of one ordering σ ∈ S_{k+d}; the lemma depends on σ only through that set, so the paper's statement is the special case T = {target starts of σ}. Proof differs in form: an induction on the partial sums S(U) over gap-bounded subsets containing 0, via S(U) = S({x ∈ U : x + k ≤ max U}).

Let k ≥ 3 and d ≥ 1, and let T be a finite set of natural numbers with 0 ∈ T, d ∈ T and every element of T at most d (for instance the set of target-occurrence starts 0 = t_1 < ... < t_r = d of an ordering of length k + d whose first and last windows are target occurrences). Call a subset M of T a cluster if 0 ∈ M, d ∈ M, and any two elements a < b of M with no element of M strictly between them satisfy b - a < k (successive elements of M differ by less than k). Let w be the sum of (-1)^|M| over all clusters M. Then w ∈ {-1, 0, 1}. Moreover, if T itself does not have all successive differences less than k (some two elements a < b of T with no element of T strictly between them have b - a ≥ k), then w = 0.
-/

/-- Every element of `M` with a smaller element of `M` has one within distance `< k`. -/
def clusterCancelG (k : ℕ) (M : Finset ℕ) : Prop :=
  ∀ b ∈ M, ∀ a ∈ M, a < b → ∃ c ∈ M, c < b ∧ b < c + k

instance clusterCancelG_dec (k : ℕ) : DecidablePred (clusterCancelG k) := fun M => by
  unfold clusterCancelG; infer_instance

theorem clusterCancel_cons_iff (k : ℕ) (M : Finset ℕ) :
    (∀ a ∈ M, ∀ b ∈ M, a < b → (∀ c ∈ M, ¬ (a < c ∧ c < b)) → b - a < k) ↔ clusterCancelG k M := by
  constructor
  · intro h b hb a ha hab
    have hne : (M.filter (· < b)).Nonempty := ⟨a, by simp [ha, hab]⟩
    set c := (M.filter (· < b)).max' hne with hc
    have hcm : c ∈ M.filter (· < b) := Finset.max'_mem _ _
    simp only [Finset.mem_filter] at hcm
    refine ⟨c, hcm.1, hcm.2, ?_⟩
    have := h c hcm.1 b hb hcm.2 (by
      intro e he ⟨h1, h2⟩
      have : e ≤ c := Finset.le_max' _ e (by simp [he, h2])
      omega)
    omega
  · intro h a ha b hb hab hbet
    obtain ⟨c, hc, hcb, hbc⟩ := h b hb a ha hab
    have : c ≤ a := by
      by_contra hca
      exact hbet c hc ⟨by omega, hcb⟩
    omega

theorem clusterCancelG_insert (k m : ℕ) (N : Finset ℕ) (hN : ∀ x ∈ N, x < m) :
    clusterCancelG k (insert m N) ↔ clusterCancelG k N ∧ (N.Nonempty → ∃ c ∈ N, m < c + k) := by
  unfold clusterCancelG
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro b hb a ha hab
      obtain ⟨c, hc, hcb, hbc⟩ := h b (Finset.mem_insert_of_mem hb) a
        (Finset.mem_insert_of_mem ha) hab
      rcases Finset.mem_insert.1 hc with rfl | hc
      · have := hN b hb; omega
      · exact ⟨c, hc, hcb, hbc⟩
    · rintro ⟨a, ha⟩
      obtain ⟨c, hc, hcb, hbc⟩ := h m (Finset.mem_insert_self _ _) a
        (Finset.mem_insert_of_mem ha) (hN a ha)
      rcases Finset.mem_insert.1 hc with rfl | hc
      · omega
      · exact ⟨c, hc, hbc⟩
  · rintro ⟨h1, h2⟩ b hb a ha hab
    rcases Finset.mem_insert.1 hb with hbm | hbN
    · subst hbm
      rcases Finset.mem_insert.1 ha with ham | haN
      · omega
      · obtain ⟨c, hc, hmc⟩ := h2 ⟨a, haN⟩
        exact ⟨c, Finset.mem_insert_of_mem hc, hN c hc, hmc⟩
    · rcases Finset.mem_insert.1 ha with ham | haN
      · subst ham; have := hN b hbN; omega
      · obtain ⟨c, hc, hcb, hbc⟩ := h1 b hbN a haN hab
        exact ⟨c, Finset.mem_insert_of_mem hc, hcb, hbc⟩

/-- Signed count of the gap-bounded subsets of `U` containing `0`. -/
noncomputable def clusterCancelP (k : ℕ) (U : Finset ℕ) : ℤ :=
  ∑ M ∈ U.powerset, if 0 ∈ M ∧ clusterCancelG k M then (-1 : ℤ) ^ M.card else 0

theorem clusterCancelP_top (k : ℕ) (hk : 1 ≤ k) (U : Finset ℕ) (hU : U.Nonempty)
    (hm : 0 < U.max' hU) :
    clusterCancelP k U = clusterCancelP k (U.filter (fun x => x + k ≤ U.max' hU)) := by
  set m := U.max' hU with hmdef
  have hmU : m ∈ U := Finset.max'_mem _ _
  have hU' : U = insert m (U.erase m) := (Finset.insert_erase hmU).symm
  have hlt : ∀ x ∈ U.erase m, x < m := by
    intro x hx
    have h1 := Finset.ne_of_mem_erase hx
    have h2 : x ≤ m := Finset.le_max' _ x (Finset.mem_of_mem_erase hx)
    omega
  unfold clusterCancelP
  rw [hU', Finset.sum_powerset_insert (Finset.notMem_erase m U), ← Finset.sum_add_distrib]
  rw [← hU']
  have hsub : (U.filter (fun x => x + k ≤ m)) ⊆ U.erase m := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact Finset.mem_erase.2 ⟨by omega, hx.1⟩
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.powerset_mono.2 hsub)
  · intro N hN
    simp only [Finset.mem_sdiff, Finset.mem_powerset] at hN
    have hNlt : ∀ x ∈ N, x < m := fun x hx => hlt x (hN.1 hx)
    have hm0 : (0 ∈ insert m N) ↔ 0 ∈ N := by
      simp only [Finset.mem_insert]; constructor
      · rintro (h | h); · omega
        · exact h
      · exact Or.inr
    have hmN : m ∉ N := fun h => lt_irrefl _ (hNlt m h)
    simp only [clusterCancelG_insert k m N hNlt, Finset.card_insert_of_notMem hmN, pow_succ]
    obtain ⟨x, hxN, hx⟩ : ∃ x ∈ N, ¬ x + k ≤ m := by
      by_contra hcon
      push Not at hcon
      exact hN.2 (fun x hx => by
        simp only [Finset.mem_filter]; exact ⟨hN.1 hx |> Finset.mem_of_mem_erase, hcon x hx⟩)
    by_cases h : 0 ∈ N ∧ clusterCancelG k N
    · rw [if_pos h, if_pos ⟨hm0.2 h.1, h.2, fun _ => ⟨x, hxN, by omega⟩⟩]; ring
    · rw [if_neg h, if_neg (by tauto)]; ring
  · intro N hN
    simp only [Finset.mem_powerset] at hN
    have hNlt : ∀ x ∈ N, x < m := fun x hx => by
      have := hN hx; simp only [Finset.mem_filter] at this; omega
    have hNk : ∀ x ∈ N, x + k ≤ m := fun x hx => by
      have := hN hx; simp only [Finset.mem_filter] at this; exact this.2
    have hmN : m ∉ N := fun h => lt_irrefl _ (hNlt m h)
    have hm0 : (0 ∈ insert m N) ↔ 0 ∈ N := by
      simp only [Finset.mem_insert]; constructor
      · rintro (h | h); · omega
        · exact h
      · exact Or.inr
    simp only [clusterCancelG_insert k m N hNlt]
    by_cases h : 0 ∈ N ∧ clusterCancelG k N
    · rw [if_pos h, if_neg]
      · simp
      · rintro ⟨_, _, h3⟩
        obtain ⟨c, hc, hmc⟩ := h3 ⟨0, h.1⟩
        have := hNk c hc; omega
    · rw [if_neg h, if_neg (by tauto)]; simp

theorem clusterCancelP_values (k : ℕ) (hk : 1 ≤ k) (U : Finset ℕ) :
    clusterCancelP k U = 0 ∨ clusterCancelP k U = -1 := by
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with rfl | hU
    · left; simp [clusterCancelP]
    by_cases hm : 0 < U.max' hU
    · rw [clusterCancelP_top k hk U hU hm]
      apply ih
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hmU : U.max' hU ∈ U := Finset.max'_mem _ _
      have h2 : U.max' hU ∈ U.filter (fun x => x + k ≤ U.max' hU) := by rw [heq]; exact hmU
      simp only [Finset.mem_filter] at h2
      omega
    · have hU0 : U = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.2
        constructor
        · have := Finset.max'_mem U hU
          have : U.max' hU = 0 := by omega
          rw [← this]; exact Finset.max'_mem U hU
        · intro x hx
          have := Finset.le_max' U x hx
          omega
      subst hU0
      right
      unfold clusterCancelP
      rw [show ({0} : Finset ℕ).powerset = {∅, {0}} by decide, Finset.sum_insert (by decide),
        Finset.sum_singleton]
      have hG : clusterCancelG k {0} := by
        intro b hb a ha hab
        simp only [Finset.mem_singleton] at hb ha; omega
      rw [if_neg (by simp), if_pos ⟨Finset.mem_singleton_self 0, hG⟩]
      simp

theorem clusterCancel_cluster_eq (k d : ℕ) (T : Finset ℕ) (hdT : d ∈ T) :
    (∑ M ∈ T.powerset.filter (fun M => 0 ∈ M ∧ d ∈ M ∧ clusterCancelG k M), (-1 : ℤ) ^ M.card)
      = clusterCancelP k T - clusterCancelP k (T.erase d) := by
  rw [Finset.sum_filter]
  have hT : T = insert d (T.erase d) := (Finset.insert_erase hdT).symm
  have hd : d ∉ T.erase d := Finset.notMem_erase d T
  have e1 : clusterCancelP k T = (∑ N ∈ (T.erase d).powerset,
        if 0 ∈ N ∧ clusterCancelG k N then (-1 : ℤ) ^ N.card else 0) +
      ∑ N ∈ (T.erase d).powerset,
        if 0 ∈ insert d N ∧ clusterCancelG k (insert d N) then (-1 : ℤ) ^ (insert d N).card else 0 := by
    unfold clusterCancelP
    conv_lhs => rw [hT]
    rw [Finset.sum_powerset_insert hd]
  conv_lhs => rw [hT, Finset.sum_powerset_insert hd]
  rw [e1, clusterCancelP, add_sub_cancel_left]
  have h1 : ∀ N ∈ (T.erase d).powerset,
      (if 0 ∈ N ∧ d ∈ N ∧ clusterCancelG k N then (-1 : ℤ) ^ N.card else 0) = 0 := by
    intro N hN
    rw [if_neg]
    rintro ⟨_, h, _⟩
    exact hd (Finset.mem_powerset.1 hN h)
  rw [Finset.sum_eq_zero h1, zero_add]
  apply Finset.sum_congr rfl
  intro N _
  simp

theorem cluster_weight_cancellation_individual_permutation (k d : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d)
    (T : Finset ℕ) (h0 : 0 ∈ T) (hdT : d ∈ T) (hle : ∀ t ∈ T, t ≤ d) :
    let w : ℤ := ∑ M ∈ T.powerset.filter (fun M => 0 ∈ M ∧ d ∈ M ∧
        ∀ a ∈ M, ∀ b ∈ M, a < b → (∀ c ∈ M, ¬ (a < c ∧ c < b)) → b - a < k),
        (-1 : ℤ) ^ M.card
    (w = -1 ∨ w = 0 ∨ w = 1) ∧
      ((¬ ∀ a ∈ T, ∀ b ∈ T, a < b → (∀ c ∈ T, ¬ (a < c ∧ c < b)) → b - a < k) → w = 0) := by
  intro w
  have hw : w = ∑ M ∈ T.powerset.filter (fun M => 0 ∈ M ∧ d ∈ M ∧ clusterCancelG k M),
      (-1 : ℤ) ^ M.card := by
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro M _
      rw [clusterCancel_cons_iff]
    · intro _ _; rfl
  refine ⟨?_, ?_⟩
  · rw [hw, clusterCancel_cluster_eq k d T hdT]
    rcases clusterCancelP_values k (by omega) T with h1 | h1 <;>
      rcases clusterCancelP_values k (by omega) (T.erase d) with h2 | h2 <;>
      · rw [h1, h2]; norm_num
  · intro hT
    rw [clusterCancel_cons_iff] at hT
    rw [hw]
    apply Finset.sum_eq_zero
    intro M hM
    exfalso
    simp only [Finset.mem_filter, Finset.mem_powerset] at hM
    obtain ⟨hMT, h0M, hdM, hGM⟩ := hM
    unfold clusterCancelG at hT
    push Not at hT
    obtain ⟨b, hb, a, ha, hab, hgap⟩ := hT
    have hne : (M.filter (b ≤ ·)).Nonempty := ⟨d, by simp [hdM, hle b hb]⟩
    set b' := (M.filter (b ≤ ·)).min' hne
    have hb'm : b' ∈ M.filter (b ≤ ·) := Finset.min'_mem _ _
    simp only [Finset.mem_filter] at hb'm
    obtain ⟨c, hc, hcb, hbc⟩ := hGM b' hb'm.1 0 h0M (by omega)
    have hcb2 : c < b := by
      by_contra hcon
      have : b' ≤ c := Finset.min'_le _ c (by simp [hc]; omega)
      omega
    have := hgap c (hMT hc) hcb2
    omega
