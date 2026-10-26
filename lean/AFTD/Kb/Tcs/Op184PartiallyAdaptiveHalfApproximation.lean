import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraThresholdPolicyLowerBound
import AFTD.Kb.Tcs.PandoraDeadlineFeasibleEmpty
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.PandoraThresholdPolicyValid
import AFTD.Kb.Tcs.PandoraExistsReservation
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.PandoraExistsDeadlineOrder
import AFTD.Kb.Tcs.PandoraCappedSurplus
import AFTD.Kb.Tcs.PandoraExistsBalancingThreshold
import AFTD.Kb.Tcs.PandoraIsReservation
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.Support

/-!
# op184_partially_adaptive_half_approximation

Topic: online_algorithms   Node: 9964602365b5

Provenance: formalization of a published result. Source: arXiv:2610.13775, Theorem 1

For every Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, there exists a valid partially adaptive policy `π : AdaptivePolicy inst.n` satisfying `IsValidPolicy inst π ∧ IsPartiallyAdaptive π` whose expected net utility under deferred-until-stopping commitment `expectedUtilityDUS inst π` is at least `(1 / 2) * optDUS inst`.
-/

/-- Maximum of a list of reals, floored at 0. -/
noncomputable def op184_partially_adaptive_half_approximation_mx (l : List ℝ) : ℝ := l.foldr max 0

lemma op184_partially_adaptive_half_approximation_mx_nil :
    op184_partially_adaptive_half_approximation_mx ([] : List ℝ) = 0 := rfl

lemma op184_partially_adaptive_half_approximation_mx_cons (c : ℝ) (l : List ℝ) :
    op184_partially_adaptive_half_approximation_mx (c :: l) =
      max c (op184_partially_adaptive_half_approximation_mx l) := rfl

lemma op184_partially_adaptive_half_approximation_mx_nonneg (l : List ℝ) :
    0 ≤ op184_partially_adaptive_half_approximation_mx l := by
  induction l with
  | nil => rw [op184_partially_adaptive_half_approximation_mx_nil]
  | cons c l ih =>
    rw [op184_partially_adaptive_half_approximation_mx_cons]
    exact le_trans ih (le_max_right c _)

lemma op184_partially_adaptive_half_approximation_mx_attained (l : List ℝ)
    (hpos : 0 < op184_partially_adaptive_half_approximation_mx l) :
    ∃ a ∈ l, a = op184_partially_adaptive_half_approximation_mx l := by
  induction l with
  | nil =>
    rw [op184_partially_adaptive_half_approximation_mx_nil] at hpos
    exact absurd hpos (lt_irrefl 0)
  | cons c l ih =>
    rw [op184_partially_adaptive_half_approximation_mx_cons] at hpos ⊢
    rcases le_total (op184_partially_adaptive_half_approximation_mx l) c with hle | hle
    · exact ⟨c, List.mem_cons_self, (max_eq_left hle).symm ▸ rfl⟩
    · have hb : max c (op184_partially_adaptive_half_approximation_mx l) =
          op184_partially_adaptive_half_approximation_mx l := max_eq_right hle
      have hpos' : 0 < op184_partially_adaptive_half_approximation_mx l := hb ▸ hpos
      obtain ⟨a, ha, hav⟩ := ih hpos'
      exact ⟨a, List.mem_cons_of_mem c ha, by rw [hav]; exact hb.symm⟩

section Op184Aux

variable {n : ℕ}

/-- The running maximum value of a history. -/
noncomputable def op184_partially_adaptive_half_approximation_hm (h : List (Fin n × ℝ)) : ℝ :=
  op184_partially_adaptive_half_approximation_mx (h.map Prod.snd)

/-- Sum of reservation penalties `(v - r)^+` over a history. -/
noncomputable def op184_partially_adaptive_half_approximation_pen (r : Fin n → ℝ)
    (h : List (Fin n × ℝ)) : ℝ :=
  (h.map (fun bv => max (bv.2 - r bv.1) 0)).sum

/-- Sum of capped surpluses `(min v r - t)^+` over a history. -/
noncomputable def op184_partially_adaptive_half_approximation_cs (r : Fin n → ℝ) (t : ℝ)
    (h : List (Fin n × ℝ)) : ℝ :=
  (h.map (fun bv => max (min bv.2 (r bv.1) - t) 0)).sum

lemma op184_partially_adaptive_half_approximation_pen_cons (r : Fin n → ℝ) (b : Fin n) (v : ℝ)
    (h : List (Fin n × ℝ)) :
    op184_partially_adaptive_half_approximation_pen r ((b,v) :: h) =
      max (v - r b) 0 + op184_partially_adaptive_half_approximation_pen r h := by
  simp [op184_partially_adaptive_half_approximation_pen, List.map_cons, List.sum_cons]

lemma op184_partially_adaptive_half_approximation_cs_cons (r : Fin n → ℝ) (t : ℝ) (b : Fin n) (v : ℝ)
    (h : List (Fin n × ℝ)) :
    op184_partially_adaptive_half_approximation_cs r t ((b,v) :: h) =
      max (min v (r b) - t) 0 + op184_partially_adaptive_half_approximation_cs r t h := by
  simp [op184_partially_adaptive_half_approximation_cs, List.map_cons, List.sum_cons]

lemma op184_partially_adaptive_half_approximation_pen_nonneg (r : Fin n → ℝ)
    (h : List (Fin n × ℝ)) : 0 ≤ op184_partially_adaptive_half_approximation_pen r h := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ 0

lemma op184_partially_adaptive_half_approximation_cs_nonneg (r : Fin n → ℝ) (t : ℝ)
    (h : List (Fin n × ℝ)) : 0 ≤ op184_partially_adaptive_half_approximation_cs r t h := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ 0

/-- Pointwise split: `v - t` is at most the penalty plus the capped surplus. -/
lemma op184_partially_adaptive_half_approximation_key (v r t : ℝ) :
    v - t ≤ max (v - r) 0 + max (min v r - t) 0 := by
  rcases le_total v r with h | h
  · have hmin : min v r = v := min_eq_left h
    rw [hmin]
    have h1 : v - t ≤ max (v - t) 0 := le_max_left _ _
    have h2 : (0:ℝ) ≤ max (v - r) 0 := le_max_right _ _
    linarith
  · have hmin : min v r = r := min_eq_right h
    rw [hmin]
    rcases le_total r t with h2 | h2
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ v - r), max_eq_right (by linarith : r - t ≤ 0)]
      linarith
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ v - r)]
      have h3 : r - t ≤ max (r - t) 0 := le_max_left _ _
      linarith

lemma op184_partially_adaptive_half_approximation_hm_eq (h : List (Fin n × ℝ)) :
    h.foldl (fun acc bv => max acc bv.2) 0 = op184_partially_adaptive_half_approximation_hm h := by
  have h1 : (h.map Prod.snd).foldl max 0 = h.foldl (fun acc bv => max acc bv.2) 0 := by
    rw [List.foldl_map]
  rw [← h1, List.foldl_eq_foldr]
  rfl

lemma op184_partially_adaptive_half_approximation_hm_sub_pen_le (r : Fin n → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (h : List (Fin n × ℝ)) :
    op184_partially_adaptive_half_approximation_hm h -
        op184_partially_adaptive_half_approximation_pen r h ≤
      t + op184_partially_adaptive_half_approximation_cs r t h := by
  rcases lt_or_ge t (op184_partially_adaptive_half_approximation_hm h) with hm | hm
  · have hpos : 0 < op184_partially_adaptive_half_approximation_hm h := lt_of_le_of_lt ht hm
    obtain ⟨a, ha, hav⟩ :=
      op184_partially_adaptive_half_approximation_mx_attained (h.map Prod.snd) hpos
    obtain ⟨bv, hbv, hbva⟩ := List.mem_map.mp ha
    obtain ⟨b, v⟩ := bv
    have hva : v = a := hbva
    have hval : v = op184_partially_adaptive_half_approximation_hm h := by rw [hva, hav]; rfl
    have hpen : max (v - r b) 0 ≤ op184_partially_adaptive_half_approximation_pen r h :=
      List.single_le_sum (l := h.map (fun bv => max (bv.2 - r bv.1) 0))
        (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact le_max_right _ 0)
        _ (List.mem_map.mpr ⟨(b,v), hbv, rfl⟩)
    have hcs : max (min v (r b) - t) 0 ≤ op184_partially_adaptive_half_approximation_cs r t h :=
      List.single_le_sum (l := h.map (fun bv => max (min bv.2 (r bv.1) - t) 0))
        (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact le_max_right _ 0)
        _ (List.mem_map.mpr ⟨(b,v), hbv, rfl⟩)
    have hk := op184_partially_adaptive_half_approximation_key v (r b) t
    rw [hval] at hpen hcs hk
    linarith
  · linarith [op184_partially_adaptive_half_approximation_pen_nonneg r h,
      op184_partially_adaptive_half_approximation_cs_nonneg r t h]

end Op184Aux

section Op184W

variable {n : ℕ}

/-- Remaining capped surplus available to a searcher who has already opened `H`: the maximum
total capped surplus of an `H`-disjoint set `N` whose union with `H` is deadline-feasible. -/
noncomputable def op184_partially_adaptive_half_approximation_w (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) (H : Finset (Fin inst.n)) : ℝ := by
  classical
  exact (Finset.univ.powerset).sup' ⟨∅, by simp⟩
    (fun N => if Disjoint N H ∧ pandora_deadline_feasible inst (H ∪ N) then
      ∑ i ∈ N, pandora_capped_surplus inst r i t else 0)

lemma op184_partially_adaptive_half_approximation_w_mem_le (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) (H N : Finset (Fin inst.n)) (hdis : Disjoint N H)
    (hfeas : pandora_deadline_feasible inst (H ∪ N)) :
    ∑ i ∈ N, pandora_capped_surplus inst r i t ≤
      op184_partially_adaptive_half_approximation_w inst r t H := by
  classical
  have hmem : N ∈ (Finset.univ : Finset (Fin inst.n)).powerset := by simp
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin inst.n)).powerset)
    (fun N => if Disjoint N H ∧ pandora_deadline_feasible inst (H ∪ N) then
      ∑ i ∈ N, pandora_capped_surplus inst r i t else 0) hmem
  rw [op184_partially_adaptive_half_approximation_w]
  refine le_trans ?_ h
  rw [if_pos ⟨hdis, hfeas⟩]

lemma op184_partially_adaptive_half_approximation_w_exists (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) (H : Finset (Fin inst.n))
    (hH : pandora_deadline_feasible inst H) :
    ∃ N : Finset (Fin inst.n), Disjoint N H ∧ pandora_deadline_feasible inst (H ∪ N) ∧
      ∑ i ∈ N, pandora_capped_surplus inst r i t =
        op184_partially_adaptive_half_approximation_w inst r t H := by
  classical
  obtain ⟨N, hNmem, hN⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin inst.n)).powerset) ⟨∅, by simp⟩
    (fun N => if Disjoint N H ∧ pandora_deadline_feasible inst (H ∪ N) then
      ∑ i ∈ N, pandora_capped_surplus inst r i t else 0)
  by_cases hc : Disjoint N H ∧ pandora_deadline_feasible inst (H ∪ N)
  · exact ⟨N, hc.1, hc.2, by rw [op184_partially_adaptive_half_approximation_w, hN, if_pos hc]⟩
  · refine ⟨∅, by simp, ?_, ?_⟩
    · simpa using hH
    · rw [op184_partially_adaptive_half_approximation_w, hN, if_neg hc]; simp

lemma op184_partially_adaptive_half_approximation_w_nonneg (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) (H : Finset (Fin inst.n))
    (hH : pandora_deadline_feasible inst H) :
    0 ≤ op184_partially_adaptive_half_approximation_w inst r t H := by
  have h := op184_partially_adaptive_half_approximation_w_mem_le inst r t H ∅ (by simp)
    (by simpa using hH)
  simpa using h

/-- Opening box `b` costs at most its capped surplus out of the remaining potential. -/
lemma op184_partially_adaptive_half_approximation_w_step (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) (H : Finset (Fin inst.n)) (b : Fin inst.n)
    (_hH : pandora_deadline_feasible inst H) (hb : b ∉ H)
    (hHb : pandora_deadline_feasible inst (insert b H)) :
    pandora_capped_surplus inst r b t +
        op184_partially_adaptive_half_approximation_w inst r t (insert b H) ≤
      op184_partially_adaptive_half_approximation_w inst r t H := by
  classical
  obtain ⟨N, hdis, hfeas, hsum⟩ :=
    op184_partially_adaptive_half_approximation_w_exists inst r t (insert b H) hHb
  have hbN : b ∉ N := fun h => Finset.disjoint_left.mp hdis h (by simp)
  have hdis' : Disjoint (insert b N) H := by
    rw [Finset.disjoint_left]
    intro x hx hxH
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hb hxH
    · exact Finset.disjoint_left.mp hdis hx' (Finset.mem_insert_of_mem hxH)
  have hfeas' : pandora_deadline_feasible inst (H ∪ insert b N) := by
    have heq : H ∪ insert b N = insert b H ∪ N := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]; exact hfeas
  have h := op184_partially_adaptive_half_approximation_w_mem_le inst r t H (insert b N) hdis' hfeas'
  rw [Finset.sum_insert hbN] at h
  rw [← hsum]
  exact h

lemma op184_partially_adaptive_half_approximation_sum_branch (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t Y : ℝ) (b : Fin inst.n) :
    ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (Y + max (min v (r b) - t) 0)
      = Y + pandora_capped_surplus inst r b t := by
  rw [pandora_capped_surplus]
  have h1 : ∀ v, (inst.dist b).prob v * (Y + max (min v (r b) - t) 0)
      = (inst.dist b).prob v * Y + (inst.dist b).prob v * max (min v (r b) - t) 0 := by
    intro v; ring
  rw [Finset.sum_congr rfl (fun v hv => h1 v), Finset.sum_add_distrib, ← Finset.sum_mul,
    (inst.dist b).sum_prob_one]
  ring

lemma op184_partially_adaptive_half_approximation_feasible_insert (inst : PandoraDeadlineInstance)
    (H : Finset (Fin inst.n)) (b : Fin inst.n) (hH : pandora_deadline_feasible inst H) (hb : b ∉ H)
    (hlen : H.card + 1 ≤ inst.deadline b) :
    pandora_deadline_feasible inst (H ∪ {b}) := by
  intro j
  simp only [pandora_deadline_feasible] at hH
  have hle : {i ∈ H | inst.deadline i ≤ j}.card ≤ H.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  by_cases hdb : inst.deadline b ≤ j
  · have hset : {i ∈ H ∪ {b} | inst.deadline i ≤ j} = insert b {i ∈ H | inst.deadline i ≤ j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro ⟨h | rfl, hd⟩
        · exact Or.inr ⟨h, hd⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨h, hd⟩)
        · exact ⟨Or.inr rfl, hdb⟩
        · exact ⟨Or.inl h, hd⟩
    rw [hset, Finset.card_insert_of_notMem (by simp [hb])]
    omega
  · have hset : {i ∈ H ∪ {b} | inst.deadline i ≤ j} = {i ∈ H | inst.deadline i ≤ j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨h | rfl, hd⟩
        · exact ⟨h, hd⟩
        · exact absurd hd hdb
      · rintro ⟨h, hd⟩
        exact ⟨Or.inl h, hd⟩
    rw [hset]
    exact hH j

lemma op184_partially_adaptive_half_approximation_capped_surplus_nonneg
    (inst : PandoraDeadlineInstance) (r : Fin inst.n → ℝ) (t : ℝ) (i : Fin inst.n) :
    0 ≤ pandora_capped_surplus inst r i t := by
  rw [pandora_capped_surplus]
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg ((inst.dist i).prob_nonneg v hv) (le_max_right _ 0)

/-- The penalty-subtracted expected utility telescopes over opening a box. -/
lemma op184_partially_adaptive_half_approximation_aux_pen_step (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (h : List (Fin inst.n × ℝ))
    (b : Fin inst.n) (cont : ℝ → AdaptivePolicy inst.n) :
    expectedUtilityDUS.aux inst h (AdaptivePolicy.openBox b cont) -
        op184_partially_adaptive_half_approximation_pen r h
      = ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          (expectedUtilityDUS.aux inst ((b,v)::h) (cont v) -
            op184_partially_adaptive_half_approximation_pen r ((b,v)::h)) := by
  classical
  rw [expectedUtilityDUS.aux.eq_2]
  have hsum1 : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
        (expectedUtilityDUS.aux inst ((b,v)::h) (cont v) -
          op184_partially_adaptive_half_approximation_pen r ((b,v)::h))
      = ∑ v ∈ (inst.dist b).support, ((inst.dist b).prob v * expectedUtilityDUS.aux inst ((b,v)::h) (cont v)
          - (inst.dist b).prob v * op184_partially_adaptive_half_approximation_pen r h
          - (inst.dist b).prob v * max (v - r b) 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [op184_partially_adaptive_half_approximation_pen_cons r b v h]; ring
  rw [hsum1, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    (inst.dist b).sum_prob_one, hr b]
  ring

/-- Lemma 1 (adaptive surplus upper bound): every valid policy's expected DUS utility is at most
`t` plus the total capped surplus of some deadline-feasible set. -/
theorem op184_partially_adaptive_half_approximation_aux_bound (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (π : AdaptivePolicy inst.n) (h : List (Fin inst.n × ℝ)),
      pandora_deadline_feasible inst (h.map Prod.fst).toFinset →
      IsValidPolicyAux inst rfl (h.map Prod.fst) π →
      expectedUtilityDUS.aux inst h π - op184_partially_adaptive_half_approximation_pen r h ≤
        t + op184_partially_adaptive_half_approximation_cs r t h +
          op184_partially_adaptive_half_approximation_w inst r t (h.map Prod.fst).toFinset := by
  intro π
  induction π using AdaptivePolicy.rec with
  | stop =>
    intro h hfeas _
    rw [expectedUtilityDUS.aux.eq_1, op184_partially_adaptive_half_approximation_hm_eq]
    have h1 := op184_partially_adaptive_half_approximation_hm_sub_pen_le r t ht h
    have h2 := op184_partially_adaptive_half_approximation_w_nonneg inst r t _ hfeas
    linarith
  | openBox b cont ih =>
    intro h hfeas hval
    rw [IsValidPolicyAux.eq_2] at hval
    obtain ⟨hbnot, hblen, hcont⟩ := hval
    have hbnot' : b ∉ (h.map Prod.fst).toFinset := by simpa using hbnot
    have hlen : (h.map Prod.fst).toFinset.card + 1 ≤ inst.deadline b := by
      have hblen' : (h.map Prod.fst).length + 1 ≤ inst.deadline b := by simpa using hblen
      have hc := List.toFinset_card_le (h.map Prod.fst)
      omega
    have hfeas' : pandora_deadline_feasible inst ((h.map Prod.fst).toFinset ∪ {b}) :=
      op184_partially_adaptive_half_approximation_feasible_insert inst _ b hfeas hbnot' hlen
    rw [op184_partially_adaptive_half_approximation_aux_pen_step inst r hr h b cont]
    have hstep1 : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          (expectedUtilityDUS.aux inst ((b,v)::h) (cont v) -
            op184_partially_adaptive_half_approximation_pen r ((b,v)::h))
        ≤ ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          (t + op184_partially_adaptive_half_approximation_cs r t ((b,v)::h) +
            op184_partially_adaptive_half_approximation_w inst r t
              ((((b,v)::h).map Prod.fst).toFinset)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hpv : 0 ≤ (inst.dist b).prob v := (inst.dist b).prob_nonneg v hv
      have hfeasv : pandora_deadline_feasible inst ((((b,v)::h).map Prod.fst).toFinset) := by
        rw [show ((((b,v)::h).map Prod.fst).toFinset) = insert b (h.map Prod.fst).toFinset from by simp,
          ← Finset.union_singleton]
        exact hfeas'
      have hvalv : IsValidPolicyAux inst rfl ((((b,v)::h).map Prod.fst)) (cont v) := hcont v hv
      exact mul_le_mul_of_nonneg_left (ih v ((b,v)::h) hfeasv hvalv) hpv
    have hstep2 : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          (t + op184_partially_adaptive_half_approximation_cs r t ((b,v)::h) +
            op184_partially_adaptive_half_approximation_w inst r t
              ((((b,v)::h).map Prod.fst).toFinset))
        = t + op184_partially_adaptive_half_approximation_cs r t h +
            op184_partially_adaptive_half_approximation_w inst r t (insert b (h.map Prod.fst).toFinset)
            + pandora_capped_surplus inst r b t := by
      have hfin : ∀ v, ((((b,v)::h).map Prod.fst).toFinset) = insert b (h.map Prod.fst).toFinset := by
        intro v; simp
      simp only [hfin, op184_partially_adaptive_half_approximation_cs_cons]
      rw [show ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
            (t + (max (min v (r b) - t) 0 + op184_partially_adaptive_half_approximation_cs r t h) +
              op184_partially_adaptive_half_approximation_w inst r t (insert b (h.map Prod.fst).toFinset))
          = ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
            ((t + op184_partially_adaptive_half_approximation_cs r t h +
              op184_partially_adaptive_half_approximation_w inst r t (insert b (h.map Prod.fst).toFinset))
              + max (min v (r b) - t) 0)
          from by
        apply Finset.sum_congr rfl
        intro v hv
        ring]
      exact op184_partially_adaptive_half_approximation_sum_branch inst r t _ b
    refine le_trans hstep1 ?_
    rw [hstep2]
    have hHins : pandora_deadline_feasible inst (insert b (h.map Prod.fst).toFinset) := by
      rwa [Finset.union_singleton] at hfeas'
    have hW := op184_partially_adaptive_half_approximation_w_step inst r t
      (h.map Prod.fst).toFinset b hfeas hbnot' hHins
    linarith

lemma op184_partially_adaptive_half_approximation_lemma1 (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (ht : 0 ≤ t)
    (π : AdaptivePolicy inst.n) (hπ : IsValidPolicy inst π) :
    ∃ S : Finset (Fin inst.n), pandora_deadline_feasible inst S ∧
      expectedUtilityDUS inst π ≤ t + ∑ i ∈ S, pandora_capped_surplus inst r i t := by
  have h0 : pandora_deadline_feasible inst (([] : List (Fin inst.n × ℝ)).map Prod.fst).toFinset := by
    simpa using pandora_deadline_feasible_empty inst
  have hπ' : IsValidPolicyAux inst rfl (([] : List (Fin inst.n × ℝ)).map Prod.fst) π := hπ
  have hb := op184_partially_adaptive_half_approximation_aux_bound inst r hr t ht π
    ([] : List (Fin inst.n × ℝ)) h0 hπ'
  rw [op184_partially_adaptive_half_approximation_pen,
    op184_partially_adaptive_half_approximation_cs] at hb
  simp only [List.map_nil, List.sum_nil, List.toFinset_nil] at hb
  obtain ⟨S, _hSdis, hSfeas, hSsum⟩ := op184_partially_adaptive_half_approximation_w_exists inst r t ∅
    (pandora_deadline_feasible_empty inst)
  refine ⟨S, by simpa using hSfeas, ?_⟩
  rw [hSsum]
  simpa [expectedUtilityDUS] using hb

end Op184W

/-- For every Pandora's problem instance with deadlines, there exists a valid partially adaptive policy achieving at least 1/2 of the fully adaptive optimum under deferred-until-stopping commitment. -/
theorem op184_partially_adaptive_half_approximation (inst : PandoraDeadlineInstance) :
    ∃ π : AdaptivePolicy inst.n, IsValidPolicy inst π ∧ IsPartiallyAdaptive π ∧
      (1 / 2 : ℝ) * optDUS inst ≤ expectedUtilityDUS inst π := by
  classical
  obtain ⟨r, hr⟩ := pandora_exists_reservation inst
  obtain ⟨t, ht, S, hSfeas, hSsum, hSmax⟩ := pandora_exists_balancing_threshold inst r
  set S' : Finset (Fin inst.n) := S.filter (fun i => 0 < pandora_capped_surplus inst r i t) with hS'def
  have hS'sub : S' ⊆ S := by
    intro i hi
    rw [hS'def] at hi
    exact Finset.mem_of_mem_filter i hi
  have hS'feas : pandora_deadline_feasible inst S' := by
    intro j
    have h1 : {i ∈ S' | inst.deadline i ≤ j} ⊆ {i ∈ S | inst.deadline i ≤ j} := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hS'sub hi.1, hi.2⟩
    exact le_trans (Finset.card_le_card h1) (hSfeas j)
  have hS'sum : ∑ i ∈ S', pandora_capped_surplus inst r i t = t := by
    rw [hS'def, Finset.sum_filter]
    have hcongr : ∀ i ∈ S,
        (if 0 < pandora_capped_surplus inst r i t then pandora_capped_surplus inst r i t else 0)
          = pandora_capped_surplus inst r i t := by
      intro i hi
      by_cases h : 0 < pandora_capped_surplus inst r i t
      · rw [if_pos h]
      · rw [if_neg h]
        have hnn := op184_partially_adaptive_half_approximation_capped_surplus_nonneg inst r t i
        linarith
    rw [Finset.sum_congr rfl hcongr, hSsum]
  obtain ⟨order, hnd, htof, hdl⟩ := pandora_exists_deadline_order inst S' hS'feas
  have hpos : ∀ i ∈ order, 0 < pandora_capped_surplus inst r i t := by
    intro i hi
    have hi' : i ∈ S' := by rw [← htof]; exact List.mem_toFinset.mpr hi
    rw [hS'def] at hi'
    exact (Finset.mem_filter.mp hi').2
  have hlb := pandora_threshold_policy_lower_bound inst r hr t ht order hnd hpos
  have hsumord : ∑ i ∈ order.toFinset, pandora_capped_surplus inst r i t = t := by
    rw [htof, hS'sum]
  rw [hsumord] at hlb
  have hEU : t ≤ expectedUtilityDUS inst (pandora_threshold_policy order t) := by
    simpa using hlb
  have hvpa := pandora_threshold_policy_valid inst t order hnd hdl
  refine ⟨pandora_threshold_policy order t, hvpa.1, hvpa.2, ?_⟩
  have hopt : optDUS inst ≤ 2 * t := by
    rw [optDUS]
    refine Real.iSup_le (fun π => ?_) (by linarith)
    refine Real.iSup_le (fun hπ => ?_) (by linarith)
    obtain ⟨S₀, hS₀feas, hS₀b⟩ := op184_partially_adaptive_half_approximation_lemma1 inst r hr t ht π hπ
    have h := hSmax S₀ hS₀feas
    linarith
  linarith
