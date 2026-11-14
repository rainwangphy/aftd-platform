import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCut20SharpExample
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_cut20_sharp_example_certificate

Topic: graphs   Node: c700e0d04e22

Provenance: helper lemma. Extension of https://arxiv.org/abs/2205.10826, Figure 3.2; experiments 26197 and 26198.

In the displayed 20-vertex graph, the first 13 vertices all have outdegree seven, exactly 20 arcs leave that set, and it contains no two disjoint directed cycles. Moreover, every nonempty induced subset of minimum outdegree at least two has at least three vertices of internal outdegree below three.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private instance in833_cut20_scratch_decAdj : DecidableRel digraph_cut20_sharp_example.Adj := by
  unfold digraph_cut20_sharp_example
  infer_instance

private theorem in833_cycle_successor {α : Type} [DecidableEq α]
    (D : Digraph α) (C : Finset α) (hC : digraph_directed_cycle_on D C) :
    C.Nonempty ∧ ∀ v ∈ C, ∃ w ∈ C, D.Adj v w := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, hhead, hlast, hclose⟩ := hC
  have ha : a ∈ l := by
    cases l with
    | nil => simp at hhead
    | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      simp
  have haC : a ∈ C := by rw [← hset, List.mem_toFinset]; exact ha
  refine ⟨⟨a, haC⟩, ?_⟩
  intro v hv
  have hvL : v ∈ l := by rw [← hset, List.mem_toFinset] at hv; exact hv
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hvL
  by_cases his : i + 1 < l.length
  · refine ⟨l[i+1], ?_, ?_⟩
    · rw [← hset, List.mem_toFinset]
      exact List.getElem_mem _
    · rw [← heq]
      exact hchain.getElem i his
  · have hilast : i = l.length - 1 := by omega
    have hidx : l[i]? = some b := by
      simpa [List.getLast?_eq_getElem?, ← hilast] using hlast
    have heqB : l[i] = b := by simpa [List.getElem?_eq_getElem hi] using hidx
    refine ⟨a, haC, ?_⟩
    rw [← heq, heqB]
    exact hclose

private theorem in833_cut20_cycle_no_apex_core
    (C : Finset (Fin 20)) (hC : digraph_directed_cycle_on digraph_cut20_sharp_example C)
    (hB : ∀ v ∈ C, v.val < 13) (h7 : (7 : Fin 20) ∉ C) :
    ∀ v : Fin 20, v.val < 7 → v ∈ C := by
  obtain ⟨hne, hs⟩ := in833_cycle_successor digraph_cut20_sharp_example C hC
  have h8 : (8 : Fin 20) ∉ C := by
    intro hv
    obtain ⟨w, hw, hadj⟩ := hs 8 hv
    have hwB := hB w hw
    have heq : w.val = 7 := by
      change ((8 : Fin 20).val < 7 ∧ (w.val = ((8 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        ((8 : Fin 20).val = 7 ∧ w.val < 7) ∨
        (8 ≤ (8 : Fin 20).val ∧ (8 : Fin 20).val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (8 : Fin 20).val) ∨ (13 ≤ w.val ∧ (8 : Fin 20).val + w.val < 27))) at hadj
      omega
    apply h7
    have h : w = (7 : Fin 20) := Fin.ext heq
    simpa [h] using hw
  have h9 : (9 : Fin 20) ∉ C := by
    intro hv
    obtain ⟨w, hw, hadj⟩ := hs 9 hv
    have hwB := hB w hw
    have hw8 : w.val ≠ 8 := by
      intro heq
      apply h8
      have h : w = (8 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have heq : w.val = 7 := by
      change ((9 : Fin 20).val < 7 ∧ (w.val = ((9 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        ((9 : Fin 20).val = 7 ∧ w.val < 7) ∨
        (8 ≤ (9 : Fin 20).val ∧ (9 : Fin 20).val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (9 : Fin 20).val) ∨ (13 ≤ w.val ∧ (9 : Fin 20).val + w.val < 27))) at hadj
      omega
    apply h7
    have h : w = (7 : Fin 20) := Fin.ext heq
    simpa [h] using hw
  have h10 : (10 : Fin 20) ∉ C := by
    intro hv
    obtain ⟨w, hw, hadj⟩ := hs 10 hv
    have hwB := hB w hw
    have hw8 : w.val ≠ 8 := by
      intro heq
      apply h8
      have h : w = (8 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw9 : w.val ≠ 9 := by
      intro heq
      apply h9
      have h : w = (9 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have heq : w.val = 7 := by
      change ((10 : Fin 20).val < 7 ∧ (w.val = ((10 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        ((10 : Fin 20).val = 7 ∧ w.val < 7) ∨
        (8 ≤ (10 : Fin 20).val ∧ (10 : Fin 20).val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (10 : Fin 20).val) ∨ (13 ≤ w.val ∧ (10 : Fin 20).val + w.val < 27))) at hadj
      omega
    apply h7
    have h : w = (7 : Fin 20) := Fin.ext heq
    simpa [h] using hw
  have h11 : (11 : Fin 20) ∉ C := by
    intro hv
    obtain ⟨w, hw, hadj⟩ := hs 11 hv
    have hwB := hB w hw
    have hw8 : w.val ≠ 8 := by
      intro heq
      apply h8
      have h : w = (8 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw9 : w.val ≠ 9 := by
      intro heq
      apply h9
      have h : w = (9 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw10 : w.val ≠ 10 := by
      intro heq
      apply h10
      have h : w = (10 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have heq : w.val = 7 := by
      change ((11 : Fin 20).val < 7 ∧ (w.val = ((11 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        ((11 : Fin 20).val = 7 ∧ w.val < 7) ∨
        (8 ≤ (11 : Fin 20).val ∧ (11 : Fin 20).val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (11 : Fin 20).val) ∨ (13 ≤ w.val ∧ (11 : Fin 20).val + w.val < 27))) at hadj
      omega
    apply h7
    have h : w = (7 : Fin 20) := Fin.ext heq
    simpa [h] using hw
  have h12 : (12 : Fin 20) ∉ C := by
    intro hv
    obtain ⟨w, hw, hadj⟩ := hs 12 hv
    have hwB := hB w hw
    have hw8 : w.val ≠ 8 := by
      intro heq
      apply h8
      have h : w = (8 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw9 : w.val ≠ 9 := by
      intro heq
      apply h9
      have h : w = (9 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw10 : w.val ≠ 10 := by
      intro heq
      apply h10
      have h : w = (10 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have hw11 : w.val ≠ 11 := by
      intro heq
      apply h11
      have h : w = (11 : Fin 20) := Fin.ext heq
      simpa [h] using hw
    have heq : w.val = 7 := by
      change ((12 : Fin 20).val < 7 ∧ (w.val = ((12 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        ((12 : Fin 20).val = 7 ∧ w.val < 7) ∨
        (8 ≤ (12 : Fin 20).val ∧ (12 : Fin 20).val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (12 : Fin 20).val) ∨ (13 ≤ w.val ∧ (12 : Fin 20).val + w.val < 27))) at hadj
      omega
    apply h7
    have h : w = (7 : Fin 20) := Fin.ext heq
    simpa [h] using hw
  have hcore : ∀ v ∈ C, v.val < 7 := by
    intro v hv
    have hvB := hB v hv
    fin_cases v <;> norm_num at hvB <;> norm_num <;>
      first | exact False.elim (h7 (by simpa using hv)) | exact False.elim (h8 (by simpa using hv)) | exact False.elim (h9 (by simpa using hv)) | exact False.elim (h10 (by simpa using hv)) | exact False.elim (h11 (by simpa using hv)) | exact False.elim (h12 (by simpa using hv))
  have hstep (v : Fin 20) (hv : v ∈ C) :
      (⟨(v.val + 1) % 7, by have := Nat.mod_lt (v.val+1) (by norm_num : 0 < 7); omega⟩ : Fin 20) ∈ C := by
    obtain ⟨w, hw, hadj⟩ := hs v hv
    have hvcore := hcore v hv
    have hwcore := hcore w hw
    have heq : w.val = (v.val + 1) % 7 := by
      change (v.val < 7 ∧ (w.val = (v.val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        (v.val = 7 ∧ w.val < 7) ∨
        (8 ≤ v.val ∧ v.val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < v.val) ∨ (13 ≤ w.val ∧ v.val + w.val < 27))) at hadj
      omega
    have hw' : w = (⟨(v.val + 1) % 7, by have := Nat.mod_lt (v.val+1) (by norm_num : 0 < 7); omega⟩ : Fin 20) := Fin.ext heq
    simpa [← hw'] using hw
  have h0 : (0 : Fin 20) ∈ C := by
    by_contra h0
    have h6 : (6 : Fin 20) ∉ C := by
      intro h
      apply h0
      simpa using hstep 6 h
    have h5 : (5 : Fin 20) ∉ C := by
      intro h
      apply h6
      simpa using hstep 5 h
    have h4 : (4 : Fin 20) ∉ C := by
      intro h
      apply h5
      simpa using hstep 4 h
    have h3 : (3 : Fin 20) ∉ C := by
      intro h
      apply h4
      simpa using hstep 3 h
    have h2 : (2 : Fin 20) ∉ C := by
      intro h
      apply h3
      simpa using hstep 2 h
    have h1 : (1 : Fin 20) ∉ C := by
      intro h
      apply h2
      simpa using hstep 1 h
    obtain ⟨v,hv⟩ := hne
    have hvcore := hcore v hv
    fin_cases v <;> norm_num at hvcore <;>
      first | exact h0 (by simpa using hv) | exact h1 (by simpa using hv) | exact h2 (by simpa using hv) | exact h3 (by simpa using hv) | exact h4 (by simpa using hv) | exact h5 (by simpa using hv) | exact h6 (by simpa using hv)
  have h1 : (1 : Fin 20) ∈ C := by simpa using hstep 0 h0
  have h2 : (2 : Fin 20) ∈ C := by simpa using hstep 1 h1
  have h3 : (3 : Fin 20) ∈ C := by simpa using hstep 2 h2
  have h4 : (4 : Fin 20) ∈ C := by simpa using hstep 3 h3
  have h5 : (5 : Fin 20) ∈ C := by simpa using hstep 4 h4
  have h6 : (6 : Fin 20) ∈ C := by simpa using hstep 5 h5
  intro v hv
  fin_cases v <;> norm_num at hv <;>
    first | simpa using h0 | simpa using h1 | simpa using h2 | simpa using h3 | simpa using h4 | simpa using h5 | simpa using h6

private theorem in833_cut20_cycle_has_core
    (C : Finset (Fin 20)) (hC : digraph_directed_cycle_on digraph_cut20_sharp_example C)
    (hB : ∀ v ∈ C, v.val < 13) :
    ∃ v ∈ C, v.val < 7 := by
  by_cases h7 : (7 : Fin 20) ∈ C
  · obtain ⟨_, hs⟩ := in833_cycle_successor digraph_cut20_sharp_example C hC
    obtain ⟨w,hw,hadj⟩ := hs 7 h7
    refine ⟨w,hw,?_⟩
    change ((7 : Fin 20).val < 7 ∧ (w.val = ((7 : Fin 20).val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
      ((7 : Fin 20).val = 7 ∧ w.val < 7) ∨
      (8 ≤ (7 : Fin 20).val ∧ (7 : Fin 20).val < 13 ∧
        (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < (7 : Fin 20).val) ∨ (13 ≤ w.val ∧ (7 : Fin 20).val + w.val < 27))) at hadj
    omega
  · exact ⟨0, in833_cut20_cycle_no_apex_core C hC hB h7 0 (by norm_num), by norm_num⟩

private theorem in833_cut20_no_two :
    let D := digraph_cut20_sharp_example
    let B : Finset (Fin 20) := Finset.univ.filter fun v => v.val < 13
    ¬ ∃ c : Fin 2 → Finset (Fin 20),
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)) := by
  dsimp only
  intro ⟨c,hc,hdis⟩
  have hdis01 : Disjoint (c 0) (c 1) := hdis (by decide)
  have hB (i : Fin 2) : ∀ v ∈ c i, v.val < 13 := by
    intro v hv
    have h := (hc i).1 hv
    simpa using h
  by_cases h70 : (7 : Fin 20) ∈ c 0
  · by_cases h71 : (7 : Fin 20) ∈ c 1
    · exact (Finset.disjoint_left.mp hdis01) h70 h71
    · obtain ⟨v,hv,hv7⟩ := in833_cut20_cycle_has_core (c 0) (hc 0).2 (hB 0)
      have hv' := in833_cut20_cycle_no_apex_core (c 1) (hc 1).2 (hB 1) h71 v hv7
      exact (Finset.disjoint_left.mp hdis01) hv hv'
  · obtain ⟨v,hv,hv7⟩ := in833_cut20_cycle_has_core (c 1) (hc 1).2 (hB 1)
    have hv' := in833_cut20_cycle_no_apex_core (c 0) (hc 0).2 (hB 0) h70 v hv7
    exact (Finset.disjoint_left.mp hdis01) hv' hv

private theorem in833_cut20_robust :
    let D := digraph_cut20_sharp_example
    ∀ T : Finset (Fin 20), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      3 ≤ (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card := by
  dsimp only
  intro T hne hdeg
  have hsink (v : Fin 20) (hv : v ∈ T) : v.val < 13 := by
    by_contra h
    have hfalse : ∀ w : Fin 20, ¬ digraph_cut20_sharp_example.Adj v w := by
      intro w
      change ¬ ((v.val < 7 ∧ (w.val = (v.val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
        (v.val = 7 ∧ w.val < 7) ∨
        (8 ≤ v.val ∧ v.val < 13 ∧
          (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < v.val) ∨ (13 ≤ w.val ∧ v.val + w.val < 27))))
      omega
    have he : T.filter (fun w => digraph_cut20_sharp_example.Adj v w) = ∅ := by
      ext w
      simp [hfalse w]
    have hh := hdeg v hv
    rw [he] at hh
    simp at hh
  have hbound (v : Fin 20) (hv : v ∈ T) : v.val < 8 := by
    by_contra hh
    let U := T.filter fun w => 8 ≤ w.val
    have hU : U.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, by omega⟩⟩
    let u := U.min' hU
    have hu : u ∈ U := Finset.min'_mem U hU
    have huT : u ∈ T := (Finset.mem_filter.mp hu).1
    have hu8 : 8 ≤ u.val := (Finset.mem_filter.mp hu).2
    have hu13 := hsink u huT
    have hsub : T.filter (fun w => digraph_cut20_sharp_example.Adj u w) ⊆ {7} := by
      intro w hw
      have hwT : w ∈ T := (Finset.mem_filter.mp hw).1
      have hadj := (Finset.mem_filter.mp hw).2
      have hw13 := hsink w hwT
      have hnot : ¬ (8 ≤ w.val ∧ w.val < u.val) := by
        intro h
        have hwU : w ∈ U := Finset.mem_filter.mpr ⟨hwT,h.1⟩
        have hmin := Finset.min'_le U w hwU
        have : u.val ≤ w.val := hmin
        omega
      have heq : w.val = 7 := by
        change (u.val < 7 ∧ (w.val = (u.val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
          (u.val = 7 ∧ w.val < 7) ∨
          (8 ≤ u.val ∧ u.val < 13 ∧
            (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < u.val) ∨ (13 ≤ w.val ∧ u.val + w.val < 27))) at hadj
        omega
      have : w = (7 : Fin 20) := Fin.ext heq
      simpa [this]
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle
    have hge := hdeg u huT
    omega
  have hcard : 2 ≤ T.card := by
    obtain ⟨v,hv⟩ := hne
    have hh := hdeg v hv
    have hsub := Finset.card_le_card (Finset.filter_subset (fun w => digraph_cut20_sharp_example.Adj v w) T)
    omega
  have hcore : ∃ v ∈ T, v.val < 7 := by
    by_contra hh
    push_neg at hh
    have hsub : T ⊆ {7} := by
      intro v hv
      have h1 := hbound v hv
      have h2 := hh v hv
      have : v = (7 : Fin 20) := Fin.ext (by omega)
      simpa [this]
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle
    omega
  have hstep (v : Fin 20) (hv : v ∈ T) (hv7 : v.val < 7) :
      (7 : Fin 20) ∈ T ∧
      (⟨(v.val + 1) % 7, by have := Nat.mod_lt (v.val+1) (by norm_num : 0 < 7); omega⟩ : Fin 20) ∈ T := by
    let next : Fin 20 := ⟨(v.val+1)%7, by have := Nat.mod_lt (v.val+1) (by norm_num : 0 < 7); omega⟩
    have hout : ∀ w ∈ T, digraph_cut20_sharp_example.Adj v w → w = 7 ∨ w = next := by
      intro w hw hadj
      have hw8 := hbound w hw
      have hval : w.val = 7 ∨ w.val = (v.val+1)%7 := by
        change (v.val < 7 ∧ (w.val = (v.val + 1) % 7 ∨ w.val = 7 ∨ (8 ≤ w.val ∧ w.val < 13))) ∨
          (v.val = 7 ∧ w.val < 7) ∨
          (8 ≤ v.val ∧ v.val < 13 ∧
            (w.val = 7 ∨ (8 ≤ w.val ∧ w.val < v.val) ∨ (13 ≤ w.val ∧ v.val + w.val < 27))) at hadj
        omega
      rcases hval with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    have hfilter := hdeg v hv
    constructor
    · by_contra h7
      have hsub : T.filter (fun w => digraph_cut20_sharp_example.Adj v w) ⊆ {next} := by
        intro w hw
        obtain ⟨hwT,hadj⟩ := Finset.mem_filter.mp hw
        rcases hout w hwT hadj with heq | heq
        · subst w; contradiction
        · simpa [heq]
      have hh := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hh
      omega
    · by_contra hn
      have hsub : T.filter (fun w => digraph_cut20_sharp_example.Adj v w) ⊆ {7} := by
        intro w hw
        obtain ⟨hwT,hadj⟩ := Finset.mem_filter.mp hw
        rcases hout w hwT hadj with heq | heq
        · simpa [heq]
        · subst w; contradiction
      have hh := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hh
      omega
  have h0 : (0 : Fin 20) ∈ T := by
    by_contra h0
    have h6 : (6 : Fin 20) ∉ T := by
      intro h
      apply h0
      simpa using (hstep 6 h (by norm_num)).2
    have h5 : (5 : Fin 20) ∉ T := by
      intro h
      apply h6
      simpa using (hstep 5 h (by norm_num)).2
    have h4 : (4 : Fin 20) ∉ T := by
      intro h
      apply h5
      simpa using (hstep 4 h (by norm_num)).2
    have h3 : (3 : Fin 20) ∉ T := by
      intro h
      apply h4
      simpa using (hstep 3 h (by norm_num)).2
    have h2 : (2 : Fin 20) ∉ T := by
      intro h
      apply h3
      simpa using (hstep 2 h (by norm_num)).2
    have h1 : (1 : Fin 20) ∉ T := by
      intro h
      apply h2
      simpa using (hstep 1 h (by norm_num)).2
    obtain ⟨v,hv,hv7⟩ := hcore
    fin_cases v <;> norm_num at hv7 <;>
      first | exact h0 (by simpa using hv) | exact h1 (by simpa using hv) | exact h2 (by simpa using hv) | exact h3 (by simpa using hv) | exact h4 (by simpa using hv) | exact h5 (by simpa using hv) | exact h6 (by simpa using hv)
  have h1 : (1 : Fin 20) ∈ T := by simpa using (hstep 0 h0 (by norm_num)).2
  have h2 : (2 : Fin 20) ∈ T := by simpa using (hstep 1 h1 (by norm_num)).2
  have h3 : (3 : Fin 20) ∈ T := by simpa using (hstep 2 h2 (by norm_num)).2
  have h4 : (4 : Fin 20) ∈ T := by simpa using (hstep 3 h3 (by norm_num)).2
  have h5 : (5 : Fin 20) ∈ T := by simpa using (hstep 4 h4 (by norm_num)).2
  have h6 : (6 : Fin 20) ∈ T := by simpa using (hstep 5 h5 (by norm_num)).2
  have h7 : (7 : Fin 20) ∈ T := (hstep 0 h0 (by norm_num)).1
  have hT : T = Finset.univ.filter (fun v : Fin 20 => v.val < 8) := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbound v hv⟩
    · intro hv
      have hv' := (Finset.mem_filter.mp hv).2
      fin_cases v <;> norm_num at hv' <;>
        first | simpa using h0 | simpa using h1 | simpa using h2 | simpa using h3 | simpa using h4 | simpa using h5 | simpa using h6 | simpa using h7
  rw [hT]
  decide

private theorem in833_cut20_degree :
    let D := digraph_cut20_sharp_example
    let B : Finset (Fin 20) := Finset.univ.filter fun v => v.val < 13
    ∀ v ∈ B, (Finset.univ.filter fun w => D.Adj v w).card = 7 := by
  decide

private theorem in833_cut20_boundary :
    let D := digraph_cut20_sharp_example
    let B : Finset (Fin 20) := Finset.univ.filter fun v => v.val < 13
    (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20 := by
  decide

theorem digraph_cut20_sharp_example_certificate :
    let D := digraph_cut20_sharp_example
    let B : Finset (Fin 20) := Finset.univ.filter fun v => v.val < 13
    (∀ v ∈ B, (Finset.univ.filter fun w => D.Adj v w).card = 7) ∧
    (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20 ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 20),
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) ∧
    (∀ T : Finset (Fin 20), T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      3 ≤ (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card) := by
  exact ⟨in833_cut20_degree, in833_cut20_boundary, in833_cut20_no_two, in833_cut20_robust⟩
