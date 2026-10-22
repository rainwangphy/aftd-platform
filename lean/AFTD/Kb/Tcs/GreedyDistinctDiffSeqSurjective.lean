import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyDistinctDiffSeq
import AFTD.Kb.Tcs.GreedyDistinctDiffNext
import AFTD.Kb.Tcs.GreedyDistinctDiffHistory

/-!
# greedy_distinct_diff_seq_surjective

Topic: combinatorics   Node: c9f7cf09d0a0

Provenance: original. Related work: List entry OP-203, a question proposed here from arXiv:2610.15860 (A note on the Slater–Vélez permutation), which works with the start a₁ = 1, a₂ = 2, for which Slater and Vélez (1977) proved the sequence is a permutation; the paper does not ask about other starts.

Conjecture: for any distinct positive integers a₁, a₂, the greedy sequence with distinct consecutive differences started at a₁, a₂ takes every positive integer as a value (it is a permutation of the positive integers).
-/

noncomputable def greedy_distinct_diff_seq_surjective_gd (a₁ a₂ : ℕ) (i : ℕ) : ℕ :=
  Int.natAbs (((greedy_distinct_diff_seq a₁ a₂ (i+1) : ℤ)) -
    ((greedy_distinct_diff_seq a₁ a₂ i : ℤ)))

noncomputable def greedy_distinct_diff_seq_surjective_difflist (a₁ a₂ : ℕ) (n : ℕ) : List ℕ :=
  ((greedy_distinct_diff_history a₁ a₂ n).zip
    (greedy_distinct_diff_history a₁ a₂ n).tail).map
    (fun p => Int.natAbs ((p.1:ℤ) - (p.2:ℤ)))

lemma greedy_distinct_diff_seq_surjective_hist_eq (a₁ a₂ : ℕ) (n : ℕ) :
    greedy_distinct_diff_history a₁ a₂ n
      = (List.range (n+2)).reverse.map (greedy_distinct_diff_seq a₁ a₂) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [greedy_distinct_diff_history]
    rw [show (n+1)+2 = (n+2)+1 from by ring]
    rw [List.range_succ, List.reverse_append, List.reverse_singleton]
    simp only [List.map_cons, List.singleton_append]
    have hnext : greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n)
        = greedy_distinct_diff_seq a₁ a₂ (n+2) := by
      simp [greedy_distinct_diff_seq, greedy_distinct_diff_history]
    rw [hnext, ih]

lemma greedy_distinct_diff_seq_surjective_hist_mem (a₁ a₂ : ℕ) (n c : ℕ) :
    c ∈ greedy_distinct_diff_history a₁ a₂ n ↔
      ∃ i, i ≤ n+1 ∧ greedy_distinct_diff_seq a₁ a₂ i = c := by
  rw [greedy_distinct_diff_seq_surjective_hist_eq, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [List.mem_reverse, List.mem_range] at ha
    exact ⟨a, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rw [List.mem_reverse, List.mem_range]
    omega

lemma greedy_distinct_diff_seq_surjective_hist_head_eq (a₁ a₂ : ℕ) (n : ℕ) :
    greedy_distinct_diff_history a₁ a₂ n
      = greedy_distinct_diff_seq a₁ a₂ (n+1) ::
        (List.range (n+1)).reverse.map (greedy_distinct_diff_seq a₁ a₂) := by
  rw [greedy_distinct_diff_seq_surjective_hist_eq]
  rw [show n+2 = (n+1)+1 from rfl, List.range_succ, List.reverse_append,
      List.reverse_singleton]
  simp

lemma greedy_distinct_diff_seq_surjective_difflist_cons (a₁ a₂ : ℕ) (n : ℕ) :
    greedy_distinct_diff_seq_surjective_difflist a₁ a₂ (n+1)
      = greedy_distinct_diff_seq_surjective_gd a₁ a₂ (n+1) ::
        greedy_distinct_diff_seq_surjective_difflist a₁ a₂ n := by
  unfold greedy_distinct_diff_seq_surjective_difflist greedy_distinct_diff_seq_surjective_gd
  have hnext : greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n)
      = greedy_distinct_diff_seq a₁ a₂ (n+2) := by
    simp [greedy_distinct_diff_seq, greedy_distinct_diff_history]
  have hh : greedy_distinct_diff_history a₁ a₂ (n+1)
      = greedy_distinct_diff_seq a₁ a₂ (n+2) ::
        greedy_distinct_diff_history a₁ a₂ n := by
    rw [show greedy_distinct_diff_history a₁ a₂ (n+1)
        = greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n) ::
          greedy_distinct_diff_history a₁ a₂ n from rfl, hnext]
  rw [hh, List.tail_cons]
  rw [greedy_distinct_diff_seq_surjective_hist_head_eq a₁ a₂ n]
  rw [List.zip_cons_cons, List.tail_cons]
  simp only [List.map_cons]

lemma greedy_distinct_diff_seq_surjective_difflist_zero (a₁ a₂ : ℕ) :
    greedy_distinct_diff_seq_surjective_difflist a₁ a₂ 0
      = [greedy_distinct_diff_seq_surjective_gd a₁ a₂ 0] := by
  unfold greedy_distinct_diff_seq_surjective_difflist greedy_distinct_diff_seq_surjective_gd
  rfl

lemma greedy_distinct_diff_seq_surjective_difflist_mem (a₁ a₂ : ℕ) (n e : ℕ) :
    e ∈ greedy_distinct_diff_seq_surjective_difflist a₁ a₂ n ↔
      ∃ i, i < n+1 ∧ e = greedy_distinct_diff_seq_surjective_gd a₁ a₂ i := by
  induction n with
  | zero =>
    rw [greedy_distinct_diff_seq_surjective_difflist_zero, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, by omega, h⟩
    · rintro ⟨i, hi, he⟩
      rw [show i = 0 by omega] at he
      exact he
  | succ n ih =>
    rw [greedy_distinct_diff_seq_surjective_difflist_cons, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, he⟩)
      · exact ⟨n+1, by omega, h⟩
      · exact ⟨i, by omega, he⟩
    · rintro ⟨i, hi, he⟩
      rcases Nat.lt_or_ge i (n+1) with h' | h'
      · exact Or.inr ⟨i, h', he⟩
      · have hi' : i = n+1 := by omega
        rw [hi'] at he
        exact Or.inl he

lemma greedy_distinct_diff_seq_surjective_greedy_next_nonempty (l : List ℕ) :
    {c : ℕ | 0 < c ∧ c ∉ l ∧
      Int.natAbs ((c:ℤ) - ((l.headD 0):ℤ)) ∉
        (l.zip l.tail).map (fun p => Int.natAbs ((p.1:ℤ) - (p.2:ℤ)))}.Nonempty := by
  set ds := (l.zip l.tail).map (fun p => Int.natAbs ((p.1:ℤ) - (p.2:ℤ))) with hds
  refine ⟨l.sum + ds.sum + l.headD 0 + 1, ?_, ?_, ?_⟩
  · omega
  · intro hmem; have h := List.le_sum_of_mem hmem; omega
  · intro hmem
    have hle : l.headD 0 ≤ l.sum + ds.sum + l.headD 0 + 1 := by omega
    have hn : Int.natAbs (((l.sum + ds.sum + l.headD 0 + 1:ℕ):ℤ) - ((l.headD 0:ℕ):ℤ))
        = (l.sum + ds.sum + l.headD 0 + 1) - l.headD 0 := by
      have hcast : (((l.sum + ds.sum + l.headD 0 + 1):ℕ):ℤ) - ((l.headD 0:ℕ):ℤ)
          = (((l.sum + ds.sum + l.headD 0 + 1) - l.headD 0 : ℕ):ℤ) := by
        rw [Nat.cast_sub hle]
      rw [hcast, Int.natAbs_natCast]
    rw [hn] at hmem
    have h := List.le_sum_of_mem hmem; omega

lemma greedy_distinct_diff_seq_surjective_spec (a₁ a₂ : ℕ) (n : ℕ) :
    greedy_distinct_diff_seq a₁ a₂ (n+2) =
        greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n) ∧
    0 < greedy_distinct_diff_seq a₁ a₂ (n+2) ∧
    greedy_distinct_diff_seq a₁ a₂ (n+2) ∉
        (Finset.range (n+2)).image (greedy_distinct_diff_seq a₁ a₂) ∧
    greedy_distinct_diff_seq_surjective_gd a₁ a₂ (n+1) ∉ (Finset.range (n+1)).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) ∧
    (∀ c, 0 < c →
      c ∉ (Finset.range (n+2)).image (greedy_distinct_diff_seq a₁ a₂) →
      Int.natAbs (((c:ℤ) - ((greedy_distinct_diff_seq a₁ a₂ (n+1)):ℤ))) ∉
        (Finset.range (n+1)).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) →
      greedy_distinct_diff_seq a₁ a₂ (n+2) ≤ c) := by
  set x := greedy_distinct_diff_seq a₁ a₂ with hxdef
  have hx : x (n+2) = greedy_distinct_diff_next (greedy_distinct_diff_history a₁ a₂ n) := by
    rw [hxdef]; simp [greedy_distinct_diff_seq, greedy_distinct_diff_history]
  set l := greedy_distinct_diff_history a₁ a₂ n with hl
  set S := {c : ℕ | 0 < c ∧ c ∉ l ∧
      Int.natAbs ((c:ℤ) - ((l.headD 0):ℤ)) ∉
        (l.zip l.tail).map (fun p => Int.natAbs ((p.1:ℤ) - (p.2:ℤ)))} with hS
  have hheadD : l.headD 0 = x (n+1) := by rw [hxdef]; rfl
  have hne : S.Nonempty := greedy_distinct_diff_seq_surjective_greedy_next_nonempty l
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  have hxS : x (n+2) = sInf S := by rw [hx]; rfl
  have hmemV : ∀ c, (c ∈ l ↔ c ∈ (Finset.range (n+2)).image x) := by
    intro c
    rw [hl, hxdef, greedy_distinct_diff_seq_surjective_hist_mem]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
  have hmemD : ∀ e, (e ∈ greedy_distinct_diff_seq_surjective_difflist a₁ a₂ n ↔
      e ∈ (Finset.range (n+1)).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂)) := by
    intro e
    rw [greedy_distinct_diff_seq_surjective_difflist_mem]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h.symm⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h.symm⟩
  refine ⟨hx, ?_, ?_, ?_, ?_⟩
  · rw [hxS]; exact hmem.1
  · rw [← hmemV, hxS]; exact hmem.2.1
  · rw [← hmemD]
    have heq : greedy_distinct_diff_seq_surjective_gd a₁ a₂ (n+1)
        = Int.natAbs ((((sInf S : ℕ)):ℤ) - ((l.headD 0):ℤ)) := by
      unfold greedy_distinct_diff_seq_surjective_gd
      rw [← hxdef, hxS, hheadD]
    rw [heq]
    exact hmem.2.2
  · intro c hc0 hcV hcD
    have hcS : c ∈ S := by
      refine ⟨hc0, ?_, ?_⟩
      · rw [hmemV]; exact hcV
      · show Int.natAbs ((c:ℤ) - ((x (n+1)):ℤ)) ∉ greedy_distinct_diff_seq_surjective_difflist a₁ a₂ n
        rw [hmemD]; exact hcD
    have hle := Nat.sInf_le hcS
    rw [← hxS] at hle
    exact hle

lemma greedy_distinct_diff_seq_surjective_natAbs_sub_nat {a b : ℕ} (h : a ≤ b) :
    Int.natAbs ((b:ℤ) - (a:ℤ)) = b - a := by
  have hcast : ((b:ℤ) - (a:ℤ)) = ((b - a : ℕ):ℤ) := by
    rw [Nat.cast_sub h]
  rw [hcast, Int.natAbs_natCast]

lemma greedy_distinct_diff_seq_surjective_natAbs_v_sub {v n : ℕ} (h : v ≤ n) :
    Int.natAbs ((v:ℤ) - (n:ℤ)) = n - v := by
  have e : ((v:ℤ) - (n:ℤ)) = -(((n:ℤ) - (v:ℤ))) := by ring
  rw [e, Int.natAbs_neg, greedy_distinct_diff_seq_surjective_natAbs_sub_nat h]

lemma greedy_distinct_diff_seq_surjective_natAbs_sub_le {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    Int.natAbs ((b:ℤ) - (a:ℤ)) ≤ M := by
  rcases le_total a b with hab | hab
  · rw [greedy_distinct_diff_seq_surjective_natAbs_sub_nat hab]; omega
  · rw [show Int.natAbs ((b:ℤ) - (a:ℤ)) = Int.natAbs ((a:ℤ) - (b:ℤ)) from by
        rw [← Int.natAbs_neg]; congr 1; ring]
    rw [greedy_distinct_diff_seq_surjective_natAbs_sub_nat hab]; omega

lemma greedy_distinct_diff_seq_surjective_spec_one (a₁ a₂ : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    0 < greedy_distinct_diff_seq a₁ a₂ (k+1) ∧
    greedy_distinct_diff_seq a₁ a₂ (k+1) ∉ (Finset.range (k+1)).image (greedy_distinct_diff_seq a₁ a₂) ∧
    greedy_distinct_diff_seq_surjective_gd a₁ a₂ k ∉ (Finset.range k).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) ∧
    (∀ c, 0 < c → c ∉ (Finset.range (k+1)).image (greedy_distinct_diff_seq a₁ a₂) →
      Int.natAbs (((c:ℤ) - ((greedy_distinct_diff_seq a₁ a₂ k):ℤ))) ∉ (Finset.range k).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) →
      greedy_distinct_diff_seq a₁ a₂ (k+1) ≤ c) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := greedy_distinct_diff_seq_surjective_spec a₁ a₂ (k-1)
  have e1 : k - 1 + 2 = k + 1 := by omega
  have e2 : k - 1 + 1 = k := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1] at h2; exact h2
  · rw [e1] at h3; exact h3
  · rw [e2] at h4; exact h4
  · intro c hc hcv hcd
    have h := h5 c hc (by rw [e1]; exact hcv) (by rw [e2]; exact hcd)
    rw [e1] at h; exact h

theorem greedy_distinct_diff_seq_surjective (a₁ a₂ : ℕ) (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (h : a₁ ≠ a₂) : ∀ v, 0 < v → ∃ n, greedy_distinct_diff_seq a₁ a₂ n = v := by
  intro v hv
  by_contra hcon
  push_neg at hcon
  set x := greedy_distinct_diff_seq a₁ a₂ with hxdef
  set D : ℕ → Finset ℕ := fun k => (Finset.range k).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) with hDdef
  have hx0 : x 0 = a₁ := by rw [hxdef]; rfl
  have hx1 : x 1 = a₂ := by rw [hxdef]; rfl
  have hvmiss : ∀ m, v ∉ (Finset.range m).image x := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, -, hi⟩ := hm
    exact hcon i hi
  have hA : ∀ k, 1 ≤ k → x (k+1) > v → Int.natAbs ((v:ℤ) - ((x k:ℤ))) ∈ D k := by
    intro k hk hgt
    by_contra hnot
    have h4 := (greedy_distinct_diff_seq_surjective_spec_one a₁ a₂ k hk).2.2.2
    have hle : x (k+1) ≤ v := h4 v hv (hvmiss (k+1)) hnot
    exact absurd hle (not_le.mpr hgt)
  have hA' : ∀ k, 1 ≤ k → x k > v → x (k+1) > v → x k - v ∈ D k := by
    intro k hk hxk hgt
    have hh := hA k hk hgt
    rw [show Int.natAbs ((v:ℤ) - ((x k:ℤ))) = x k - v from greedy_distinct_diff_seq_surjective_natAbs_v_sub (le_of_lt hxk)] at hh
    exact hh
  have hDsucc : ∀ k, D (k+1) = D k ∪ {greedy_distinct_diff_seq_surjective_gd a₁ a₂ k} := by
    intro k
    show (Finset.range (k+1)).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂)
        = (Finset.range k).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂) ∪ {greedy_distinct_diff_seq_surjective_gd a₁ a₂ k}
    rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq, Finset.union_comm]
  have hB : ∀ k, 1 ≤ k → x k > v → x (k+1) > v → x (k+2) > v →
      greedy_distinct_diff_seq_surjective_gd a₁ a₂ k ≤ (D k).sup id := by
    intro k hk hx1 hx2 hx3
    have ha : x k - v ∈ D k := hA' k hk hx1 hx2
    have hb : x (k+1) - v ∈ D (k+1) := hA' (k+1) (by omega) hx2 hx3
    have hapos : 0 < x k - v := by omega
    have hd_eq : greedy_distinct_diff_seq_surjective_gd a₁ a₂ k
        = Int.natAbs (((x (k+1) - v : ℕ):ℤ) - ((x k - v : ℕ):ℤ)) := by
      unfold greedy_distinct_diff_seq_surjective_gd
      congr 1
      have e1 : ((x (k+1) - v : ℕ):ℤ) = (x (k+1):ℤ) - (v:ℤ) := Nat.cast_sub (le_of_lt hx2)
      have e2 : ((x k - v : ℕ):ℤ) = (x k:ℤ) - (v:ℤ) := Nat.cast_sub (le_of_lt hx1)
      rw [e1, e2]; ring
    have hb' : x (k+1) - v ∈ D k ∪ {greedy_distinct_diff_seq_surjective_gd a₁ a₂ k} := by rw [← hDsucc]; exact hb
    rw [Finset.mem_union, Finset.mem_singleton] at hb'
    rcases hb' with hbD | hbgd
    · rw [hd_eq]
      exact greedy_distinct_diff_seq_surjective_natAbs_sub_le (Finset.le_sup (f := id) ha) (Finset.le_sup (f := id) hbD)
    · have hde : greedy_distinct_diff_seq_surjective_gd a₁ a₂ k
          = Int.natAbs (((greedy_distinct_diff_seq_surjective_gd a₁ a₂ k : ℕ):ℤ) - ((x k - v : ℕ):ℤ)) := by
        rw [hbgd] at hd_eq; exact hd_eq
      rw [hde]
      have haM : x k - v ≤ (D k).sup id := Finset.le_sup (f := id) ha
      by_contra hgt
      push_neg at hgt
      have hle : x k - v ≤ greedy_distinct_diff_seq_surjective_gd a₁ a₂ k := by omega
      rw [greedy_distinct_diff_seq_surjective_natAbs_sub_nat hle] at hde
      omega
  have hx_out : ∀ m, 1 ≤ m → x m ∉ (Finset.range m).image x := by
    intro m hm
    rcases eq_or_lt_of_le hm with hm1 | hm2
    · subst hm1
      intro hmem
      rw [Finset.range_one, Finset.image_singleton, Finset.mem_singleton] at hmem
      rw [hx1, hx0] at hmem
      exact h hmem.symm
    · have hs := (greedy_distinct_diff_seq_surjective_spec_one a₁ a₂ (m-1) (by omega)).2.1
      have e : m - 1 + 1 = m := by omega
      rw [e] at hs
      exact hs
  have hx_ne : ∀ i j, i < j → x i ≠ x j := by
    intro i j hij heq
    have hj : 1 ≤ j := by omega
    have hout := hx_out j hj
    have hin : x i ∈ (Finset.range j).image x := by
      rw [Finset.mem_image]; exact ⟨i, Finset.mem_range.mpr hij, rfl⟩
    exact hout (heq ▸ hin)
  have hinj : Function.Injective x := by
    intro i j heq
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd heq (hx_ne i j hij)
    · exact hij
    · exact absurd heq.symm (hx_ne j i hij)
  have hgd_ne : ∀ i j, i < j → greedy_distinct_diff_seq_surjective_gd a₁ a₂ i ≠ greedy_distinct_diff_seq_surjective_gd a₁ a₂ j := by
    intro i j hij heq
    have hj : 1 ≤ j := by omega
    have hs : greedy_distinct_diff_seq_surjective_gd a₁ a₂ j ∉ D j := (greedy_distinct_diff_seq_surjective_spec_one a₁ a₂ j hj).2.2.1
    have hi : greedy_distinct_diff_seq_surjective_gd a₁ a₂ i ∈ D j := by
      show greedy_distinct_diff_seq_surjective_gd a₁ a₂ i ∈ (Finset.range j).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩
    rw [← heq] at hs
    exact hs hi
  have hDcard : ∀ k, (D k).card = k := by
    intro k
    show ((Finset.range k).image (greedy_distinct_diff_seq_surjective_gd a₁ a₂)).card = k
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj heq
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with hlt | hlt | hlt
    · exact absurd heq (hgd_ne i j hlt)
    · exact hlt
    · exact absurd heq.symm (hgd_ne j i hlt)
  classical
  set idx : ℕ → ℕ := fun m => if hh : ∃ k, x k = m then Classical.choose hh else 0 with hidx
  have hidx_eq : ∀ m k, x k = m → idx m = k := by
    intro m k hk
    have hex : ∃ j, x j = m := ⟨k, hk⟩
    have hchoose : x (Classical.choose hex) = m := Classical.choose_spec hex
    have hck : Classical.choose hex = k := hinj (by rw [hchoose, hk])
    simp only [idx, dif_pos hex, hck]
  have hK : ∃ K, ∀ k, K ≤ k → v < x k := by
    refine ⟨(Finset.range (v+1)).sup idx + 1, ?_⟩
    intro k hk
    by_contra hle
    push_neg at hle
    have hmem : x k ∈ Finset.range (v+1) := Finset.mem_range.mpr (by omega)
    have h1 : idx (x k) ≤ (Finset.range (v+1)).sup idx := Finset.le_sup hmem
    have h2 : idx (x k) = k := hidx_eq (x k) k rfl
    rw [h2] at h1
    omega
  obtain ⟨K, hK⟩ := hK
  set K' := max K 2 with hK'
  have hstab : ∀ k, K' ≤ k → (D (k+1)).sup id = (D k).sup id := by
    intro k hk
    have hKk : K ≤ k := le_trans (le_max_left K 2) hk
    have hBk := hB k (by omega) (hK k hKk) (hK (k+1) (by omega)) (hK (k+2) (by omega))
    rw [hDsucc, Finset.sup_union, Finset.sup_singleton]
    exact max_eq_left hBk
  have hMconst : ∀ k, K' ≤ k → (D k).sup id = (D K').sup id := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k K' with hlt | hge
      · have hk1 : k + 1 = K' := by omega
        rw [hk1]
      · rw [hstab k hge, ih hge]
  have hfinal : ∀ k, K' ≤ k → k ≤ (D K').sup id + 1 := by
    intro k hk
    have hsub : D k ⊆ Finset.range ((D K').sup id + 1) := by
      intro m hm
      rw [Finset.mem_range]
      have hle : m ≤ (D k).sup id := Finset.le_sup (f := id) hm
      rw [hMconst k hk] at hle
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range, hDcard k] at hc
    exact hc
  have hcontra := hfinal (max K' ((D K').sup id + 2)) (le_max_left _ _)
  omega
