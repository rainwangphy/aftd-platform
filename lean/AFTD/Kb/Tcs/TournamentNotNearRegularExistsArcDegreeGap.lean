import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentSumOutCount
import AFTD.Kb.Tcs.TournamentNearRegularOfCardDegrees
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_not_near_regular_exists_arc_degree_gap

Topic: graphs   Node: d76fed5e2a19

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

In a tournament on 2m vertices with m ≥ 2 that is not near-regular, there are vertices u, v with an arc u → v and out-degree of v at least 2 smaller than the out-degree of u.
-/

open Classical in
lemma tournament_not_near_regular_exists_arc_degree_gap_out_add_in {n : ℕ} (T : Digraph (Fin n))
    [DecidableRel T.Adj] (hT : digraph_is_tournament T) (x : Fin n) :
    digraph_out_count T x + (Finset.univ.filter (fun y => T.Adj y x)).card = n - 1 := by
  classical
  unfold digraph_out_count
  set A := Finset.univ.filter (fun y => T.Adj x y) with hA
  set B := Finset.univ.filter (fun y => T.Adj y x) with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hyA hyB
    by_cases hyx : y = x
    · subst hyx; exact hT.1 y hyA
    · exact (hT.2 x y (Ne.symm hyx)).mp hyA hyB
  have hunion : A ∪ B = Finset.univ.erase x := by
    ext y
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro (h | h) <;> exact ⟨fun e => by subst e; exact hT.1 y h, trivial⟩
    · rintro ⟨hyx, _⟩
      by_cases h : T.Adj x y
      · exact Or.inl h
      · exact Or.inr (by by_contra hc; exact h ((hT.2 x y (Ne.symm hyx)).mpr hc))
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp

lemma tournament_not_near_regular_exists_arc_degree_gap_arith (m d a b c : ℕ) (hm : 2 ≤ m)
    (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hcd : c ≤ d) (hdm : d ≤ m - 1) (had : a ≤ 2 * m - 3 - d)
    (hsum : a + b + c = 2 * m) (hdeg : a * d + b * (d + 1) + c * (d + 2) = m * (2 * m - 1)) :
    False := by
  have key : (c:ℤ) - (a:ℤ) = (m:ℤ) * (2*(m:ℤ) - 3 - 2*(d:ℤ)) := by
    have h1 : (a:ℤ) + (b:ℤ) + (c:ℤ) = 2*(m:ℤ) := by exact_mod_cast hsum
    have h2 : (a:ℤ)*(d:ℤ) + (b:ℤ)*((d:ℤ)+1) + (c:ℤ)*((d:ℤ)+2) = (m:ℤ)*(2*(m:ℤ)-1) := by
      have h2m : (2*(m:ℤ) - 1) = ((2*m - 1 : ℕ) : ℤ) := by
        have : 1 ≤ 2*m := by omega
        omega
      rw [h2m]
      exact_mod_cast hdeg
    nlinarith [h1, h2]
  by_cases hcase : d ≤ m - 2
  · have hk : (1:ℤ) ≤ 2*(m:ℤ) - 3 - 2*(d:ℤ) := by
      have : (d:ℤ) ≤ (m:ℤ) - 2 := by
        have : d + 2 ≤ m := by omega
        omega
      linarith
    have hm0 : (0:ℤ) ≤ (m:ℤ) := by positivity
    have hmul : (m:ℤ) ≤ (m:ℤ) * (2*(m:ℤ) - 3 - 2*(d:ℤ)) := by
      calc (m:ℤ) = (m:ℤ) * 1 := by ring
        _ ≤ (m:ℤ) * (2*(m:ℤ) - 3 - 2*(d:ℤ)) := by
            apply mul_le_mul_of_nonneg_left hk hm0
    have hca : (m:ℤ) ≤ (c:ℤ) - (a:ℤ) := by rw [key]; exact hmul
    have hc1 : (1:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
    have hcd' : (c:ℤ) ≤ (d:ℤ) := by exact_mod_cast hcd
    have hdm' : (d:ℤ) ≤ (m:ℤ) - 1 := by
      have : d + 1 ≤ m := by omega
      omega
    omega
  · have hd : d = m - 1 := by omega
    subst hd
    have hcm : ((m-1:ℕ):ℤ) = (m:ℤ)-1 := by
      have : 1 ≤ m := by omega
      omega
    have hkey2 : (c:ℤ) - (a:ℤ) = -(m:ℤ) := by
      rw [key, hcm]; ring
    have had' : (a:ℤ) ≤ (m:ℤ) - 2 := by
      have h : 2 * m - 3 - (m - 1) = m - 2 := by omega
      have := had
      rw [h] at this
      exact_mod_cast this
    have hc0 : (0:ℤ) ≤ (c:ℤ) := by positivity
    linarith

/-- A non-near-regular tournament on 2m ≥ 4 vertices has an arc whose tail has out-degree exceeding the head's by at least 2. -/
theorem tournament_not_near_regular_exists_arc_degree_gap (m : ℕ) (hm : 2 ≤ m)
    (T : Digraph (Fin (2 * m))) [DecidableRel T.Adj] (hT : digraph_is_tournament T)
    (hnr : ¬ tournament_is_near_regular m T) :
    ∃ u v : Fin (2 * m), T.Adj u v ∧ digraph_out_count T v + 2 ≤ digraph_out_count T u := by
  classical
  by_contra hcon
  have hgap : ∀ u v, T.Adj u v → digraph_out_count T u ≤ digraph_out_count T v + 1 := by
    intro u v huv
    have hnv : ¬ (digraph_out_count T v + 2 ≤ digraph_out_count T u) := by
      intro hB; exact hcon ⟨u, v, huv, hB⟩
    omega
  obtain ⟨vmin, -, hvmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (2 * m)))
    (fun x => digraph_out_count T x) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨vmax, -, hvmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (2 * m)))
    (fun x => digraph_out_count T x) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set dv := digraph_out_count T vmin with hdv
  set Dv := digraph_out_count T vmax with hDv
  have hvmin' : ∀ x, dv ≤ digraph_out_count T x := fun x => hvmin x (Finset.mem_univ x)
  have hvmax' : ∀ x, digraph_out_count T x ≤ Dv := fun x => hvmax x (Finset.mem_univ x)
  have hcomplete : ∀ x y : Fin (2 * m), x ≠ y → T.Adj x y ∨ T.Adj y x := by
    intro x y hne
    by_cases h : T.Adj x y
    · exact Or.inl h
    · exact Or.inr (by by_contra h2; exact h ((hT.2 x y hne).mpr h2))
  have hDbound : Dv ≤ dv + 2 := by
    by_cases hveq : vmin = vmax
    · have : Dv = dv := by rw [hDv, hdv, hveq]
      omega
    · suffices hreach : T.Adj vmax vmin ∨ ∃ w, T.Adj vmax w ∧ T.Adj w vmin by
        rcases hreach with h | ⟨w, h1, h2⟩
        · have := hgap vmax vmin h; omega
        · have e1 := hgap vmax w h1; have e2 := hgap w vmin h2; omega
      by_contra hcon2
      push_neg at hcon2
      obtain ⟨hnotadj, hno3⟩ := hcon2
      set Nmax := Finset.univ.filter (fun x => T.Adj vmax x) with hNmax_def
      set Nmin := Finset.univ.filter (fun x => T.Adj vmin x) with hNmin_def
      have hsub : Nmax ⊆ Nmin := by
        intro x hx
        rw [hNmax_def] at hx; rw [hNmin_def]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have hxne : x ≠ vmin := by intro e; subst e; exact hnotadj hx
        have hnotwx : ¬ T.Adj x vmin := hno3 x hx
        rcases hcomplete vmin x (Ne.symm hxne) with h | h
        · exact h
        · exact absurd h hnotwx
      have hvmaxin : vmax ∈ Nmin := by
        rw [hNmin_def]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hcomplete vmin vmax hveq with h | h
        · exact h
        · exact absurd h hnotadj
      have hvmaxnotin : vmax ∉ Nmax := by
        rw [hNmax_def]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hT.1 vmax
      have hdisj : Disjoint Nmax {vmax} := by
        rw [Finset.disjoint_left]; intro x hx hx'
        rw [Finset.mem_singleton] at hx'; subst hx'; exact hvmaxnotin hx
      have hunion_sub : Nmax ∪ {vmax} ⊆ Nmin := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hsub h
        · rw [Finset.mem_singleton] at h; subst h; exact hvmaxin
      have hcardle : (Nmax ∪ {vmax}).card ≤ Nmin.card := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at hcardle
      have hNmax : Nmax.card = Dv := by rw [hNmax_def, hDv]; rfl
      have hNmin : Nmin.card = dv := by rw [hNmin_def, hdv]; rfl
      rw [hNmax, hNmin] at hcardle
      have := hvmin' vmax
      omega
  by_cases hDle : Dv ≤ dv + 1
  · have hle_all : ∀ x, digraph_out_count T x ≤ dv + 1 := fun x => le_trans (hvmax' x) hDle
    have hsum_out := tournament_sum_out_count (2 * m) T hT
    have hsum_eq : ∑ x : Fin (2 * m), digraph_out_count T x = m * (2 * m - 1) := by
      rw [hsum_out]
      have : (2 * m) * ((2 * m) - 1) = 2 * (m * (2 * m - 1)) := by ring
      omega
    have hsum_const1 : (∑ x : Fin (2 * m), (dv + 1)) = (2 * m) * (dv + 1) := by
      simp [Finset.sum_const, Finset.card_univ]
    have hsum_const0 : (∑ x : Fin (2 * m), dv) = (2 * m) * dv := by
      simp [Finset.sum_const, Finset.card_univ]
    have hle' : m * (2 * m - 1) ≤ (2 * m) * (dv + 1) := by
      rw [← hsum_eq, ← hsum_const1]
      exact Finset.sum_le_sum (fun x _ => hle_all x)
    have hge' : (2 * m) * dv ≤ m * (2 * m - 1) := by
      rw [← hsum_eq, ← hsum_const0]
      exact Finset.sum_le_sum (fun x _ => hvmin' x)
    have hdvm : dv = m - 1 := by
      have hmpos : 0 < m := by omega
      rw [show (2 * m) * (dv + 1) = m * (2 * (dv + 1)) by ring] at hle'
      have hle2 : 2 * m - 1 ≤ 2 * (dv + 1) := by
        have := Nat.le_of_mul_le_mul_left hle' hmpos; omega
      rw [show (2 * m) * dv = m * (2 * dv) by ring] at hge'
      have hge2 : 2 * dv ≤ 2 * m - 1 := Nat.le_of_mul_le_mul_left hge' hmpos
      omega
    exact hnr (fun v => by
      have a1 := hvmin' v
      have a2 := hle_all v
      rw [hdvm] at a1 a2
      by_cases hcase : digraph_out_count T v = m - 1
      · exact Or.inl hcase
      · exact Or.inr (by omega))
  · have hDeq : Dv = dv + 2 := by omega
    exfalso
    set A : Finset (Fin (2 * m)) := Finset.univ.filter (fun x => digraph_out_count T x = dv) with hA
    set B : Finset (Fin (2 * m)) := Finset.univ.filter (fun x => digraph_out_count T x = dv + 1) with hB
    set C : Finset (Fin (2 * m)) := Finset.univ.filter (fun x => digraph_out_count T x = dv + 2) with hC
    have hmemA : vmin ∈ A := by
      rw [hA]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hdv.symm
    have hmemC : vmax ∈ C := by
      rw [hC]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hDv]; exact hDeq
    have ha : 1 ≤ A.card := by
      have := Finset.card_pos.mpr ⟨vmin, hmemA⟩; omega
    have hc : 1 ≤ C.card := by
      have := Finset.card_pos.mpr ⟨vmax, hmemC⟩; omega
    have hmemABC : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ C := by
      intro x
      rw [hA, hB, hC]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hvmin' x
      have h2 := hvmax' x
      omega
    have hABC : (A ∪ B) ∪ C = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rcases hmemABC x with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hdisjAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [hA] at hx; rw [hB] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      omega
    have hdisjAB_C : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_union] at hx; rw [hC] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [hA] at hx; rw [hB] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with hx | hx <;> omega
    have hcard : A.card + B.card + C.card = 2 * m := by
      have h1 : ((A ∪ B) ∪ C).card = A.card + B.card + C.card := by
        rw [Finset.card_union_of_disjoint hdisjAB_C, Finset.card_union_of_disjoint hdisjAB]
      rw [hABC] at h1
      rw [← h1]; simp
    have eA : ∑ x ∈ A, digraph_out_count T x = A.card * dv := by
      have h : ∀ x ∈ A, digraph_out_count T x = dv := by
        intro x hx; rw [hA] at hx; exact (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl h]; simp [Finset.sum_const]
    have eB : ∑ x ∈ B, digraph_out_count T x = B.card * (dv + 1) := by
      have h : ∀ x ∈ B, digraph_out_count T x = dv + 1 := by
        intro x hx; rw [hB] at hx; exact (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl h]; simp [Finset.sum_const]
    have eC : ∑ x ∈ C, digraph_out_count T x = C.card * (dv + 2) := by
      have h : ∀ x ∈ C, digraph_out_count T x = dv + 2 := by
        intro x hx; rw [hC] at hx; exact (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl h]; simp [Finset.sum_const]
    have hdeg_eq : ∑ x : Fin (2 * m), digraph_out_count T x
        = A.card * dv + B.card * (dv + 1) + C.card * (dv + 2) := by
      rw [← hABC, Finset.sum_union hdisjAB_C, Finset.sum_union hdisjAB, eA, eB, eC]
    have hsum_out := tournament_sum_out_count (2 * m) T hT
    have hsum_eq : ∑ x : Fin (2 * m), digraph_out_count T x = m * (2 * m - 1) := by
      rw [hsum_out]
      have : (2 * m) * ((2 * m) - 1) = 2 * (m * (2 * m - 1)) := by ring
      omega
    have hdeg : A.card * dv + B.card * (dv + 1) + C.card * (dv + 2) = m * (2 * m - 1) := by
      rw [← hdeg_eq]; exact hsum_eq
    have hcd : C.card ≤ dv := by
      have hCsub : C ⊆ Finset.univ.filter (fun x => T.Adj vmin x) := by
        intro x hx
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ x, ?_⟩
        rw [hC] at hx
        have hdx : digraph_out_count T x = dv + 2 := (Finset.mem_filter.mp hx).2
        have hne : x ≠ vmin := by
          intro hxv
          have hdx' := hdx
          rw [hxv, ← hdv] at hdx'
          omega
        rcases hcomplete vmin x (Ne.symm hne) with h | h
        · exact h
        · exfalso
          have hh := hgap x vmin h
          rw [hdx, ← hdv] at hh
          omega
      have hc_le := Finset.card_le_card hCsub
      have hthis : (Finset.univ.filter (fun x => T.Adj vmin x)).card = dv := by
        rw [hdv]; rfl
      rwa [hthis] at hc_le
    have hdm : dv ≤ m - 1 := by
      have hsum_eq2 : ∑ x : Fin (2 * m), digraph_out_count T x = m * (2 * m - 1) := by
        rw [hsum_out]
        have : (2 * m) * ((2 * m) - 1) = 2 * (m * (2 * m - 1)) := by ring
        omega
      have hsum_const0 : (∑ x : Fin (2 * m), dv) = (2 * m) * dv := by
        simp [Finset.sum_const, Finset.card_univ]
      have hge : (2 * m) * dv ≤ m * (2 * m - 1) := by
        rw [← hsum_eq2, ← hsum_const0]
        exact Finset.sum_le_sum (fun x _ => hvmin' x)
      have hmpos : 0 < m := by omega
      rw [show (2 * m) * dv = m * (2 * dv) by ring] at hge
      have := Nat.le_of_mul_le_mul_left hge hmpos
      omega
    have had : A.card ≤ 2 * m - 3 - dv := by
      have hAsub : A ⊆ Finset.univ.filter (fun y => T.Adj y vmax) := by
        intro x hx
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ x, ?_⟩
        rw [hA] at hx
        have hdx : digraph_out_count T x = dv := (Finset.mem_filter.mp hx).2
        have hne : x ≠ vmax := by
          intro hxv
          have hdx' := hdx
          rw [hxv, ← hDv] at hdx'
          omega
        rcases hcomplete x vmax hne with h | h
        · exact h
        · exfalso
          have hh := hgap vmax x h
          rw [hdx, ← hDv] at hh
          omega
      have hoi := tournament_not_near_regular_exists_arc_degree_gap_out_add_in T hT vmax
      rw [← hDv] at hoi
      have hincard : (Finset.univ.filter (fun y => T.Adj y vmax)).card = 2 * m - 1 - Dv := by omega
      have hc_le := Finset.card_le_card hAsub
      rw [hincard] at hc_le
      omega
    exact tournament_not_near_regular_exists_arc_degree_gap_arith m dv A.card B.card C.card hm ha hc hcd hdm had hcard hdeg
