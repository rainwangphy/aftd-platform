import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# two_token_domination_number_odd_p3_matching_le

Topic: graphs   Node: ef06585efe69

Provenance: formalization of a published result. Source: arXiv:2611.15124, Theorem 1.3

Let G be a finite simple graph on vertex type V whose complement graph Gᶜ has a unique vertex of degree 2 and all other vertices of degree 1. Then the domination number of the 2-token graph F_2(G) is at most (Fintype.card V + 1) / 2.
-/

lemma two_token_domination_number_odd_p3_matching_le_symmDiff_pair_pair {V : Type*} [DecidableEq V] (a b x : V)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    symmDiff ({a, x} : Finset V) {a, b} = {b, x} := by
  ext c
  rw [Finset.mem_symmDiff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hca : c = a
  · subst hca
    simp [hab, hax]
  · by_cases hcx : c = x
    · subst hcx
      simp [hbx.symm, hax.symm]
    · by_cases hcb : c = b
      · subst hcb
        simp [hab.symm, hbx]
      · simp [hca, hcx, hcb]

open scoped Classical in
/-- If the complement of G has a vertex of degree 2 and all others degree 1 (isomorphic to P_3 union disjoint edges), then the domination number of F_2(G) is at most (n + 1) / 2. -/
theorem two_token_domination_number_odd_p3_matching_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdeg : ∃ v : V, Gᶜ.degree v = 2 ∧ ∀ u : V, u ≠ v → Gᶜ.degree u = 1) :
    simple_graph_domination_number (token_graph G 2) ≤ (Fintype.card V + 1) / 2 := by
  classical
  obtain ⟨x2, hx2_deg, hothers⟩ := hdeg
  have hex : ∀ u, u ≠ x2 → ∃! w, Gᶜ.Adj u w := by
    intro u hu
    have h1 : (Gᶜ.neighborFinset u).card = 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hothers u hu]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
    refine ⟨w, ?_, ?_⟩
    · have : w ∈ Gᶜ.neighborFinset u := by rw [hw]; simp
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp this
    · intro y hy
      have : y ∈ Gᶜ.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr hy
      rw [hw] at this
      simpa using this
  let p : V → V := fun v => if h : v = x2 then x2 else Classical.choose (hex v h)
  have hp_def : ∀ v (hv : v ≠ x2), p v = Classical.choose (hex v hv) := by
    intro v hv
    dsimp [p]
    rw [dif_neg hv]
  have hp_adj : ∀ v (hv : v ≠ x2), Gᶜ.Adj v (p v) := by
    intro v hv
    rw [hp_def v hv]
    exact (Classical.choose_spec (hex v hv)).1
  have hp_uniq : ∀ v (hv : v ≠ x2) w, Gᶜ.Adj v w → w = p v := by
    intro v hv w hw
    rw [hp_def v hv]
    exact (Classical.choose_spec (hex v hv)).2 w hw

  have h2 : (Gᶜ.neighborFinset x2).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hx2_deg]
  obtain ⟨x1, x3, hx13_ne, hx2_nbrs⟩ := Finset.card_eq_two.mp h2
  have hx1_mem : x1 ∈ Gᶜ.neighborFinset x2 := by rw [hx2_nbrs]; simp
  have hx3_mem : x3 ∈ Gᶜ.neighborFinset x2 := by rw [hx2_nbrs]; simp
  have hx21_adj : Gᶜ.Adj x2 x1 := (SimpleGraph.mem_neighborFinset _ _ _).mp hx1_mem
  have hx23_adj : Gᶜ.Adj x2 x3 := (SimpleGraph.mem_neighborFinset _ _ _).mp hx3_mem
  have hx12_ne : x1 ≠ x2 := ((Gᶜ).ne_of_adj hx21_adj).symm
  have hx32_ne : x3 ≠ x2 := ((Gᶜ).ne_of_adj hx23_adj).symm
  have hpx1 : p x1 = x2 := (hp_uniq x1 hx12_ne x2 hx21_adj.symm).symm
  have hpx3 : p x3 = x2 := (hp_uniq x3 hx32_ne x2 hx23_adj.symm).symm

  let W : Finset V := Finset.univ.filter (fun v => v ≠ x1 ∧ v ≠ x2 ∧ v ≠ x3)
  have hpW : ∀ u ∈ W, p u ∈ W := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    obtain ⟨-, hu1, hu2, hu3⟩ := hu
    have hpadj := hp_adj u hu2
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro h
      have h1 : Gᶜ.Adj x1 u := by rw [h] at hpadj; exact hpadj.symm
      have := hp_uniq x1 hx12_ne u h1
      rw [hpx1] at this
      exact hu2 this
    · intro h
      have h2 : Gᶜ.Adj x2 u := by rw [h] at hpadj; exact hpadj.symm
      have hmem : u ∈ Gᶜ.neighborFinset x2 := (SimpleGraph.mem_neighborFinset _ _ _).mpr h2
      rw [hx2_nbrs] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hu1 rfl
      · exact hu3 rfl
    · intro h
      have h3 : Gᶜ.Adj x3 u := by rw [h] at hpadj; exact hpadj.symm
      have := hp_uniq x3 hx32_ne u h3
      rw [hpx3] at this
      exact hu2 this

  have hpinvol : ∀ u ∈ W, p (p u) = u := by
    intro u hu
    have hpuW := hpW u hu
    rw [Finset.mem_filter] at hu hpuW
    have hadj := (hp_adj u hu.2.2.1).symm
    exact (hp_uniq (p u) hpuW.2.2.1 u hadj).symm

  have hpne : ∀ u ∈ W, p u ≠ u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    intro h
    exact (Gᶜ).ne_of_adj (hp_adj u hu.2.2.1) h.symm

  have hGadj : ∀ u v : V, u ≠ v → ¬ Gᶜ.Adj u v → G.Adj u v := by
    intro u v huv hc
    by_contra h
    exact hc ⟨huv, h⟩

  have hx13_Gadj : G.Adj x1 x3 := by
    apply hGadj x1 x3 hx13_ne
    intro hc
    have := hp_uniq x1 hx12_ne x3 hc
    rw [hpx1] at this
    exact hx32_ne this

  let f : V → {s : Finset V // s.card = 2} := fun u =>
    if h : u ∈ W then ⟨{u, p u}, Finset.card_pair (hpne u h).symm⟩
    else ⟨{x1, x2}, Finset.card_pair hx12_ne⟩

  have hfib : ∀ u ∈ W, (W.filter (fun v => f v = f u)) = ({u, p u} : Finset V) := by
    intro u hu
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hvW, heq⟩
      have huW := hu
      dsimp [f] at heq
      rw [dif_pos hvW, dif_pos huW] at heq
      have hmem : v ∈ (⟨{v, p v}, Finset.card_pair (hpne v hvW).symm⟩ : {s : Finset V // s.card = 2}).val := by simp
      rw [heq] at hmem
      simpa using hmem
    · rintro (rfl | rfl)
      · exact ⟨hu, rfl⟩
      · refine ⟨hpW u hu, ?_⟩
        dsimp [f]
        rw [dif_pos (hpW u hu), dif_pos hu]
        apply Subtype.ext
        change ({p u, p (p u)} : Finset V) = {u, p u}
        rw [hpinvol u hu, Finset.pair_comm]

  let DW : Finset {s : Finset V // s.card = 2} := W.image f
  have hmaps : Set.MapsTo f (↑W) (↑DW) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber2 : ∀ b ∈ DW, (W.filter (fun a => f a = b)).card = 2 := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    rw [hfib u hu, Finset.card_pair (hpne u hu).symm]
  have h1 : W.card = DW.card * 2 := by
    rw [hsum, Finset.sum_congr rfl hfiber2]
    simp [Finset.sum_const]
  have hDWcard : DW.card = W.card / 2 := by
    rw [h1, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]

  have hx23 : x2 ∉ ({x3} : Finset V) := by simp [hx32_ne.symm]
  have hx123 : x1 ∉ ({x2, x3} : Finset V) := by simp [hx12_ne, hx13_ne]
  have hcardX : ({x1, x2, x3} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem hx123, Finset.card_insert_of_notMem hx23, Finset.card_singleton]
  have hW_compl : W = Finset.univ \ {x1, x2, x3} := by
    ext v
    simp [W]
  have hWcard : W.card = Fintype.card V - 3 := by
    rw [hW_compl, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcardX]
  have hV3 : 3 ≤ Fintype.card V := by
    rw [← Finset.card_univ, ← hcardX]
    exact Finset.card_le_card (Finset.subset_univ _)

  let e1 : {s : Finset V // s.card = 2} := ⟨{x1, x2}, Finset.card_pair hx12_ne⟩
  let e2 : {s : Finset V // s.card = 2} := ⟨{x1, x3}, Finset.card_pair hx13_ne⟩

  have he1_not_DW : e1 ∉ DW := by
    intro hmem
    obtain ⟨u, huW, heq⟩ := Finset.mem_image.mp hmem
    have huW_prop : u ∈ W := huW
    dsimp [f] at heq
    rw [dif_pos huW] at heq
    have hval : ({u, p u} : Finset V) = {x1, x2} := Subtype.ext_iff.mp heq
    have hx1 : x1 ∈ ({u, p u} : Finset V) := by rw [hval]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rw [Finset.mem_filter] at huW_prop
    rcases hx1 with rfl | hpu
    · exact huW_prop.2.1 rfl
    · have hpuW := hpW u huW
      rw [Finset.mem_filter] at hpuW
      exact hpuW.2.1 hpu.symm

  have he2_not_DW : e2 ∉ DW := by
    intro hmem
    obtain ⟨u, huW, heq⟩ := Finset.mem_image.mp hmem
    have huW_prop : u ∈ W := huW
    dsimp [f] at heq
    rw [dif_pos huW] at heq
    have hval : ({u, p u} : Finset V) = {x1, x3} := Subtype.ext_iff.mp heq
    have hx1 : x1 ∈ ({u, p u} : Finset V) := by rw [hval]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rw [Finset.mem_filter] at huW_prop
    rcases hx1 with rfl | hpu
    · exact huW_prop.2.1 rfl
    · have hpuW := hpW u huW
      rw [Finset.mem_filter] at hpuW
      exact hpuW.2.1 hpu.symm

  have he12_ne : e1 ≠ e2 := by
    intro h
    have hval : e1.val = e2.val := by rw [h]
    change ({x1, x2} : Finset V) = {x1, x3} at hval
    have hx2 : x2 ∈ ({x1, x3} : Finset V) := by rw [← hval]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl
    · exact hx12_ne.symm rfl
    · exact hx32_ne.symm rfl

  let D : Finset {s : Finset V // s.card = 2} := insert e1 (insert e2 DW)
  have he1_not : e1 ∉ insert e2 DW := by simp [he12_ne, he1_not_DW]
  have hDcard : D.card = 2 + DW.card := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem he1_not, Finset.card_insert_of_notMem he2_not_DW]
    omega
  have hD_total : D.card = (Fintype.card V + 1) / 2 := by
    rw [hDcard, hDWcard, hWcard]
    omega

  have hdom_u : ∀ a b : V, (hab : a ≠ b) → a ∈ W →
      (⟨{a, b}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) ∈ D ∨
        ∃ t ∈ D, (token_graph G 2).Adj t ⟨{a, b}, Finset.card_pair hab⟩ := by
    intro a b hab haW
    have hfa_DW : f a ∈ DW := Finset.mem_image.mpr ⟨a, haW, rfl⟩
    have hfa_D : f a ∈ D := by simp [D, hfa_DW]
    have hfa_val : (f a).val = {a, p a} := by
      dsimp [f]
      rw [dif_pos haW]
    by_cases hb : b = p a
    · left
      subst hb
      have heq : (⟨{a, p a}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) = f a := by
        apply Subtype.ext
        rw [hfa_val]
      rw [heq]
      exact hfa_D
    · right
      refine ⟨f a, hfa_D, b, p a, ?_, ?_⟩
      · apply hGadj
        · exact hb
        · intro hc
          have hpadj : Gᶜ.Adj (p a) b := hc.symm
          have hpaW := hpW a haW
          rw [Finset.mem_filter] at hpaW
          have huniq := hp_uniq (p a) hpaW.2.2.1 b hpadj
          rw [hpinvol a haW] at huniq
          exact hab huniq.symm
      · rw [hfa_val]
        change symmDiff ({a, p a} : Finset V) {a, b} = {b, p a}
        have hpa_ne_a : a ≠ p a := (hpne a haW).symm
        exact two_token_domination_number_odd_p3_matching_le_symmDiff_pair_pair a b (p a) hab hpa_ne_a hb

  have he1_D : e1 ∈ D := by simp [D]
  have he2_D : e2 ∈ D := by simp [D]

  have hdom : simple_graph_is_dominating (token_graph G 2) (D : Set {s : Finset V // s.card = 2}) := by
    intro s
    obtain ⟨S, hS⟩ := s
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    by_cases haW : a ∈ W
    · exact hdom_u a b hab haW
    · by_cases hbW : b ∈ W
      · have hsymm := hdom_u b a hab.symm hbW
        have hpair_eq : (⟨{b, a}, Finset.card_pair hab.symm⟩ : {s : Finset V // s.card = 2}) = ⟨{a, b}, Finset.card_pair hab⟩ := by
          apply Subtype.ext
          exact Finset.pair_comm b a
        rw [hpair_eq] at hsymm
        exact hsymm
      · have ha_cases : a = x1 ∨ a = x2 ∨ a = x3 := by
          simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at haW
          tauto
        have hb_cases : b = x1 ∨ b = x2 ∨ b = x3 := by
          simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hbW
          tauto
        have hcases : (a = x1 ∧ b = x2) ∨ (a = x2 ∧ b = x1) ∨
          (a = x1 ∧ b = x3) ∨ (a = x3 ∧ b = x1) ∨
          (a = x2 ∧ b = x3) ∨ (a = x3 ∧ b = x2) := by
          rcases ha_cases with rfl | rfl | rfl <;> rcases hb_cases with rfl | rfl | rfl <;> try { contradiction } <;> tauto
        rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · left
          have : (⟨{a, b}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) = e1 := by
            apply Subtype.ext; change ({a, b} : Finset V) = {x1, x2}; rw [ha, hb]
          rw [this]; exact he1_D
        · left
          have : (⟨{a, b}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) = e1 := by
            apply Subtype.ext; change ({a, b} : Finset V) = {x1, x2}; rw [ha, hb, Finset.pair_comm]
          rw [this]; exact he1_D
        · left
          have : (⟨{a, b}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) = e2 := by
            apply Subtype.ext; change ({a, b} : Finset V) = {x1, x3}; rw [ha, hb]
          rw [this]; exact he2_D
        · left
          have : (⟨{a, b}, Finset.card_pair hab⟩ : {s : Finset V // s.card = 2}) = e2 := by
            apply Subtype.ext; change ({a, b} : Finset V) = {x1, x3}; rw [ha, hb, Finset.pair_comm]
          rw [this]; exact he2_D
        · right
          refine ⟨e1, he1_D, x1, x3, hx13_Gadj, ?_⟩
          change symmDiff ({x1, x2} : Finset V) {a, b} = {x1, x3}
          rw [ha, hb, Finset.pair_comm x1 x2]
          have := two_token_domination_number_odd_p3_matching_le_symmDiff_pair_pair x2 x3 x1 hx32_ne.symm hx12_ne.symm hx13_ne.symm
          rw [this, Finset.pair_comm x3 x1]
        · right
          refine ⟨e1, he1_D, x1, x3, hx13_Gadj, ?_⟩
          change symmDiff ({x1, x2} : Finset V) {a, b} = {x1, x3}
          rw [ha, hb, Finset.pair_comm x1 x2, Finset.pair_comm x3 x2]
          have := two_token_domination_number_odd_p3_matching_le_symmDiff_pair_pair x2 x3 x1 hx32_ne.symm hx12_ne.symm hx13_ne.symm
          rw [this, Finset.pair_comm x3 x1]

  unfold simple_graph_domination_number
  rw [← hD_total]
  exact Nat.sInf_le ⟨D, hdom, rfl⟩
