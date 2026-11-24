import AFTD.Prelude
import AFTD.Kb.Tcs.MatchingShortAlternatingCycleNearUniversal

/-!
# matching_short_switch_complement_local_girth_five

Topic: graphs   Node: b0698e122ce1

Provenance: helper lemma. OP-1957, complement local-girth selection route; tested in experiments 34558 and 34563.

For a graph on 2j vertices with minimum degree at least two and complement maximum degree at most 2j-3, suppose no triangle or four-cycle in the complement contains u. Every perfect-matching edge uv then lies on an alternating cycle of length four or six.
-/

theorem matching_short_switch_complement_local_girth_five_inj4 {V : Type*} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> try rfl
  all_goals { first | contradiction | symm at hij; contradiction }

theorem matching_short_switch_complement_local_girth_five_inj6 {V : Type*} {a b c d e f : V}
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e) (h5 : a ≠ f)
    (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f)
    (h10 : c ≠ d) (h11 : c ≠ e) (h12 : c ≠ f)
    (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    Function.Injective (![a, b, c, d, e, f] : Fin 6 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> try rfl
  all_goals { first | contradiction | symm at hij; contradiction }

open SimpleGraph in
theorem matching_short_switch_complement_local_girth_five_mate_in_A
    (j : ℕ) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (h4 : ¬ ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → Fin (2*j)) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b)
    (a : Fin (2*j)) (hua : (Gᶜ).Adj u a) (hva : G.Adj v a) :
    (Gᶜ).Adj u ((SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP a).choose) := by
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  let m : Fin (2*j) → Fin (2*j) := fun x => (hP' x).choose
  have hm_adj : ∀ x, P.Adj x (m x) := fun x => (hP' x).choose_spec.1
  have hm_eq : ∀ {x y}, P.Adj x y → y = m x := fun {x y} hxy => (hP' x).choose_spec.2 y hxy
  have huvG : G.Adj u v := P.adj_sub huv
  have hnot_cuv : ¬ (Gᶜ).Adj u v := by
    intro h
    exact (compl_adj G u v).mp h |>.2 huvG
  set b := m a
  have hpab : P.Adj a b := hm_adj a
  by_contra hncub
  have hbu : b ≠ u := by
    intro hbu
    have hab : P.Adj a u := by simpa [hbu] using hpab
    have : a = v := (hP' u).unique hab.symm huv
    subst a
    exact hnot_cuv hua
  have hbv : b ≠ v := by
    intro hbv
    have hab : P.Adj a v := by simpa [hbv] using hpab
    have : a = u := (hP' v).unique hab.symm huv.symm
    subst a
    exact (compl_adj G u u).mp hua |>.1 rfl
  have hub : G.Adj u b := by
    by_contra h
    apply hncub
    exact (compl_adj G u b).mpr ⟨hbu.symm, h⟩
  have hau : u ≠ a := (compl_adj G u a).mp hua |>.1
  have hav : v ≠ a := hva.ne
  have hab : a ≠ b := (P.adj_sub hpab).ne
  have hinj : Function.Injective (![u,v,a,b] : Fin 4 → Fin (2*j)) :=
    matching_short_switch_complement_local_girth_five_inj4
      huvG.ne hau (hbu.symm) hav hbv.symm hab
  apply h4
  exact ⟨a, b, hinj, hpab, hva, hub⟩

open SimpleGraph in
theorem matching_short_switch_complement_local_girth_five_six_switch_pair
    (j : ℕ) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (hsquare : ∀ a b x, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → x ≠ u → ¬ ((Gᶜ).Adj a x ∧ (Gᶜ).Adj b x))
    (a b : Fin (2*j)) (hua : (Gᶜ).Adj u a) (hub : (Gᶜ).Adj u b) (hab : a ≠ b)
    (hpab : P.Adj a b) (hva : G.Adj v a) (hvb : G.Adj v b)
    (c d : Fin (2*j)) (hpcd : P.Adj c d)
    (hcu : c ≠ u) (hcv : c ≠ v) (hnuc : ¬ (Gᶜ).Adj u c)
    (hdu : d ≠ u) (hdv : d ≠ v) (hnud : ¬ (Gᶜ).Adj u d) :
    ∃ a' b' c' d', Function.Injective (![u,v,a',b',c',d'] : Fin 6 → Fin (2*j)) ∧
      P.Adj a' b' ∧ P.Adj c' d' ∧ G.Adj v b' ∧ G.Adj a' c' ∧ G.Adj u d' := by
  have huvG : G.Adj u v := P.adj_sub huv
  have huc : G.Adj u c := by
    by_contra h
    apply hnuc
    exact (compl_adj G u c).mpr ⟨hcu.symm, h⟩
  have hud : G.Adj u d := by
    by_contra h
    apply hnud
    exact (compl_adj G u d).mpr ⟨hdu.symm, h⟩
  have hca : c ≠ a := by
    rintro rfl
    exact hnuc hua
  have hcb : c ≠ b := by
    rintro rfl
    exact hnuc hub
  have hda : d ≠ a := by
    rintro rfl
    exact hnud hua
  have hdb : d ≠ b := by
    rintro rfl
    exact hnud hub
  have hcd : c ≠ d := (P.adj_sub hpcd).ne
  have hau : u ≠ a := (compl_adj G u a).mp hua |>.1
  have hbu : u ≠ b := (compl_adj G u b).mp hub |>.1
  have hav : v ≠ a := hva.ne
  have hbv : v ≠ b := hvb.ne
  have hor : G.Adj a c ∨ G.Adj b c := by
    by_contra h
    have h1 : (Gᶜ).Adj a c := (compl_adj G a c).mpr ⟨hca.symm, fun hac => h (Or.inl hac)⟩
    have h2 : (Gᶜ).Adj b c := (compl_adj G b c).mpr ⟨hcb.symm, fun hbc => h (Or.inr hbc)⟩
    exact hsquare a b c hua hub hab hcu ⟨h1, h2⟩
  rcases hor with hac | hbc
  · refine ⟨a, b, c, d, ?_, hpab, hpcd, hvb, hac, hud⟩
    exact matching_short_switch_complement_local_girth_five_inj6
      huvG.ne hau hbu hcu.symm hdu.symm
      hav hbv hcv.symm hdv.symm
      hab hca.symm hda.symm hcb.symm hdb.symm hcd
  · refine ⟨b, a, c, d, ?_, hpab.symm, hpcd, hva, hbc, hud⟩
    exact matching_short_switch_complement_local_girth_five_inj6
      huvG.ne hbu hau hcu.symm hdu.symm
      hbv hav hcv.symm hdv.symm
      hab.symm hcb.symm hdb.symm hca.symm hda.symm hcd

open SimpleGraph in
theorem matching_short_switch_complement_local_girth_five_six_switch_a0
    (j : ℕ) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (htri : ∀ a b, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → ¬ (Gᶜ).Adj a b)
    (a b : Fin (2*j)) (hua : (Gᶜ).Adj u a) (hub : (Gᶜ).Adj u b) (hab : a ≠ b)
    (hpab : P.Adj a b) (hvb : G.Adj v b)
    (a0 b0 : Fin (2*j)) (hpa0b0 : P.Adj a0 b0)
    (hua0 : (Gᶜ).Adj u a0) (hva0 : ¬ G.Adj v a0)
    (hnub0 : ¬ (Gᶜ).Adj u b0) :
    ∃ a' b' c' d', Function.Injective (![u,v,a',b',c',d'] : Fin 6 → Fin (2*j)) ∧
      P.Adj a' b' ∧ P.Adj c' d' ∧ G.Adj v b' ∧ G.Adj a' c' ∧ G.Adj u d' := by
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have huvG : G.Adj u v := P.adj_sub huv
  have hnot_cuv : ¬ (Gᶜ).Adj u v := by
    intro h
    exact (compl_adj G u v).mp h |>.2 huvG
  have ha0u : u ≠ a0 := (compl_adj G u a0).mp hua0 |>.1
  have ha0v : v ≠ a0 := by
    rintro rfl
    exact hnot_cuv hua0
  have haa0 : a ≠ a0 := by
    intro h
    have heq : b0 = b := (hP' a).unique (h ▸ hpa0b0) hpab
    exact hnub0 (heq ▸ hub)
  have hba0 : b ≠ a0 := by
    intro h
    have heq : b0 = a := (hP' b).unique (h ▸ hpa0b0) hpab.symm
    exact hnub0 (heq ▸ hua)
  have hb0u : b0 ≠ u := by
    intro h
    have heq : a0 = v := (hP' u).unique (h ▸ hpa0b0.symm) huv
    exact hnot_cuv (heq ▸ hua0)
  have hb0v : b0 ≠ v := by
    intro h
    have heq : a0 = u := (hP' v).unique (h ▸ hpa0b0.symm) huv.symm
    exact ha0u (heq ▸ rfl)
  have hb0a : b0 ≠ a := by
    intro h
    exact hnub0 (h ▸ hua)
  have hb0b : b0 ≠ b := by
    intro h
    exact hnub0 (h ▸ hub)
  have ha0b0 : a0 ≠ b0 := (P.adj_sub hpa0b0).ne
  have hau : u ≠ a := (compl_adj G u a).mp hua |>.1
  have hbu : u ≠ b := (compl_adj G u b).mp hub |>.1
  have hav : v ≠ a := by
    rintro rfl
    exact hnot_cuv hua
  have hbv : v ≠ b := hvb.ne
  have haa0G : G.Adj a a0 := by
    by_contra h
    have h1 : (Gᶜ).Adj a a0 := (compl_adj G a a0).mpr ⟨haa0, h⟩
    exact htri a a0 hua hua0 haa0 h1
  have hub0 : G.Adj u b0 := by
    by_contra h
    apply hnub0
    exact (compl_adj G u b0).mpr ⟨hb0u.symm, h⟩
  refine ⟨a, b, a0, b0, ?_, hpab, hpa0b0, hvb, haa0G, hub0⟩
  exact matching_short_switch_complement_local_girth_five_inj6
    huvG.ne hau hbu ha0u hb0u.symm
    hav hbv ha0v hb0v.symm
    hab haa0 hb0a.symm hba0 hb0b.symm ha0b0

open SimpleGraph in
theorem matching_short_switch_complement_local_girth_five_six_switch_a0_c
    (j : ℕ) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (a0 a1 : Fin (2*j)) (hpa : P.Adj a1 a0)
    (hua0 : (Gᶜ).Adj u a0) (hua1 : (Gᶜ).Adj u a1)
    (hva1 : G.Adj v a1)
    (c d : Fin (2*j)) (hpcd : P.Adj c d)
    (hcu : c ≠ u) (hcv : c ≠ v) (hca0 : c ≠ a0) (hca1 : c ≠ a1)
    (hdu : d ≠ u) (hdv : d ≠ v) (hda0 : d ≠ a0) (hda1 : d ≠ a1)
    (hud : G.Adj u d)
    (hac : G.Adj a0 c) :
    ∃ a' b' c' d', Function.Injective (![u,v,a',b',c',d'] : Fin 6 → Fin (2*j)) ∧
      P.Adj a' b' ∧ P.Adj c' d' ∧ G.Adj v b' ∧ G.Adj a' c' ∧ G.Adj u d' := by
  have huvG : G.Adj u v := P.adj_sub huv
  have hnot_cuv : ¬ (Gᶜ).Adj u v := by
    intro h
    exact (compl_adj G u v).mp h |>.2 huvG
  have ha1u : u ≠ a1 := (compl_adj G u a1).mp hua1 |>.1
  have ha0u : u ≠ a0 := (compl_adj G u a0).mp hua0 |>.1
  have ha1v : v ≠ a1 := hva1.ne
  have ha0v : v ≠ a0 := by
    rintro rfl
    exact hnot_cuv hua0
  have ha1a0 : a1 ≠ a0 := (P.adj_sub hpa).ne
  have hcd : c ≠ d := (P.adj_sub hpcd).ne
  refine ⟨a0, a1, c, d, ?_, hpa.symm, hpcd, hva1, hac, hud⟩
  exact matching_short_switch_complement_local_girth_five_inj6
    huvG.ne ha0u ha1u hcu.symm hdu.symm
    ha0v ha1v hcv.symm hdv.symm
    ha1a0.symm hca0.symm hda0.symm hca1.symm hda1.symm hcd

open SimpleGraph in
theorem matching_short_switch_complement_local_girth_five_outside_pair
    (j : ℕ) (hj : 2 ≤ j) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (hmax : (Gᶜ).degree u ≤ 2*j - 3)
    (hm_A : ∀ x, (Gᶜ).Adj u x → (Gᶜ).Adj u ((SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP x).choose)) :
    ∃ c d, P.Adj c d ∧ c ≠ u ∧ c ≠ v ∧ ¬ (Gᶜ).Adj u c ∧ d ≠ u ∧ d ≠ v ∧ ¬ (Gᶜ).Adj u d := by
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  let m : Fin (2*j) → Fin (2*j) := fun x => (hP' x).choose
  have hm_adj : ∀ x, P.Adj x (m x) := fun x => (hP' x).choose_spec.1
  have hm_eq : ∀ {x y}, P.Adj x y → y = m x := fun {x y} hxy => (hP' x).choose_spec.2 y hxy
  have hm_inv : ∀ x, m (m x) = x := fun x => (hm_eq (hm_adj x).symm).symm
  have hm_u : m u = v := (hm_eq huv).symm
  have hm_v : m v = u := (hm_eq huv.symm).symm
  have huvG : G.Adj u v := P.adj_sub huv
  have hnot_cuv : ¬ (Gᶜ).Adj u v := by
    intro h
    exact (compl_adj G u v).mp h |>.2 huvG
  let A := (Gᶜ).neighborFinset u
  have huA : u ∉ A := by simp [A]
  have hvA : v ∉ A := by simp [A, hnot_cuv]
  let S := A ∪ {u, v}
  have hS_disj : Disjoint A {u, v} := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨huA, hvA⟩
  have hS_card : S.card = A.card + 2 := by
    rw [Finset.card_union_of_disjoint hS_disj]
    simp [huvG.ne]
  have hScard_le : S.card ≤ 2*j - 1 := by
    have hdeg : A.card = (Gᶜ).degree u := rfl
    rw [hS_card, hdeg]
    omega
  have h_univ_card : (Finset.univ : Finset (Fin (2*j))).card = 2*j := Fintype.card_fin (2*j)
  have h_sdiff_pos : 0 < (Finset.univ \ S : Finset (Fin (2*j))).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h_univ_card]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h_sdiff_pos
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hcA, hcu, hcv⟩ := hc
  have hncuc : ¬ (Gᶜ).Adj u c := by
    intro h
    exact hcA (((Gᶜ).mem_neighborFinset u c).mpr h)
  set d := m c
  have hcd : P.Adj c d := hm_adj c
  have hdu : d ≠ u := by
    intro hdu
    have : c = m d := (hm_inv c).symm
    rw [hdu, hm_u] at this
    exact hcv this
  have hdv : d ≠ v := by
    intro hdv
    have : c = m d := (hm_inv c).symm
    rw [hdv, hm_v] at this
    exact hcu this
  have hncud : ¬ (Gᶜ).Adj u d := by
    intro h
    have hmd : (Gᶜ).Adj u (m d) := hm_A d h
    have : c = m d := (hm_inv c).symm
    rw [← this] at hmd
    exact hncuc hmd
  exact ⟨c, d, hcd, hcu, hcv, hncuc, hdu, hdv, hncud⟩

theorem matching_short_switch_complement_local_girth_five
    (j : ℕ) (hj : 2 ≤ j) (G : SimpleGraph (Fin (2*j))) [DecidableRel G.Adj]
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (hdeg : ∀ x, 2 ≤ G.degree x) (hmax : ∀ x, (Gᶜ).degree x ≤ 2*j-3)
    (u v : Fin (2*j)) (huv : P.Adj u v)
    (htri : ∀ a b, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → ¬ (Gᶜ).Adj a b)
    (hsquare : ∀ a b x, (Gᶜ).Adj u a → (Gᶜ).Adj u b → a ≠ b → x ≠ u → ¬ ((Gᶜ).Adj a x ∧ (Gᶜ).Adj b x)) :
    (∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → Fin (2*j)) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b) ∨
    (∃ a b c d, Function.Injective (![u,v,a,b,c,d] : Fin 6 → Fin (2*j)) ∧ P.Adj a b ∧ P.Adj c d ∧ G.Adj v b ∧ G.Adj a c ∧ G.Adj u d) := by
  open SimpleGraph in
  have hP' := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  let m : Fin (2*j) → Fin (2*j) := fun x => (hP' x).choose
  have hm_adj : ∀ x, P.Adj x (m x) := fun x => (hP' x).choose_spec.1
  have hm_eq : ∀ {x y}, P.Adj x y → y = m x := fun {x y} hxy => (hP' x).choose_spec.2 y hxy
  have hm_inv : ∀ x, m (m x) = x := fun x => (hm_eq (hm_adj x).symm).symm
  have hm_u : m u = v := (hm_eq huv).symm
  have hm_v : m v = u := (hm_eq huv.symm).symm
  have huvG : G.Adj u v := P.adj_sub huv
  have hnot_cuv : ¬ (Gᶜ).Adj u v := by
    intro h
    exact (compl_adj G u v).mp h |>.2 huvG
  have hnot_cuu : ¬ (Gᶜ).Adj u u := by
    intro h
    exact (compl_adj G u u).mp h |>.1 rfl
  have hdeg' : ∀ x, ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
    intro x
    have hc : 1 < (G.neighborFinset x).card := hdeg x
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hc
    exact ⟨a, b, hab, (G.mem_neighborFinset x a).mp ha, (G.mem_neighborFinset x b).mp hb⟩
  by_cases hnear : ∀ a b, a ≠ u → b ≠ u → ¬ G.Adj u a → ¬ G.Adj u b → a = b
  · exact matching_short_alternating_cycle_near_universal G P hP hdeg' u v huv hnear
  by_cases h4 : ∃ a b, Function.Injective (![u,v,a,b] : Fin 4 → Fin (2*j)) ∧ P.Adj a b ∧ G.Adj v a ∧ G.Adj u b
  · exact Or.inl h4
  right
  push Not at hnear
  obtain ⟨x1, x2, hx1u, hx2u, hnx1, hnx2, hx12⟩ := hnear
  have hx1 : (Gᶜ).Adj u x1 := (compl_adj G u x1).mpr ⟨hx1u.symm, hnx1⟩
  have hx2 : (Gᶜ).Adj u x2 := (compl_adj G u x2).mpr ⟨hx2u.symm, hnx2⟩
  have h_mate_A : ∀ a, (Gᶜ).Adj u a → G.Adj v a → (Gᶜ).Adj u (m a) :=
    fun a hua hva => matching_short_switch_complement_local_girth_five_mate_in_A j G P hP u v huv h4 a hua hva
  have h_at_most_one : ∀ a b, (Gᶜ).Adj u a → (Gᶜ).Adj u b → ¬ G.Adj v a → ¬ G.Adj v b → a = b := by
    intro a b hua hub hva hvb
    by_contra hab
    have hav : a ≠ v := by
      rintro rfl
      exact hnot_cuv hua
    have hbv : b ≠ v := by
      rintro rfl
      exact hnot_cuv hub
    have h1 : (Gᶜ).Adj a v := (compl_adj G a v).mpr ⟨hav, fun h => hva h.symm⟩
    have h2 : (Gᶜ).Adj b v := (compl_adj G b v).mpr ⟨hbv, fun h => hvb h.symm⟩
    exact hsquare a b v hua hub hab huvG.ne.symm ⟨h1, h2⟩
  by_cases h_miss : ∃ a0, (Gᶜ).Adj u a0 ∧ ¬ G.Adj v a0
  · obtain ⟨a0, hua0, hva0⟩ := h_miss
    have hva_other : ∀ a, (Gᶜ).Adj u a → a ≠ a0 → G.Adj v a :=
      fun a hua ha => by_contra fun h => ha (h_at_most_one a a0 hua hua0 h hva0)
    by_cases hma0 : (Gᶜ).Adj u (m a0)
    · set a1 := m a0
      have hua1 : (Gᶜ).Adj u a1 := hma0
      have ha0a1 : a0 ≠ a1 := (P.adj_sub (hm_adj a0)).ne
      have hva1 : G.Adj v a1 := hva_other a1 hua1 ha0a1.symm
      have hma1 : m a1 = a0 := hm_inv a0
      have hmA_all : ∀ x, (Gᶜ).Adj u x → (Gᶜ).Adj u (m x) := by
        intro x hx
        by_cases hxa0 : x = a0
        · rw [hxa0]
          exact hma0
        by_cases hxa1 : x = a1
        · rw [hxa1, hma1]
          exact hua0
        exact h_mate_A x hx (hva_other x hx hxa0)
      obtain ⟨c, d, hpcd, hcu, hcv, hnuc, hdu, hdv, hnud⟩ :=
        matching_short_switch_complement_local_girth_five_outside_pair j hj G P hP u v huv (hmax u) hmA_all
      by_cases hex_other : ∃ a, (Gᶜ).Adj u a ∧ a ≠ a0 ∧ a ≠ a1
      · obtain ⟨a, hua, ha0, ha1⟩ := hex_other
        have hva : G.Adj v a := hva_other a hua ha0
        set b := m a
        have hub : (Gᶜ).Adj u b := h_mate_A a hua hva
        have hba0 : b ≠ a0 := by
          intro hba0
          have : a = m b := (hm_inv a).symm
          rw [hba0] at this
          exact ha1 this
        have hba1 : b ≠ a1 := by
          intro hba1
          have : a = m b := (hm_inv a).symm
          rw [hba1, hma1] at this
          exact ha0 this
        have hvb : G.Adj v b := hva_other b hub hba0
        have hpab : P.Adj a b := hm_adj a
        have hab : a ≠ b := (P.adj_sub hpab).ne
        exact matching_short_switch_complement_local_girth_five_six_switch_pair
          j G P u v huv hsquare a b hua hub hab hpab hva hvb c d hpcd hcu hcv hnuc hdu hdv hnud
      · have h_only : ∀ a, (Gᶜ).Adj u a → a = a0 ∨ a = a1 := by
          intro a hua
          by_contra h
          apply hex_other
          have h1 : a ≠ a0 := fun h1 => h (Or.inl h1)
          have h2 : a ≠ a1 := fun h2 => h (Or.inr h2)
          exact ⟨a, hua, h1, h2⟩
        by_cases hex_adj : ∃ x, x ≠ u ∧ x ≠ v ∧ x ≠ a0 ∧ x ≠ a1 ∧ G.Adj a0 x
        · obtain ⟨x, hxu, hxv, hxa0, hxa1, ha0x⟩ := hex_adj
          set y := m x
          have hp_xy : P.Adj x y := hm_adj x
          have hyu : y ≠ u := by
            intro hyu
            have : x = m y := (hm_inv x).symm
            rw [hyu, hm_u] at this
            exact hxv this
          have hyv : y ≠ v := by
            intro hyv
            have : x = m y := (hm_inv x).symm
            rw [hyv, hm_v] at this
            exact hxu this
          have hya0 : y ≠ a0 := by
            intro hya0
            have : x = m y := (hm_inv x).symm
            rw [hya0] at this
            exact hxa1 this
          have hya1 : y ≠ a1 := by
            intro hya1
            have : x = m y := (hm_inv x).symm
            rw [hya1, hma1] at this
            exact hxa0 this
          have hy_not_A : ¬ (Gᶜ).Adj u y := fun h => by
            rcases h_only y h with hy | hy
            · exact hya0 hy
            · exact hya1 hy
          have huy : G.Adj u y := by
            by_contra h
            exact hy_not_A ((compl_adj G u y).mpr ⟨hyu.symm, h⟩)
          exact matching_short_switch_complement_local_girth_five_six_switch_a0_c
            j G P u v huv a0 a1 (hm_adj a0).symm hua0 hua1 hva1 x y hp_xy
            hxu hxv hxa0 hxa1 hyu hyv hya0 hya1 huy ha0x
        · push Not at hex_adj
          have hsub : ∀ x, x ≠ a0 → x ≠ a1 → (Gᶜ).Adj a0 x := by
            intro x hxa0 hxa1
            by_cases hxu : x = u
            · rw [hxu]
              exact hua0.symm
            by_cases hxv : x = v
            · rw [hxv]
              have hav : a0 ≠ v := by
                rintro rfl
                exact hnot_cuv hua0
              exact (compl_adj G a0 v).mpr ⟨hav, fun h => hva0 h.symm⟩
            have hnot_a0x : ¬ G.Adj a0 x := hex_adj x hxu hxv hxa0 hxa1
            exact (compl_adj G a0 x).mpr ⟨hxa0.symm, hnot_a0x⟩
          have hcard : (Finset.univ \ {a0, a1} : Finset (Fin (2*j))).card = 2*j - 2 := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
            simp [Finset.card_pair ha0a1]
          have hinc : (Finset.univ \ {a0, a1} : Finset (Fin (2*j))) ⊆ (Gᶜ).neighborFinset a0 := by
            intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
              true_and, not_or] at hx
            exact ((Gᶜ).mem_neighborFinset a0 x).mpr (hsub x hx.1 hx.2)
          have hle := Finset.card_le_card hinc
          rw [hcard] at hle
          have hdeg : ((Gᶜ).neighborFinset a0).card = (Gᶜ).degree a0 := rfl
          rw [hdeg] at hle
          have hmax_a0 := hmax a0
          omega
    · have ha_ex : ∃ a, (Gᶜ).Adj u a ∧ a ≠ a0 := by
        by_cases hx1a0 : x1 = a0
        · refine ⟨x2, hx2, ?_⟩
          rintro rfl
          exact hx12 hx1a0
        · exact ⟨x1, hx1, hx1a0⟩
      obtain ⟨a, hua, haa0⟩ := ha_ex
      have hva : G.Adj v a := hva_other a hua haa0
      set b := m a
      have hub : (Gᶜ).Adj u b := h_mate_A a hua hva
      have hba0 : b ≠ a0 := by
        intro hba0
        have : a = m b := (hm_inv a).symm
        rw [hba0] at this
        exact hma0 (this ▸ hua)
      have hvb : G.Adj v b := hva_other b hub hba0
      have hpab : P.Adj a b := hm_adj a
      have hab : a ≠ b := (P.adj_sub hpab).ne
      exact matching_short_switch_complement_local_girth_five_six_switch_a0
        j G P hP u v huv htri a b hua hub hab hpab hvb a0 (m a0) (hm_adj a0) hua0 hva0 hma0
  · push Not at h_miss
    have hva_all : ∀ a, (Gᶜ).Adj u a → G.Adj v a := h_miss
    have hmA_all : ∀ x, (Gᶜ).Adj u x → (Gᶜ).Adj u (m x) := fun x hx => h_mate_A x hx (hva_all x hx)
    obtain ⟨c, d, hpcd, hcu, hcv, hnuc, hdu, hdv, hnud⟩ :=
      matching_short_switch_complement_local_girth_five_outside_pair j hj G P hP u v huv (hmax u) hmA_all
    have hp : P.Adj x1 (m x1) := hm_adj x1
    have hx1ne : x1 ≠ m x1 := (P.adj_sub hp).ne
    exact matching_short_switch_complement_local_girth_five_six_switch_pair
      j G P u v huv hsquare x1 (m x1) hx1 (hmA_all x1 hx1) hx1ne hp (hva_all x1 hx1) (hva_all (m x1) (hmA_all x1 hx1))
      c d hpcd hcu hcv hnuc hdu hdv hnud
