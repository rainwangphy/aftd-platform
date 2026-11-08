import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.OneLayeredFamily
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# one_layered_linear_bound

Topic: combinatorics   Node: a8175c2f4b72

Provenance: formalization of a published result. Source: arXiv:2611.08071 Theorem 2.1

For all integers r ≥ 1 and m ≥ r, the maximum number of layers F(m, r) in a 1-layered family of r-subsets on at most m vertices satisfies F(m, r) ≤ 2^(r - 1) * (m - r) + 1.
-/

def olb_vs {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (t : Fin F.k) :
    Finset V := (F.layers t).biUnion id

def olb_U {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) : Finset V :=
  (Finset.univ : Finset (Fin F.k)).biUnion (olb_vs F)

theorem olb_mem_vs {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (t : Fin F.k)
    (w : V) : w ∈ olb_vs F t ↔ ∃ G ∈ F.layers t, w ∈ G := by
  simp [olb_vs]

theorem olb_vs_mid {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) {w : V}
    {s t u : Fin F.k} (hs : w ∈ olb_vs F s) (ht : w ∈ olb_vs F t) (h1 : s ≤ u) (h2 : u ≤ t) :
    w ∈ olb_vs F u := by
  have h := (F.interval_property {w} (Finset.singleton_nonempty w)).out
  rw [olb_mem_vs] at hs ht ⊢
  obtain ⟨G1, hG1, hw1⟩ := hs
  obtain ⟨G2, hG2, hw2⟩ := ht
  obtain ⟨G, hG, hsub⟩ := h (x := s) ⟨G1, hG1, Finset.singleton_subset_iff.mpr hw1⟩ (y := t)
    ⟨G2, hG2, Finset.singleton_subset_iff.mpr hw2⟩ ⟨h1, h2⟩
  exact ⟨G, hG, Finset.singleton_subset_iff.mp hsub⟩

def olb_suf {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (j : ℕ)
    (hj : j < F.k) : OneLayeredFamily V r where
  k := F.k - j
  k_pos := by omega
  layers t := F.layers ⟨t.val + j, by have := t.isLt; omega⟩
  layers_nonempty t := F.layers_nonempty _
  layers_card t := F.layers_card _
  layers_disjoint t₁ t₂ h := F.layers_disjoint _ _ (fun e => h (Fin.ext (by
    have := congrArg Fin.val e; simp only at this; omega)))
  interval_property S hS := by
    have h := (F.interval_property S hS).out
    refine ⟨fun x hx y hy z hz => ?_⟩
    have hz1 := Fin.le_def.mp hz.1
    have hz2 := Fin.le_def.mp hz.2
    exact h (x := ⟨x.val + j, by have := x.isLt; omega⟩) hx (y := ⟨y.val + j, by have := y.isLt; omega⟩) hy
      ⟨Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr (by omega)⟩

theorem olb_suf_vs {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (j : ℕ)
    (hj : j < F.k) (t : Fin (olb_suf F j hj).k) :
    olb_vs (olb_suf F j hj) t = olb_vs F ⟨t.val + j, by have := t.isLt; simp [olb_suf] at this; omega⟩ :=
  rfl

def olb_link {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (v : V) (m : ℕ)
    (hm0 : 0 < m) (hm : m ≤ F.k)
    (hv : ∀ t : Fin F.k, t.val < m → v ∈ olb_vs F t) : OneLayeredFamily V (r - 1) where
  k := m
  k_pos := hm0
  layers t := ((F.layers ⟨t.val, by omega⟩).filter (fun G => v ∈ G)).image (fun G => G.erase v)
  layers_nonempty t := by
    obtain ⟨G, hG, hv'⟩ := (olb_mem_vs F _ v).mp (hv ⟨t.val, by omega⟩ t.isLt)
    exact ⟨G.erase v, Finset.mem_image.mpr ⟨G, Finset.mem_filter.mpr ⟨hG, hv'⟩, rfl⟩⟩
  layers_card t G hG := by
    obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
    rw [Finset.mem_filter] at hG'
    rw [Finset.card_erase_of_mem hG'.2, F.layers_card _ _ hG'.1]
  layers_disjoint t₁ t₂ h := by
    rw [Finset.disjoint_left]
    intro G h1 h2
    obtain ⟨G1, hG1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨G2, hG2, he⟩ := Finset.mem_image.mp h2
    rw [Finset.mem_filter] at hG1 hG2
    have : G2 = G1 := by rw [← Finset.insert_erase hG1.2, ← Finset.insert_erase hG2.2, he]
    subst this
    exact Finset.disjoint_left.mp (F.layers_disjoint _ _ (fun e => h (Fin.ext (by
      have := congrArg Fin.val e; simp only at this; omega)))) hG1.1 hG2.1
  interval_property S hS := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨G1, hG1, hS1⟩ := hx
    obtain ⟨G2, hG2, hS2⟩ := hy
    obtain ⟨H1, hH1, rfl⟩ := Finset.mem_image.mp hG1
    obtain ⟨H2, hH2, rfl⟩ := Finset.mem_image.mp hG2
    rw [Finset.mem_filter] at hH1 hH2
    have hvS : v ∉ S := fun h => Finset.notMem_erase v H1 (hS1 h)
    have h := (F.interval_property (insert v S) (Finset.insert_nonempty v S)).out
    have hz1 := Fin.le_def.mp hz.1
    have hz2 := Fin.le_def.mp hz.2
    have hxl : x.val < F.k := by have := x.isLt; omega
    have hyl : y.val < F.k := by have := y.isLt; omega
    have hzl : z.val < F.k := by have := z.isLt; omega
    have hx' : (⟨x.val, hxl⟩ : Fin F.k) ∈ {t : Fin F.k | ∃ G ∈ F.layers t, insert v S ⊆ G} :=
      ⟨H1, hH1.1, Finset.insert_subset hH1.2 (hS1.trans (Finset.erase_subset v H1))⟩
    have hy' : (⟨y.val, hyl⟩ : Fin F.k) ∈ {t : Fin F.k | ∃ G ∈ F.layers t, insert v S ⊆ G} :=
      ⟨H2, hH2.1, Finset.insert_subset hH2.2 (hS2.trans (Finset.erase_subset v H2))⟩
    have hzm : (⟨z.val, hzl⟩ : Fin F.k) ∈ Set.Icc (⟨x.val, hxl⟩ : Fin F.k) ⟨y.val, hyl⟩ :=
      ⟨Fin.mk_le_mk.mpr hz1, Fin.mk_le_mk.mpr hz2⟩
    obtain ⟨H3, hH3, hS3⟩ := h hx' hy' hzm
    refine ⟨H3.erase v, Finset.mem_image.mpr ⟨H3, Finset.mem_filter.mpr
      ⟨hH3, hS3 (Finset.mem_insert_self v S)⟩, rfl⟩, ?_⟩
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun e => hvS (e ▸ hw), hS3 (Finset.mem_insert_of_mem hw)⟩

theorem olb_link_U {V : Type*} [DecidableEq V] {r : ℕ} (F : OneLayeredFamily V r) (v : V) (m : ℕ)
    (hm0 : 0 < m) (hm : m ≤ F.k) (hv : ∀ t : Fin F.k, t.val < m → v ∈ olb_vs F t) :
    olb_U (olb_link F v m hm0 hm hv) ⊆
      ((Finset.univ.filter (fun t : Fin F.k => t.val < m)).biUnion (olb_vs F)).erase v := by
  intro w hw
  simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and, olb_vs, id] at hw
  obtain ⟨t, G, hG, hwG⟩ := hw
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hG
  rw [Finset.mem_filter] at hH
  rw [Finset.mem_erase] at hwG
  refine Finset.mem_erase.mpr ⟨hwG.1, ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨t.val, by have : t.val < m := t.isLt; omega⟩, t.isLt, (olb_mem_vs F _ w).mpr ⟨H, hH.1, hwG.2⟩⟩
theorem olb_ar1 (c k a U r g : ℕ) (hG : k + c * r ≤ c * g + 1) (hg : g + 1 ≤ U) (ha : a ≤ U) :
    k + c * (a + (r + 1)) ≤ c * (2 * U) + 1 := by
  have h1 : c * (g + 1) ≤ c * U := Nat.mul_le_mul_left c hg
  have h2 : c * a ≤ c * U := Nat.mul_le_mul_left c ha
  nlinarith

theorem olb_ar2 (c k l1 d a U r g n1 a' R uR : ℕ) (hc : 1 ≤ c) (hr : 1 ≤ r) (hk : k = l1 + d)
    (hG : l1 + c * r ≤ c * g + 1) (hg : g + 1 ≤ n1)
    (hR : d + c * (a' + (r + 1)) ≤ c * (2 * uR) + 1) (huR : uR ≤ R)
    (h3 : n1 + R ≤ U + a') (h4 : a + R ≤ U) :
    k + c * (a + (r + 1)) ≤ c * (2 * U) + 1 := by
  have m1 : c * (g + 1) ≤ c * n1 := Nat.mul_le_mul_left c hg
  have m2 : c * uR ≤ c * R := Nat.mul_le_mul_left c huR
  have m3 : c * (n1 + R) ≤ c * (U + a') := Nat.mul_le_mul_left c h3
  have m4 : c * (a + R) ≤ c * U := Nat.mul_le_mul_left c h4
  have m5 : 1 * 2 ≤ c * (r + 1) := Nat.mul_le_mul hc (by omega)
  subst hk
  nlinarith

theorem olb_one {V : Type*} [DecidableEq V] (F : OneLayeredFamily V 1) :
    F.k ≤ (olb_U F).card := by
  choose u hu using F.layers_nonempty
  have hc : ∀ t, (u t).card = 1 := fun t => F.layers_card t (u t) (hu t)
  choose w hw using fun t => Finset.card_eq_one.mp (hc t)
  calc F.k = (Finset.univ : Finset (Fin F.k)).card := by simp
    _ ≤ (olb_U F).card := Finset.card_le_card_of_injOn w (by
        intro t _
        rw [Finset.mem_coe, olb_U, Finset.mem_biUnion]
        exact ⟨t, Finset.mem_univ _, (olb_mem_vs F t _).mpr ⟨u t, hu t, by rw [hw t]; exact Finset.mem_singleton_self _⟩⟩)
        (by
        intro s _ t _ hst
        by_contra hne
        have hus : u s = u t := by rw [hw s, hw t, hst]
        exact Finset.disjoint_left.mp (F.layers_disjoint s t hne) (hu s) (by rw [hus]; exact hu t))

theorem olb_main {V : Type*} [DecidableEq V] (r : ℕ) (hr : 1 ≤ r) : ∀ F : OneLayeredFamily V r,
    F.k + 2 ^ (r - 1) * r ≤ 2 ^ (r - 1) * (olb_U F).card + 1 := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro F
    have := olb_one F
    simp only [Nat.sub_self, pow_zero, one_mul]
    omega
  | succ r hr ih =>
    have block : ∀ n, ∀ F : OneLayeredFamily V (r + 1), F.k = n →
        F.k + 2 ^ (r - 1) * ((olb_vs F ⟨0, F.k_pos⟩).card + (r + 1)) ≤
          2 ^ (r - 1) * (2 * (olb_U F).card) + 1 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n IH =>
      intro F hFn
      have hc1 : 1 ≤ 2 ^ (r - 1) := Nat.one_le_two_pow
      have hA0 : (olb_vs F ⟨0, F.k_pos⟩).Nonempty := by
        obtain ⟨G, hG⟩ := F.layers_nonempty ⟨0, F.k_pos⟩
        have := F.layers_card _ G hG
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < G.card)
        exact ⟨w, (olb_mem_vs F _ w).mpr ⟨G, hG, hw⟩⟩
      have ht0S : (⟨0, F.k_pos⟩ : Fin F.k) ∈ Finset.univ.filter
          (fun t : Fin F.k => ¬ Disjoint (olb_vs F t) (olb_vs F ⟨0, F.k_pos⟩)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_self_iff_empty]
        exact hA0.ne_empty
      set l := (Finset.univ.filter
          (fun t : Fin F.k => ¬ Disjoint (olb_vs F t) (olb_vs F ⟨0, F.k_pos⟩))).max' ⟨_, ht0S⟩ with hl
      have hlS := Finset.max'_mem (Finset.univ.filter
          (fun t : Fin F.k => ¬ Disjoint (olb_vs F t) (olb_vs F ⟨0, F.k_pos⟩))) ⟨_, ht0S⟩
      rw [← hl] at hlS
      have hmax : ∀ t, ¬ Disjoint (olb_vs F t) (olb_vs F ⟨0, F.k_pos⟩) → t ≤ l := fun t ht =>
        Finset.le_max' _ t (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)
      obtain ⟨v, hvl, hv0⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hlS).2
      have hvall : ∀ t : Fin F.k, t.val < l.val + 1 → v ∈ olb_vs F t := fun t ht =>
        olb_vs_mid F hv0 hvl (Fin.le_def.mpr (Nat.zero_le _)) (Fin.le_def.mpr (by omega))
      have hlk : l.val + 1 ≤ F.k := l.isLt
      have hm0 : 0 < l.val + 1 := Nat.succ_pos _
      have hG : (l.val + 1) + 2 ^ (r - 1) * r ≤
          2 ^ (r - 1) * (olb_U (r := r) (olb_link F v (l.val + 1) hm0 hlk hvall)).card + 1 :=
        ih (olb_link F v (l.val + 1) hm0 hlk hvall)
      have hGk : (olb_link F v (l.val + 1) hm0 hlk hvall).k = l.val + 1 := rfl
      have hvB1 : v ∈ (Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion
          (olb_vs F) := by
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨0, F.k_pos⟩, Nat.succ_pos _, hv0⟩
      have hGU0 := Finset.card_le_card (olb_link_U F v (l.val + 1) hm0 hlk hvall)
      rw [Finset.card_erase_of_mem hvB1] at hGU0
      have hGU : (olb_U (r := r) (olb_link F v (l.val + 1) hm0 hlk hvall)).card ≤
          ((Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion (olb_vs F)).card - 1 :=
        hGU0
      have hB1pos := Finset.card_pos.mpr ⟨v, hvB1⟩
      have hAU : olb_vs F ⟨0, F.k_pos⟩ ⊆ olb_U F := fun w hw => by
        simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨_, hw⟩
      have hAB1 : olb_vs F ⟨0, F.k_pos⟩ ⊆ (Finset.univ.filter
          (fun t : Fin F.k => t.val < l.val + 1)).biUnion (olb_vs F) := fun w hw => by
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨0, F.k_pos⟩, Nat.succ_pos _, hw⟩
      by_cases hend : l.val + 1 = F.k
      · have hB1eq : (Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion
            (olb_vs F) = olb_U F := by
          ext w
          simp only [olb_U, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨t, -, ht⟩; exact ⟨t, ht⟩
          · rintro ⟨t, ht⟩; exact ⟨t, by have := t.isLt; omega, ht⟩
        rw [hB1eq] at hGU hB1pos
        have := olb_ar1 _ (l.val + 1) _ (olb_U F).card _ _ hG (by omega) (Finset.card_le_card hAU)
        rw [hend] at this
        exact this
      · have hj : l.val + 1 < F.k := by omega
        have hRk : (olb_suf F (l.val + 1) hj).k < n := by
          show F.k - (l.val + 1) < n
          omega
        have hR := IH _ hRk (olb_suf F (l.val + 1) hj) rfl
        have hA' : olb_vs (olb_suf F (l.val + 1) hj) ⟨0, (olb_suf F (l.val + 1) hj).k_pos⟩ =
            olb_vs F ⟨l.val + 1, hj⟩ := by
          rw [olb_suf_vs]
          congr 1
          ext
          simp
        rw [hA'] at hR
        have hUR : olb_U (olb_suf F (l.val + 1) hj) ⊆
            (Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion (olb_vs F) := by
          intro w hw
          simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
          obtain ⟨t, ht⟩ := hw
          rw [olb_suf_vs] at ht
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨_, by simp only; omega, ht⟩
        have hinter : (Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion
            (olb_vs F) ∩ (Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion
            (olb_vs F) ⊆ olb_vs F ⟨l.val + 1, hj⟩ := by
          intro w hw
          simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
            true_and] at hw
          obtain ⟨⟨s, hs, hws⟩, ⟨t, ht, hwt⟩⟩ := hw
          exact olb_vs_mid F hws hwt (Fin.le_def.mpr (by simp only; omega))
            (Fin.le_def.mpr (by simp only; omega))
        have hdisj : Disjoint (olb_vs F ⟨0, F.k_pos⟩)
            ((Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion (olb_vs F)) := by
          rw [Finset.disjoint_left]
          intro w hw0 hw
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          obtain ⟨t, ht, hwt⟩ := hw
          have := Fin.le_def.mp (hmax t (Finset.not_disjoint_iff.mpr ⟨w, hwt, hw0⟩))
          omega
        have hR'U : (Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion
            (olb_vs F) ⊆ olb_U F := fun w hw => by
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          obtain ⟨t, -, hwt⟩ := hw
          simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨t, hwt⟩
        have hB1U : (Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion
            (olb_vs F) ⊆ olb_U F := fun w hw => by
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          obtain ⟨t, -, hwt⟩ := hw
          simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨t, hwt⟩
        have k1 := Finset.card_union_add_card_inter
          ((Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion (olb_vs F))
          ((Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion (olb_vs F))
        have k2 := Finset.card_le_card (Finset.union_subset hB1U hR'U)
        have k3 := Finset.card_le_card hinter
        have k4 := Finset.card_union_of_disjoint hdisj
        have k5 := Finset.card_le_card (Finset.union_subset hAU hR'U)
        have k6 := Finset.card_le_card hUR
        have hRk' : (olb_suf F (l.val + 1) hj).k = F.k - (l.val + 1) := rfl
        rw [hRk'] at hR
        exact olb_ar2 (k := F.k) (U := (olb_U F).card)
          (n1 := ((Finset.univ.filter (fun t : Fin F.k => t.val < l.val + 1)).biUnion (olb_vs F)).card)
          (R := ((Finset.univ.filter (fun t : Fin F.k => l.val + 1 ≤ t.val)).biUnion (olb_vs F)).card)
          _ (l.val + 1) (F.k - (l.val + 1)) _ _ _ _ _ hc1 hr (by omega) hG
          (by omega) hR k6 (by omega) (by omega)
    intro F
    have hb := block _ F rfl
    have ha : r + 1 ≤ (olb_vs F ⟨0, F.k_pos⟩).card := by
      obtain ⟨G, hG⟩ := F.layers_nonempty ⟨0, F.k_pos⟩
      calc r + 1 = G.card := (F.layers_card _ G hG).symm
        _ ≤ _ := Finset.card_le_card (fun w hw => (olb_mem_vs F _ w).mpr ⟨G, hG, hw⟩)
    have hp : 2 ^ (r + 1 - 1) = 2 * 2 ^ (r - 1) := by
      rw [Nat.add_sub_cancel, ← pow_succ']
      congr 1
      omega
    rw [hp]
    have m := Nat.mul_le_mul_left (2 ^ (r - 1)) ha
    nlinarith

/-- The linear upper bound F(m, r) ≤ 2^(r-1)(m-r) + 1. -/
theorem one_layered_linear_bound (m r : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    one_layered_max_layers m r ≤ 2 ^ (r - 1) * (m - r) + 1 := by
  unfold one_layered_max_layers
  refine csSup_le' ?_
  rintro k ⟨n, hn, F, rfl⟩
  have h := olb_main r hr F
  have hU : (olb_U F).card ≤ m := (Finset.card_le_univ _).trans (by simp [hn])
  have hrU : r ≤ (olb_U F).card := by
    obtain ⟨G, hG⟩ := F.layers_nonempty ⟨0, F.k_pos⟩
    refine (F.layers_card _ G hG).symm.le.trans (Finset.card_le_card (fun w hw => ?_))
    simp only [olb_U, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨⟨0, F.k_pos⟩, (olb_mem_vs F _ w).mpr ⟨G, hG, hw⟩⟩
  have e : 2 ^ (r - 1) * (olb_U F).card ≤ 2 ^ (r - 1) * (m - r) + 2 ^ (r - 1) * r := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  omega
