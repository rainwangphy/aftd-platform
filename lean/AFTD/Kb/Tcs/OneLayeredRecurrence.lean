import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.Tcs.OneLayeredFamily
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.F

/-!
# one_layered_recurrence

Topic: combinatorics   Node: 542b25a444d9

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 2, Equation (1)

For integers r ≥ 2 and m ≥ r, the maximum number of layers F(m, r) satisfies F(m, r) ≤ F(⌊(m - 1) / 2⌋, r) + F(⌈(m - 1) / 2⌉, r) + F(m - 1, r - 1), where ⌈(m - 1) / 2⌉ is represented by m / 2.
-/

open Classical

private def one_layered_recurrence_fsf {V : Type*} [DecidableEq V] (W s : Finset V) : Finset ↥W :=
  W.attach.filter (fun x => x.1 ∈ s)

private lemma one_layered_recurrence_fsf_mem {V : Type*} [DecidableEq V] {W s : Finset V} {x : ↥W} :
    x ∈ one_layered_recurrence_fsf W s ↔ x.1 ∈ s := by
  simp [one_layered_recurrence_fsf]

private lemma one_layered_recurrence_fsf_card {V : Type*} [DecidableEq V] {W s : Finset V} (h : s ⊆ W) :
    (one_layered_recurrence_fsf W s).card = s.card := by
  have heq : one_layered_recurrence_fsf W s = s.attach.map ⟨fun x => (⟨x.1, h x.2⟩ : ↥W),
      fun a b hab => Subtype.ext (by
        have := congrArg (fun z : ↥W => (z : V)) hab
        simpa using this)⟩ := by
    ext y
    simp only [one_layered_recurrence_fsf, Finset.mem_map, Finset.mem_filter, Finset.mem_attach]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨⟨y.1, hy⟩, ⟨⟩, Subtype.ext rfl⟩
    · rintro ⟨a, -, ha⟩
      rw [← ha]
      exact ⟨⟨⟩, a.2⟩
  rw [heq, Finset.card_map, Finset.card_attach]

private lemma one_layered_recurrence_fsf_inj {V : Type*} [DecidableEq V] {W s₁ s₂ : Finset V}
    (h₁ : s₁ ⊆ W) (h₂ : s₂ ⊆ W) (he : one_layered_recurrence_fsf W s₁ = one_layered_recurrence_fsf W s₂) :
    s₁ = s₂ := by
  ext x
  constructor
  · intro hx
    have hm : (⟨x, h₁ hx⟩ : ↥W) ∈ one_layered_recurrence_fsf W s₁ :=
      one_layered_recurrence_fsf_mem.mpr hx
    rw [he] at hm
    exact one_layered_recurrence_fsf_mem.mp hm
  · intro hx
    have hm : (⟨x, h₂ hx⟩ : ↥W) ∈ one_layered_recurrence_fsf W s₂ :=
      one_layered_recurrence_fsf_mem.mpr hx
    rw [← he] at hm
    exact one_layered_recurrence_fsf_mem.mp hm

private lemma one_layered_recurrence_fsf_subset_iff {V : Type*} [DecidableEq V] {W G : Finset V}
    (S : Finset ↥W) :
    S ⊆ one_layered_recurrence_fsf W G ↔
      S.map ⟨fun x : ↥W => x.1, fun a b h => Subtype.ext h⟩ ⊆ G := by
  constructor
  · intro h x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact one_layered_recurrence_fsf_mem.mp (h hy)
  · intro h y hy
    rw [one_layered_recurrence_fsf_mem]
    exact h (Finset.mem_map.mpr ⟨y, hy, rfl⟩)

open Classical in
noncomputable def one_layered_recurrence_restrict {V : Type*} [DecidableEq V] {r : ℕ}
    (F : OneLayeredFamily V r) (W : Finset V) (hW : ∀ t, ∀ G ∈ F.layers t, G ⊆ W) :
    OneLayeredFamily ↥W r where
  k := F.k
  k_pos := F.k_pos
  layers t := (F.layers t).attach.map ⟨fun p => one_layered_recurrence_fsf W p.1, by
    intro p q hpq
    exact Subtype.ext (one_layered_recurrence_fsf_inj (hW t p.1 p.2) (hW t q.1 q.2) hpq)⟩
  layers_nonempty t := by
    obtain ⟨G, hG⟩ := F.layers_nonempty t
    exact ⟨one_layered_recurrence_fsf W G,
      Finset.mem_map.mpr ⟨⟨G, hG⟩, Finset.mem_attach _ _, rfl⟩⟩
  layers_card t G hG := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hG
    exact (one_layered_recurrence_fsf_card (hW t p.1 p.2)).trans (F.layers_card t p.1 p.2)
  layers_disjoint t₁ t₂ hne := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨q, hq, hab⟩ := Finset.mem_map.mp hb
    have hpq : p.1 = q.1 := one_layered_recurrence_fsf_inj (hW t₁ p.1 p.2) (hW t₂ q.1 q.2) hab.symm
    exact (Finset.disjoint_left.mp (F.layers_disjoint t₁ t₂ hne)) p.2 (hpq ▸ q.2)
  interval_property S hS := by
    have hSne : (S.map ⟨fun x : ↥W => x.1, fun a b h => Subtype.ext h⟩).Nonempty :=
      Finset.Nonempty.map (f := ⟨fun x : ↥W => x.1, fun a b h => Subtype.ext h⟩) hS
    have h := F.interval_property (S.map ⟨fun x : ↥W => x.1, fun a b h => Subtype.ext h⟩) hSne
    convert h using 2
    ext t
    constructor
    · rintro ⟨a, ha, hSa⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ha
      exact ⟨p.1, p.2, (one_layered_recurrence_fsf_subset_iff S).mp hSa⟩
    · rintro ⟨G, hG, hSG⟩
      exact ⟨one_layered_recurrence_fsf W G,
        Finset.mem_map.mpr ⟨⟨G, hG⟩, Finset.mem_attach _ _, rfl⟩,
        (one_layered_recurrence_fsf_subset_iff S).mpr hSG⟩

private lemma one_layered_recurrence_map_subset_iff {V W : Type*} (e : V ≃ W) (S : Finset W) (G : Finset V) :
    S ⊆ G.map e.toEmbedding ↔ S.map e.symm.toEmbedding ⊆ G := by
  constructor
  · intro h x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem : y ∈ G.map e.toEmbedding := h hy
    rw [Finset.mem_map] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have hzy : z = e.symm y := by rw [← hze]; simp
    rwa [hzy] at hz
  · intro h y hy
    rw [Finset.mem_map]
    refine ⟨e.symm y, ?_, by simp⟩
    exact h (Finset.mem_map.mpr ⟨y, hy, by simp⟩)

open Classical in
noncomputable def one_layered_recurrence_equivMap {V W : Type*} {r : ℕ} (e : V ≃ W)
    (F : OneLayeredFamily V r) : OneLayeredFamily W r where
  k := F.k
  k_pos := F.k_pos
  layers t := (F.layers t).image (fun G => G.map e.toEmbedding)
  layers_nonempty t := Finset.Nonempty.image (F.layers_nonempty t) _
  layers_card t G hG := by
    obtain ⟨G₀, hG₀, rfl⟩ := Finset.mem_image.mp hG
    rw [Finset.card_map]
    exact F.layers_card t G₀ hG₀
  layers_disjoint t₁ t₂ hne := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨G₁, hG₁, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨G₂, hG₂, hab⟩ := Finset.mem_image.mp hb
    have hG_eq : G₂ = G₁ := Finset.map_injective e.toEmbedding hab
    exact (Finset.disjoint_left.mp (F.layers_disjoint t₁ t₂ hne)) hG₁ (hG_eq ▸ hG₂)
  interval_property S hS := by
    have hT : (S.map e.symm.toEmbedding).Nonempty :=
      Finset.Nonempty.map (f := e.symm.toEmbedding) hS
    have h := F.interval_property (S.map e.symm.toEmbedding) hT
    convert h using 2
    ext t
    constructor
    · rintro ⟨a, ha, hSa⟩
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨G, hG, (one_layered_recurrence_map_subset_iff e S G).mp hSa⟩
    · rintro ⟨G, hG, hSG⟩
      exact ⟨G.map e.toEmbedding, Finset.mem_image.mpr ⟨G, hG, rfl⟩,
        (one_layered_recurrence_map_subset_iff e S G).mpr hSG⟩

open Classical in
noncomputable def one_layered_recurrence_block {V : Type*} {r : ℕ}
    (F : OneLayeredFamily V r) (lo hi : ℕ) (hlt : lo < hi) (hhi : hi ≤ F.k) :
    OneLayeredFamily V r where
  k := hi - lo
  k_pos := by omega
  layers i := F.layers ⟨lo + i.val, by have := i.isLt; omega⟩
  layers_nonempty i := F.layers_nonempty _
  layers_card i := F.layers_card _
  layers_disjoint i₁ i₂ h := by
    refine F.layers_disjoint _ _ ?_
    intro hc
    exact h (Fin.ext (by simpa using congrArg Fin.val hc))
  interval_property S hS := by
    have hf : Monotone (fun i : Fin (hi - lo) => (⟨lo + i.val, by have := i.isLt; omega⟩ : Fin F.k)) := by
      intro i j hij
      simp only [Fin.le_iff_val_le_val] at *
      omega
    exact (F.interval_property S hS).preimage_mono hf

private lemma one_layered_recurrence_subset_erase_iff {V : Type*} [DecidableEq V] {S F : Finset V} {v : V} :
    S ⊆ F.erase v ↔ v ∉ S ∧ S ⊆ F := by
  constructor
  · intro h
    refine ⟨?_, fun x hx => Finset.mem_of_mem_erase (h hx)⟩
    intro hv
    have := h hv
    rw [Finset.mem_erase] at this
    exact this.1 rfl
  · rintro ⟨hvS, hSF⟩ x hx
    rw [Finset.mem_erase]
    exact ⟨fun hxv => hvS (hxv ▸ hx), hSF hx⟩

private def one_layered_recurrence_linkLayer {V : Type*} [DecidableEq V] {r : ℕ}
    (G : OneLayeredFamily V r) (v : V) (t : Fin G.k) : Finset (Finset V) :=
  ((G.layers t).filter (fun F => v ∈ F)).image (fun F => F.erase v)

private lemma one_layered_recurrence_linkLayer_mem {V : Type*} [DecidableEq V] {r : ℕ}
    {G : OneLayeredFamily V r} {v : V} {t : Fin G.k} {a : Finset V} :
    a ∈ one_layered_recurrence_linkLayer G v t ↔ ∃ F ∈ G.layers t, v ∈ F ∧ F.erase v = a := by
  simp only [one_layered_recurrence_linkLayer, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨F, ⟨hF, hvF⟩, rfl⟩
    exact ⟨F, hF, hvF, rfl⟩
  · rintro ⟨F, hF, hvF, rfl⟩
    exact ⟨F, ⟨hF, hvF⟩, rfl⟩

open Classical in
noncomputable def one_layered_recurrence_link {V : Type*} [DecidableEq V] {r : ℕ}
    (G : OneLayeredFamily V r) (v : V) (hv : ∀ t, ∃ F ∈ G.layers t, v ∈ F) :
    OneLayeredFamily V (r - 1) where
  k := G.k
  k_pos := G.k_pos
  layers t := one_layered_recurrence_linkLayer G v t
  layers_nonempty t := by
    obtain ⟨F, hF, hvF⟩ := hv t
    exact ⟨F.erase v, one_layered_recurrence_linkLayer_mem.mpr ⟨F, hF, hvF, rfl⟩⟩
  layers_card t F' hF' := by
    obtain ⟨F, hF, hvF, rfl⟩ := one_layered_recurrence_linkLayer_mem.mp hF'
    rw [Finset.card_erase_of_mem hvF, G.layers_card t F hF]
  layers_disjoint t₁ t₂ hne := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨F₁, hF₁, hv₁, rfl⟩ := one_layered_recurrence_linkLayer_mem.mp ha
    obtain ⟨F₂, hF₂, hv₂, hab⟩ := one_layered_recurrence_linkLayer_mem.mp hb
    have hEq : F₂ = F₁ := by
      rw [← Finset.insert_erase hv₂, ← Finset.insert_erase hv₁, hab]
    exact (Finset.disjoint_left.mp (G.layers_disjoint t₁ t₂ hne)) hF₁ (hEq ▸ hF₂)
  interval_property S hS := by
    by_cases hvS : v ∈ S
    · have hempty : {t : Fin G.k | ∃ a ∈ one_layered_recurrence_linkLayer G v t, S ⊆ a} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro a ha hSa
        obtain ⟨F, hF, hvF, rfl⟩ := one_layered_recurrence_linkLayer_mem.mp ha
        have : v ∈ F.erase v := hSa hvS
        simpa using this
      rw [hempty]
      exact Set.ordConnected_empty
    · have h := G.interval_property (insert v S) (Finset.insert_nonempty _ _)
      convert h using 2
      ext t
      constructor
      · rintro ⟨a, ha, hSa⟩
        obtain ⟨F, hF, hvF, rfl⟩ := one_layered_recurrence_linkLayer_mem.mp ha
        exact ⟨F, hF, Finset.insert_subset hvF (one_layered_recurrence_subset_erase_iff.mp hSa).2⟩
      · rintro ⟨F, hF, hSF⟩
        have hvF : v ∈ F := hSF (Finset.mem_insert_self v S)
        exact ⟨F.erase v, one_layered_recurrence_linkLayer_mem.mpr ⟨F, hF, hvF, rfl⟩,
          one_layered_recurrence_subset_erase_iff.mpr ⟨hvS, fun x hx => hSF (Finset.mem_insert_of_mem hx)⟩⟩

private noncomputable def one_layered_recurrence_layerUnion {V : Type*} [DecidableEq V] {r : ℕ}
    (F : OneLayeredFamily V r) (t : Fin F.k) : Finset V :=
  (F.layers t).biUnion (fun G => G)

private lemma one_layered_recurrence_layerUnion_mem {V : Type*} [DecidableEq V] {r : ℕ}
    {F : OneLayeredFamily V r} {t : Fin F.k} {x : V} :
    x ∈ one_layered_recurrence_layerUnion F t ↔ ∃ G ∈ F.layers t, x ∈ G := by
  simp [one_layered_recurrence_layerUnion, Finset.mem_biUnion]

private noncomputable def one_layered_recurrence_union {V : Type*} [DecidableEq V] {r : ℕ}
    (F : OneLayeredFamily V r) (lo hi : ℕ) : Finset V :=
  (Finset.Ico lo hi).biUnion (fun t => if h : t < F.k then one_layered_recurrence_layerUnion F ⟨t, h⟩ else ∅)

private lemma one_layered_recurrence_union_mem {V : Type*} [DecidableEq V] {r : ℕ} {F : OneLayeredFamily V r}
    {lo hi : ℕ} {x : V} :
    x ∈ one_layered_recurrence_union F lo hi ↔
      ∃ t, lo ≤ t ∧ t < hi ∧ ∃ (h : t < F.k), ∃ G ∈ F.layers ⟨t, h⟩, x ∈ G := by
  rw [one_layered_recurrence_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [Finset.mem_Ico] at ht
    by_cases h : t < F.k
    · rw [dif_pos h] at hx
      exact ⟨t, ht.1, ht.2, h, one_layered_recurrence_layerUnion_mem.mp hx⟩
    · rw [dif_neg h] at hx
      exact absurd hx (Finset.notMem_empty x)
  · rintro ⟨t, ht₁, ht₂, h, hx⟩
    refine ⟨t, Finset.mem_Ico.mpr ⟨ht₁, ht₂⟩, ?_⟩
    rw [dif_pos h]
    exact one_layered_recurrence_layerUnion_mem.mpr hx

private lemma one_layered_recurrence_union_self {V : Type*} [DecidableEq V] {r : ℕ}
    (F : OneLayeredFamily V r) (lo : ℕ) : one_layered_recurrence_union F lo lo = ∅ := by
  simp [one_layered_recurrence_union]

private lemma one_layered_recurrence_block_union_subset {V : Type*} [DecidableEq V] {r : ℕ}
    {F : OneLayeredFamily V r} {lo hi : ℕ} (hlt : lo < hi) (hhi : hi ≤ F.k) :
    ∀ t, ∀ G ∈ (one_layered_recurrence_block F lo hi hlt hhi).layers t,
      G ⊆ one_layered_recurrence_union F lo hi := by
  intro t G hG x hx
  have ht : t.val < hi - lo := t.isLt
  rw [one_layered_recurrence_union_mem]
  exact ⟨lo + t.val, by omega, by omega, by omega, G, hG, hx⟩

private def one_layered_recurrence_set (m r : ℕ) : Set ℕ :=
  {k : ℕ | ∃ n ≤ m, ∃ F : OneLayeredFamily (Fin n) r, F.k = k}

private lemma one_layered_recurrence_eq_sSup (m r : ℕ) :
    one_layered_max_layers m r = sSup (one_layered_recurrence_set m r) := rfl

private lemma one_layered_recurrence_bddAbove (m r : ℕ) : BddAbove (one_layered_recurrence_set m r) := by
  refine ⟨2 ^ m, ?_⟩
  rintro k ⟨n, hn, F, rfl⟩
  have hinj : Function.Injective (fun t : Fin F.k => Classical.choose (F.layers_nonempty t)) := by
    intro t₁ t₂ heq
    have heq' : Classical.choose (F.layers_nonempty t₁) = Classical.choose (F.layers_nonempty t₂) := heq
    by_contra hne
    have h1 : Classical.choose (F.layers_nonempty t₁) ∈ F.layers t₁ :=
      Classical.choose_spec (F.layers_nonempty t₁)
    have h2 : Classical.choose (F.layers_nonempty t₂) ∈ F.layers t₂ :=
      Classical.choose_spec (F.layers_nonempty t₂)
    exact (Finset.disjoint_left.mp (F.layers_disjoint t₁ t₂ hne)) h1 (heq' ▸ h2)
  have h1 : F.k ≤ Fintype.card (Finset (Fin n)) := by
    have := Fintype.card_le_of_injective
      (fun t : Fin F.k => Classical.choose (F.layers_nonempty t)) hinj
    simpa using this
  rw [Fintype.card_finset, Fintype.card_fin] at h1
  calc F.k ≤ 2 ^ n := h1
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hn

private lemma one_layered_recurrence_le_of_family {V : Type*} [Fintype V] {r : ℕ}
    (F : OneLayeredFamily V r) {m : ℕ} (hm : Fintype.card V ≤ m) :
    F.k ≤ one_layered_max_layers m r := by
  rw [one_layered_recurrence_eq_sSup]
  apply le_csSup (one_layered_recurrence_bddAbove m r)
  exact ⟨Fintype.card V, hm, one_layered_recurrence_equivMap (Fintype.equivFin V) F, rfl⟩

private lemma one_layered_recurrence_mono {m₁ m₂ r : ℕ} (h : m₁ ≤ m₂) :
    one_layered_max_layers m₁ r ≤ one_layered_max_layers m₂ r := by
  rw [one_layered_recurrence_eq_sSup, one_layered_recurrence_eq_sSup]
  by_cases hne : (one_layered_recurrence_set m₁ r).Nonempty
  · apply csSup_le_csSup (one_layered_recurrence_bddAbove m₂ r) hne
    rintro k ⟨n, hn, F, hk⟩
    exact ⟨n, le_trans hn h, F, hk⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

private noncomputable def one_layered_recurrence_oneLayer (r : ℕ) : OneLayeredFamily (Fin r) r where
  k := 1
  k_pos := Nat.one_pos
  layers _ := {Finset.univ}
  layers_nonempty _ := ⟨Finset.univ, Finset.mem_singleton_self _⟩
  layers_card _ G hG := by
    rw [Finset.mem_singleton] at hG
    subst hG
    rw [Finset.card_univ, Fintype.card_fin]
  layers_disjoint t₁ t₂ hne := by
    have : t₁ = t₂ := Subsingleton.elim _ _
    exact absurd this hne
  interval_property S hS := by
    refine Set.OrdConnected.mk ?_
    intro x hx y hy z hz
    have hxz : z = x := Subsingleton.elim z x
    rwa [hxz]

private lemma one_layered_recurrence_set_nonempty {m r : ℕ} (hm : r ≤ m) :
    (one_layered_recurrence_set m r).Nonempty :=
  ⟨1, r, hm, one_layered_recurrence_oneLayer r, rfl⟩

private lemma one_layered_recurrence_half_sum (m : ℕ) : (m - 1) / 2 + m / 2 = m - 1 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases k with _ | j
    · subst hk; simp
    · have hm : m = 2*j + 2 := by omega
      have h1 : (m-1)/2 = j := by apply Nat.div_eq_of_lt_le <;> omega
      have h2 : m/2 = j+1 := by apply Nat.div_eq_of_lt_le <;> omega
      omega
  · have hm : m = 2*k + 1 := by omega
    have h1 : (m-1)/2 = k := by apply Nat.div_eq_of_lt_le <;> omega
    have h2 : m/2 = k := by apply Nat.div_eq_of_lt_le <;> omega
    omega

private lemma one_layered_recurrence_aux {n m r : ℕ} (hr : 2 ≤ r) (hn : n ≤ m)
    (F : OneLayeredFamily (Fin n) r) :
    F.k ≤ one_layered_max_layers ((m - 1) / 2) r +
      one_layered_max_layers (m / 2) r + one_layered_max_layers (m - 1) (r - 1) := by
  classical
  have hhalf : (m - 1) / 2 + m / 2 = m - 1 := one_layered_recurrence_half_sum m
  let j := Nat.findGreatest (fun s => (one_layered_recurrence_union F 0 s).card ≤ (m - 1) / 2) F.k
  have hjle : j ≤ F.k := Nat.findGreatest_le F.k
  have hjcard : (one_layered_recurrence_union F 0 j).card ≤ (m - 1) / 2 :=
    Nat.findGreatest_spec (P := fun s => (one_layered_recurrence_union F 0 s).card ≤ (m - 1) / 2)
      (m := 0) (n := F.k) (by omega) (by simp [one_layered_recurrence_union])
  have hjmax : ∀ s, j < s → s ≤ F.k → ¬ (one_layered_recurrence_union F 0 s).card ≤ (m - 1) / 2 := by
    intro s hjs hsk
    have h := (Nat.findGreatest_eq_iff (P := fun s => (one_layered_recurrence_union F 0 s).card ≤ (m - 1) / 2)
      (k := F.k) (m := j)).mp rfl
    exact h.2.2 hjs hsk
  have hex : ∃ i, j ≤ i ∧ (one_layered_recurrence_union F i F.k).card ≤ m / 2 :=
    ⟨F.k, hjle, by rw [one_layered_recurrence_union_self]; simp⟩
  let j' := Nat.find hex
  have hj'spec : j ≤ j' ∧ (one_layered_recurrence_union F j' F.k).card ≤ m / 2 := Nat.find_spec hex
  have hj'le : j' ≤ F.k :=
    Nat.find_min' hex (m := F.k) ⟨hjle, by rw [one_layered_recurrence_union_self]; simp⟩
  have hj'min : ∀ s, j ≤ s → s < j' → ¬ (one_layered_recurrence_union F s F.k).card ≤ m / 2 := by
    intro s hjs hsj'
    have h := Nat.find_min hex hsj'
    intro hc
    exact h ⟨hjs, hc⟩
  have hA : j ≤ one_layered_max_layers ((m - 1) / 2) r := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0]; exact Nat.zero_le _
    · set blk := one_layered_recurrence_block F 0 j (by omega) (by omega) with hblk
      have hsub : ∀ t, ∀ G ∈ blk.layers t, G ⊆ one_layered_recurrence_union F 0 j :=
        one_layered_recurrence_block_union_subset (F := F) (lo := 0) (hi := j) (by omega) (by omega)
      set restr := one_layered_recurrence_restrict blk (one_layered_recurrence_union F 0 j) hsub with hrestr
      have hcardV : Fintype.card ↥(one_layered_recurrence_union F 0 j) ≤ (m - 1) / 2 := by
        rw [Fintype.card_coe]; exact hjcard
      have hres := one_layered_recurrence_le_of_family restr hcardV
      have hk1 : restr.k = blk.k := rfl
      have hk2 : blk.k = j := by
        rw [hblk]
        simp [one_layered_recurrence_block]
      rw [hk1.trans hk2] at hres
      exact hres
  have hC : F.k - j' ≤ one_layered_max_layers (m / 2) r := by
    rcases Nat.eq_zero_or_pos (F.k - j') with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hlt : j' < F.k := by omega
      set blk := one_layered_recurrence_block F j' F.k (by omega) (le_refl F.k) with hblk
      have hsub : ∀ t, ∀ G ∈ blk.layers t, G ⊆ one_layered_recurrence_union F j' F.k :=
        one_layered_recurrence_block_union_subset (F := F) (lo := j') (hi := F.k) (by omega) (le_refl F.k)
      set restr := one_layered_recurrence_restrict blk (one_layered_recurrence_union F j' F.k) hsub with hrestr
      have hcardV : Fintype.card ↥(one_layered_recurrence_union F j' F.k) ≤ m / 2 := by
        rw [Fintype.card_coe]; exact hj'spec.2
      have hres := one_layered_recurrence_le_of_family restr hcardV
      have hk1 : restr.k = blk.k := rfl
      have hk2 : blk.k = F.k - j' := by
        rw [hblk]
        simp [one_layered_recurrence_block]
      rw [hk1.trans hk2] at hres
      exact hres
  have hB : j' - j ≤ one_layered_max_layers (m - 1) (r - 1) := by
    rcases Nat.eq_zero_or_pos (j' - j) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hlt : j < j' := by omega
      have hPcard : (m - 1) / 2 + 1 ≤ (one_layered_recurrence_union F 0 (j + 1)).card := by
        have := hjmax (j + 1) (by omega) (by omega)
        omega
      have hQcard : m / 2 + 1 ≤ (one_layered_recurrence_union F (j' - 1) F.k).card := by
        have := hj'min (j' - 1) (by omega) (by omega)
        omega
      have hinter : (one_layered_recurrence_union F 0 (j + 1) ∩
          one_layered_recurrence_union F (j' - 1) F.k).Nonempty := by
        rw [← Finset.card_pos]
        have hun : (one_layered_recurrence_union F 0 (j + 1) ∪
            one_layered_recurrence_union F (j' - 1) F.k).card ≤ n := by
          have h := Finset.card_le_univ (one_layered_recurrence_union F 0 (j + 1) ∪
            one_layered_recurrence_union F (j' - 1) F.k)
          rwa [Fintype.card_fin] at h
        have hci := Finset.card_union_add_card_inter (one_layered_recurrence_union F 0 (j + 1))
          (one_layered_recurrence_union F (j' - 1) F.k)
        omega
      obtain ⟨v0, hv0⟩ := hinter
      rw [Finset.mem_inter] at hv0
      obtain ⟨t₁, ht₁lo, ht₁hi, ht₁k, G₁, hG₁, hv₁⟩ := one_layered_recurrence_union_mem.mp hv0.1
      obtain ⟨t₂, ht₂lo, ht₂hi, ht₂k, G₂, hG₂, hv₂⟩ := one_layered_recurrence_union_mem.mp hv0.2
      have hts : {t : Fin F.k | ∃ G ∈ F.layers t, ({v0} : Finset (Fin n)) ⊆ G}.OrdConnected :=
        F.interval_property {v0} (Finset.singleton_nonempty v0)
      have hmem₁ : (⟨t₁, ht₁k⟩ : Fin F.k) ∈ {t : Fin F.k | ∃ G ∈ F.layers t, ({v0} : Finset (Fin n)) ⊆ G} :=
        ⟨G₁, hG₁, by rw [Finset.singleton_subset_iff]; exact hv₁⟩
      have hmem₂ : (⟨t₂, ht₂k⟩ : Fin F.k) ∈ {t : Fin F.k | ∃ G ∈ F.layers t, ({v0} : Finset (Fin n)) ⊆ G} :=
        ⟨G₂, hG₂, by rw [Finset.singleton_subset_iff]; exact hv₂⟩
      set blk := one_layered_recurrence_block F j j' (by omega) (by omega) with hblk
      have hvblock : ∀ t : Fin (j' - j), ∃ G ∈ blk.layers t, v0 ∈ G := by
        intro t
        have ht : t.val < j' - j := t.isLt
        have hu : j + t.val < F.k := by omega
        have hub : (⟨j + t.val, hu⟩ : Fin F.k) ∈
            Set.Icc (⟨t₁, ht₁k⟩ : Fin F.k) ⟨t₂, ht₂k⟩ := by
          refine Set.mem_Icc.mpr ⟨Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr (by omega)⟩
        have hmem := hts.out' hmem₁ hmem₂ hub
        obtain ⟨G, hG, hGv⟩ := hmem
        have hlayers : blk.layers t = F.layers ⟨j + t.val, hu⟩ := rfl
        exact ⟨G, hlayers ▸ hG, Finset.singleton_subset_iff.mp hGv⟩
      set link := one_layered_recurrence_link blk v0 hvblock with hlink
      set W := Finset.univ.erase v0 with hWdef
      have hW : ∀ t, ∀ G ∈ link.layers t, G ⊆ W := by
        intro t G hG x hx
        obtain ⟨F₀, hF₀, hvF₀, rfl⟩ := one_layered_recurrence_linkLayer_mem.mp hG
        rw [hWdef, Finset.mem_erase]
        exact ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
      set restr := one_layered_recurrence_restrict link W hW with hrestr
      have hcardV : Fintype.card ↥W ≤ m - 1 := by
        rw [Fintype.card_coe, hWdef, Finset.card_erase_of_mem (Finset.mem_univ v0),
          Finset.card_univ, Fintype.card_fin]
        omega
      have hres := one_layered_recurrence_le_of_family restr hcardV
      have hk1 : restr.k = link.k := rfl
      have hk2 : link.k = blk.k := rfl
      have hk3 : blk.k = j' - j := by
        rw [hblk]
        simp [one_layered_recurrence_block]
      rw [hk1.trans (hk2.trans hk3)] at hres
      exact hres
  have hsum : F.k = j + (j' - j) + (F.k - j') := by omega
  omega

/-- Recurrence for the maximum number of layers F(m, r) ≤ F(⌊(m-1)/2⌋, r) + F(⌈(m-1)/2⌉, r) + F(m-1, r-1). -/
theorem one_layered_recurrence (m r : ℕ) (hr : 2 ≤ r) (hm : r ≤ m) :
    one_layered_max_layers m r ≤
      one_layered_max_layers ((m - 1) / 2) r +
      one_layered_max_layers (m / 2) r +
      one_layered_max_layers (m - 1) (r - 1) := by
  rw [one_layered_recurrence_eq_sSup]
  refine csSup_le (one_layered_recurrence_set_nonempty hm) ?_
  rintro k ⟨n, hn, F, rfl⟩
  exact one_layered_recurrence_aux hr hn F
