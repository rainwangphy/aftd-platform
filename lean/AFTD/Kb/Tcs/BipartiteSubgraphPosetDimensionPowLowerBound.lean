import AFTD.Prelude
import AFTD.Kb.Tcs.BipartitePosetLe
import AFTD.Kb.Tcs.PosetDimension
import AFTD.Kb.Tcs.BipartitePosetIsPartialOrder
import AFTD.Kb.Tcs.IsPosetRealizer
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# bipartite_subgraph_poset_dimension_pow_lower_bound

Topic: combinatorics   Node: 7d7dcb33c9f8

Provenance: helper lemma. arXiv:2610.24774, Section 4.1, Lemma 4.2

Let V be a finite type with decidable equality, G a simple graph on V with decidable adjacency, and A, B subsets of V covering V such that G is bipartite with parts A and B. Let N = Fintype.card V and M = G.edgeFinset.card, with 2 ≤ N. Then there exists a spanning subgraph H ≤ G such that 2 ^ M ≤ (N.factorial) ^ (poset_dimension (bipartite_poset_le H A B)).
-/

open Finset

/-- A linear order gives a permutation of the finite type to `Fin n`, canonically. -/
noncomputable def bspd_pLo {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
    (n : ℕ) (hn : Fintype.card W = n) : W ≃ Fin n :=
  let e : Fin n ≃o (↑(Finset.univ : Finset W)) :=
    (Finset.univ : Finset W).orderIsoOfFin (by simpa using hn)
  let f : Fin n → W := fun i => (e i : W)
  have hinj : Function.Injective f := fun a b hab => e.injective (Subtype.ext hab)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := e.surjective ⟨x, Finset.mem_univ x⟩
    exact ⟨i, by simpa [f] using congrArg Subtype.val hi⟩
  (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm

/-- `bspd_pLo` preserves and reflects the linear order. -/
theorem bspd_pLo_spec {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
    (n : ℕ) (hn : Fintype.card W = n) (x y : W) :
    x ≤ y ↔ (bspd_pLo n hn x) ≤ (bspd_pLo n hn y) := by
  let e : Fin n ≃o (↑(Finset.univ : Finset W)) :=
    (Finset.univ : Finset W).orderIsoOfFin (by simpa using hn)
  let f : Fin n → W := fun i => (e i : W)
  have hinj : Function.Injective f := fun a b hab => e.injective (Subtype.ext hab)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := e.surjective ⟨x, Finset.mem_univ x⟩
    exact ⟨i, by simpa [f] using congrArg Subtype.val hi⟩
  have key : ∀ a b : Fin n, f a ≤ f b ↔ a ≤ b := fun a b => e.le_iff_le
  have happ : ∀ z : W, f (bspd_pLo n hn z) = z :=
    fun z => Equiv.apply_symm_apply (Equiv.ofBijective f ⟨hinj, hsurj⟩) z
  rw [← key, happ, happ]

/-- Szpilrajn: a partial order relation extends to a linear order relation. -/
theorem bspd_hexists_linearRel_ext {α : Type*} {r : α → α → Prop} (h : IsPartialOrder α r) :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ ∀ a b, r a b → s a b := by
  letI := h
  obtain ⟨s, hsl, hrs⟩ := extend_partialOrder r
  exact ⟨s, hsl, fun a b hab => hrs a b hab⟩

/-- For a non-related pair in a partial order, some extending linear order also does not
relate that pair. -/
theorem bspd_hexists_linearRel_sep {α : Type*} {r : α → α → Prop} (h : IsPartialOrder α r)
    {x y : α} (hxy : ¬ r x y) :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ (∀ a b, r a b → s a b) ∧ ¬ s x y := by
  classical
  set r' : α → α → Prop := fun a b => r a b ∨ (r a y ∧ r x b) with hr'
  have hr'po : IsPartialOrder α r' :=
    { refl := fun a => Or.inl (h.refl a)
      trans := by
        intro a b c hab hbc
        rcases hab with hab | ⟨hay, hxb⟩
        · rcases hbc with hbc | ⟨hby, hxc⟩
          · exact Or.inl (_root_.trans hab hbc)
          · exact Or.inr ⟨_root_.trans hab hby, hxc⟩
        · rcases hbc with hbc | ⟨hby, hxc⟩
          · exact Or.inr ⟨hay, _root_.trans hxb hbc⟩
          · exact Or.inr ⟨hay, hxc⟩
      antisymm := by
        intro a b hab hba
        rcases hab with hab | ⟨hay, hxb⟩
        · rcases hba with hba | ⟨hby, hxa⟩
          · exact h.antisymm a b hab hba
          · exact absurd (_root_.trans (_root_.trans hxa hab) hby) hxy
        · rcases hba with hba | ⟨hby, hxa⟩
          · exact absurd (_root_.trans hxb (_root_.trans hba hay)) hxy
          · exact absurd (_root_.trans hxb hby) hxy }
  obtain ⟨s, hslin, hrs⟩ := bspd_hexists_linearRel_ext hr'po
  refine ⟨s, hslin, ?_, ?_⟩
  · intro a b hab
    exact hrs a b (Or.inl hab)
  · intro hsxy
    have hyx : r' y x := Or.inr ⟨h.refl y, h.refl x⟩
    have : s y x := hrs y x hyx
    have hEq : x = y := hslin.antisymm x y hsxy this
    exact hxy (hEq ▸ h.refl x)

/-- A linear order relation on a finite type is induced by a permutation to `Fin n`. -/
theorem bspd_hexists_perm_of_isLinearOrder {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : Fintype.card α = n) (s : α → α → Prop) (hs : IsLinearOrder α s) :
    ∃ p : α ≃ Fin n, ∀ x y, s x y ↔ (p x : Fin n) ≤ p y := by
  classical
  set rank : α → ℕ := fun x => (Finset.univ.filter (fun y => s y x)).card with hrank
  have hrank_spec : ∀ x y, s x y ↔ rank x ≤ rank y := by
    intro x y
    constructor
    · intro hxy
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hs.trans z x y hz hxy
    · intro hle
      by_contra hxy
      have hyx : s y x := (hs.total y x).resolve_right hxy
      have hsub : (Finset.univ.filter (fun z => s z y)) ⊆ (Finset.univ.filter (fun z => s z x)) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hs.trans z y x hz hyx
      have hxmem : x ∈ Finset.univ.filter (fun z => s z x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hs.refl x
      have hxnot : x ∉ Finset.univ.filter (fun z => s z y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hxy
      have hlt : (Finset.univ.filter (fun z => s z y)).card <
          (Finset.univ.filter (fun z => s z x)).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩)
        intro heq
        exact hxnot (heq ▸ hxmem)
      have hle' : (Finset.univ.filter (fun z => s z x)).card ≤
          (Finset.univ.filter (fun z => s z y)).card := hle
      omega
  have hinj : Function.Injective rank := by
    intro x y hxy
    have h1 : s x y := (hrank_spec x y).mpr (le_of_eq hxy)
    have h2 : s y x := (hrank_spec y x).mpr (le_of_eq hxy.symm)
    exact hs.antisymm x y h1 h2
  let L : LinearOrder α := LinearOrder.lift' rank hinj
  refine ⟨@bspd_pLo α _ _ L n hn, ?_⟩
  intro x y
  exact (hrank_spec x y).trans (@bspd_pLo_spec α _ _ L n hn x y)

/-- Every partial order on a finite type has a finite family of linear orders realizing it,
exhibited as a family of permutations of `Fin n`. -/
theorem bspd_hexists_perm_realizer_of_isPartialOrder {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : Fintype.card α = n) {r : α → α → Prop} (h : IsPartialOrder α r) :
    ∃ d : ℕ, ∃ p : Fin d → (α ≃ Fin n), ∀ x y, r x y ↔ ∀ i, (p i x : Fin n) ≤ p i y := by
  classical
  let ι := {w : α × α // ¬ r w.1 w.2}
  have hkey : ∀ w : ι, ∃ p : α ≃ Fin n,
      (∀ a b, r a b → (p a : Fin n) ≤ p b) ∧ ¬ (p w.1.1 : Fin n) ≤ p w.1.2 := by
    intro w
    obtain ⟨s, hslin, hrs, hns⟩ := bspd_hexists_linearRel_sep h w.2
    obtain ⟨p, hp⟩ := bspd_hexists_perm_of_isLinearOrder n hn s hslin
    exact ⟨p, fun a b hab => (hp a b).mp (hrs a b hab), fun hc => hns ((hp _ _).mpr hc)⟩
  choose P hP₁ hP₂ using hkey
  refine ⟨Fintype.card ι, fun i => P ((Fintype.equivFin ι).symm i), ?_⟩
  intro x y
  constructor
  · intro hxy i
    exact hP₁ _ x y hxy
  · intro hall
    by_contra hxy
    have h := hall (Fintype.equivFin ι ⟨(x, y), hxy⟩)
    simp only [Equiv.symm_apply_apply] at h
    exact hP₂ ⟨(x, y), hxy⟩ h

/-- The poset dimension is attained by an actual family of linear orders. -/
theorem bspd_hexists_realizer_of_poset_dimension {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : Fintype.card α = n) {r : α → α → Prop} (h : IsPartialOrder α r) :
    ∃ R : Fin (poset_dimension r) → LinearOrder α, is_poset_realizer r R := by
  have hne : {d : ℕ | ∃ R : Fin d → LinearOrder α, is_poset_realizer r R}.Nonempty := by
    obtain ⟨d, p, hp⟩ := bspd_hexists_perm_realizer_of_isPartialOrder n hn h
    exact ⟨d, fun i => LinearOrder.lift' (fun x => (p i x : Fin n)) (p i).injective,
      fun x y => by rw [hp x y]; rfl⟩
  exact Nat.sInf_mem hne

/-- A permutation family of length exactly the poset dimension realizing a partial order. -/
theorem bspd_hexists_perm_realizer_of_poset_dimension {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : Fintype.card α = n) {r : α → α → Prop} (h : IsPartialOrder α r) :
    ∃ q : Fin (poset_dimension r) → (α ≃ Fin n),
      ∀ x y, r x y ↔ ∀ i, (q i x : Fin n) ≤ q i y := by
  obtain ⟨R, hR⟩ := bspd_hexists_realizer_of_poset_dimension n hn h
  refine ⟨fun i => @bspd_pLo α _ _ (R i) n hn, ?_⟩
  intro x y
  rw [hR x y]
  constructor
  · intro h i; exact (@bspd_pLo_spec α _ _ (R i) n hn x y).mp (h i)
  · intro h i; exact (@bspd_pLo_spec α _ _ (R i) n hn x y).mpr (h i)

/-- Pad a permutation family realizing a relation to any length `D ≥ d`, repeating members. -/
theorem bspd_hexists_perm_pad {α : Type*} [Fintype α] [DecidableEq α] {n d : ℕ}
    (q : Fin d → (α ≃ Fin n)) (hd : 1 ≤ d) {D : ℕ} (hdD : d ≤ D) :
    ∃ Q : Fin D → (α ≃ Fin n),
      ∀ x y, (∀ i, (q i x : Fin n) ≤ q i y) ↔ ∀ i, (Q i x : Fin n) ≤ Q i y := by
  have hmin : ∀ i : Fin D, min (i : ℕ) (d - 1) < d := by
    intro i
    have h1 := Nat.min_le_right (i : ℕ) (d - 1)
    omega
  refine ⟨fun i => q ⟨min (i : ℕ) (d - 1), hmin i⟩, ?_⟩
  intro x y
  constructor
  · intro h i
    exact h ⟨min (i : ℕ) (d - 1), hmin i⟩
  · intro h j
    have hjD : (j : ℕ) < D := by have := j.2; omega
    have h2 := h ⟨(j : ℕ), hjD⟩
    have he : (⟨min ((⟨(j : ℕ), hjD⟩ : Fin D) : ℕ) (d - 1), hmin ⟨(j : ℕ), hjD⟩⟩ : Fin d) = j :=
      Fin.ext (by show min (j : ℕ) (d - 1) = (j : ℕ); omega)
    simpa [he] using h2

/-- The bipartite height-2 relation of a graph is not universal when there are two vertices. -/
theorem bspd_hexists_not_le {W : Type*} [Fintype W] (H : SimpleGraph W) (A B : Set W)
    (hdisj : Disjoint A B) (hcard : 2 ≤ Fintype.card W) :
    ∃ x y : W, ¬ bipartite_poset_le H A B x y := by
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
  by_cases hB : B = ∅
  · refine ⟨u, v, ?_⟩
    simp only [bipartite_poset_le, not_or]
    exact ⟨huv, fun h => by simpa [hB] using h.2.1⟩
  · obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hB
    obtain ⟨y, hyb⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card W) b
    refine ⟨b, y, ?_⟩
    simp only [bipartite_poset_le, not_or]
    exact ⟨hyb.symm, fun h => (Set.disjoint_left.mp hdisj) h.1 hb⟩

/-- The number of spanning subgraphs of a finite graph is `2 ^ #edges`. -/
theorem bspd_hcard_subgraph_le {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] [DecidablePred (fun H : SimpleGraph W => H ≤ G)] :
    Fintype.card {H : SimpleGraph W // H ≤ G} = 2 ^ G.edgeFinset.card := by
  classical
  have e : {H : SimpleGraph W // H ≤ G} ≃ Set G.edgeSet :=
  { toFun := fun H => {x | (x : Sym2 W) ∈ H.1.edgeSet}
    invFun := fun S => ⟨SimpleGraph.fromEdgeSet ((↑) '' S), by
      rw [← SimpleGraph.edgeSet_subset_edgeSet]
      intro z hz
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hz
      obtain ⟨⟨y, hy, hyz⟩, -⟩ := hz
      rw [← hyz]
      exact y.2⟩
    left_inv := by
      intro H
      apply Subtype.ext
      have hS : (↑) '' {x : G.edgeSet | (x : Sym2 W) ∈ H.1.edgeSet} = H.1.edgeSet := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hz
          exact ⟨⟨z, SimpleGraph.edgeSet_mono H.2 hz⟩, hz, rfl⟩
      show SimpleGraph.fromEdgeSet ((↑) '' {x : G.edgeSet | (x : Sym2 W) ∈ H.1.edgeSet}) = H.1
      rw [hS, SimpleGraph.fromEdgeSet_edgeSet]
    right_inv := by
      intro S
      ext x
      show (x : Sym2 W) ∈ (SimpleGraph.fromEdgeSet ((↑) '' S)).edgeSet ↔ x ∈ S
      rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff]
      constructor
      · rintro ⟨h1, -⟩
        obtain ⟨y, hy, hyx⟩ := h1
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      · intro hx
        exact ⟨⟨x, hx, rfl⟩, SimpleGraph.not_isDiag_of_mem_edgeSet G x.2⟩ }
  rw [Fintype.card_congr e, Fintype.card_set]
  congr 1
  show Fintype.card ↑G.edgeSet = G.edgeSet.toFinset.card
  exact (Set.toFinset_card (G.edgeSet)).symm

/-- A subgraph of a bipartite graph is determined by the height-2 relation it induces. -/
theorem bspd_heq_of_bipartite_poset_le_iff {W : Type*} {G H H' : SimpleGraph W} {A B : Set W}
    (hbip : G.IsBipartiteWith A B) (hH : H ≤ G) (hH' : H' ≤ G)
    (h : ∀ x y, bipartite_poset_le H A B x y ↔ bipartite_poset_le H' A B x y) : H = H' := by
  have key : ∀ (K K' : SimpleGraph W), K ≤ G →
      (∀ x y, bipartite_poset_le K A B x y → bipartite_poset_le K' A B x y) →
      ∀ x y, K.Adj x y → K'.Adj x y := by
    intro K K' hK hkk x y hxy
    have hne : x ≠ y := by rintro rfl; exact K.irrefl hxy
    rcases hbip.mem_of_adj (hK hxy) with ⟨hxA, hyB⟩ | ⟨hxB, hyA⟩
    · rcases hkk x y (Or.inr ⟨hxA, hyB, hxy⟩) with hEq | ⟨-, -, hadj'⟩
      · exact absurd hEq hne
      · exact hadj'
    · rcases hkk y x (Or.inr ⟨hyA, hxB, hxy.symm⟩) with hEq | ⟨-, -, hadj'⟩
      · exact absurd hEq.symm hne
      · exact hadj'.symm
  refine SimpleGraph.ext (funext fun x => funext fun y => propext ⟨?_, ?_⟩)
  · exact key H H' hH (fun x y hxy => (h x y).mp hxy) x y
  · exact key H' H hH' (fun x y hxy => (h x y).mpr hxy) x y

/-- Lower bound on the maximum dimension of a subgraph poset in power form 2^M ≤ (N!)^d. -/
theorem bipartite_subgraph_poset_dimension_pow_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Set V) (h_cov : A ∪ B = Set.univ) (h_bip : G.IsBipartiteWith A B)
    (N M : ℕ) (hN : Fintype.card V = N) (hM : G.edgeFinset.card = M)
    (hN2 : 2 ≤ N) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      2 ^ M ≤ (N.factorial) ^ (poset_dimension (bipartite_poset_le H A B)) := by
  classical
  have hcardV : 2 ≤ Fintype.card V := by omega
  set r : {H : SimpleGraph V // H ≤ G} → V → V → Prop :=
    fun H => bipartite_poset_le H.1 A B with hr
  have hpo : ∀ H, IsPartialOrder V (r H) :=
    fun H => bipartite_poset_is_partial_order H.1 A B h_bip.disjoint
  set D : ℕ := Finset.univ.sup (fun H : {H : SimpleGraph V // H ≤ G} => poset_dimension (r H)) with hD
  have hleD : ∀ H : {H : SimpleGraph V // H ≤ G}, poset_dimension (r H) ≤ D := by
    intro H
    rw [hD]
    exact Finset.le_sup (f := fun H : {H : SimpleGraph V // H ≤ G} => poset_dimension (r H))
      (Finset.mem_univ H)
  have hge1 : ∀ H : {H : SimpleGraph V // H ≤ G}, 1 ≤ poset_dimension (r H) := by
    intro H
    by_contra hcon
    have h0 : poset_dimension (r H) = 0 := by omega
    obtain ⟨R, hR⟩ := bspd_hexists_realizer_of_poset_dimension N hN (hpo H)
    obtain ⟨x, y, hxy⟩ := bspd_hexists_not_le H.1 A B h_bip.disjoint hcardV
    exact hxy ((hR x y).mpr (fun i => (Fin.cast h0 i).elim0))
  have hex : ∀ H : {H : SimpleGraph V // H ≤ G}, ∃ q : Fin D → (V ≃ Fin N),
      ∀ x y, r H x y ↔ ∀ i, (q i x : Fin N) ≤ q i y := by
    intro H
    obtain ⟨q, hq⟩ := bspd_hexists_perm_realizer_of_poset_dimension N hN (hpo H)
    obtain ⟨Q, hQ⟩ := bspd_hexists_perm_pad q (hge1 H) (hleD H)
    exact ⟨Q, fun x y => (hq x y).trans (hQ x y)⟩
  set pad : {H : SimpleGraph V // H ≤ G} → (Fin D → (V ≃ Fin N)) := fun H => (hex H).choose
    with hpaddef
  have hpad : ∀ H, ∀ x y, r H x y ↔ ∀ i, (pad H i x : Fin N) ≤ pad H i y :=
    fun H => (hex H).choose_spec
  have hpadinj : Function.Injective pad := by
    intro H H' hEq
    have hrr : ∀ x y, r H x y ↔ r H' x y := by
      intro x y
      have h1 := hpad H x y
      have h2 := hpad H' x y
      rw [hEq] at h1
      exact h1.trans h2.symm
    apply Subtype.ext
    exact bspd_heq_of_bipartite_poset_le_iff h_bip H.2 H'.2 hrr
  have hbound : Fintype.card {H : SimpleGraph V // H ≤ G} ≤
      Fintype.card (Fin D → (V ≃ Fin N)) :=
    Fintype.card_le_of_injective pad hpadinj
  have hcardperm : Fintype.card (Fin D → (V ≃ Fin N)) = N.factorial ^ D := by
    rw [Fintype.card_fun, Fintype.card_fin]
    obtain ⟨e⟩ : Nonempty (V ≃ Fin N) := ⟨(Fintype.equivFin V).trans (finCongr hN)⟩
    rw [Fintype.card_equiv e, hN]
  have hMeq : 2 ^ M = Fintype.card {H : SimpleGraph V // H ≤ G} := by
    rw [bspd_hcard_subgraph_le G, hM]
  obtain ⟨H₀, -, hH₀⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset {H : SimpleGraph V // H ≤ G})
      ⟨⟨⊥, bot_le⟩, Finset.mem_univ _⟩ (fun H : {H : SimpleGraph V // H ≤ G} => poset_dimension (r H))
  have hDval : D = poset_dimension (r H₀) := by rw [hD]; exact hH₀
  refine ⟨H₀.1, H₀.2, ?_⟩
  calc 2 ^ M = Fintype.card {H : SimpleGraph V // H ≤ G} := hMeq
    _ ≤ Fintype.card (Fin D → (V ≃ Fin N)) := hbound
    _ = N.factorial ^ D := hcardperm
    _ = N.factorial ^ (poset_dimension (r H₀)) := by rw [hDval]
