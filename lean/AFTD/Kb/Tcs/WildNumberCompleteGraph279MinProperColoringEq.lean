import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.WildPartitionEventMass279Certificate
import AFTD.Kb.Tcs.FiniteProductOneSubLowerBoundByFibres
import AFTD.Kb.Tcs.CanonicalPermutationAvoidanceOfLocalLemma
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.OddCompleteMinEdgeColoringMissingVertexEquiv
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.WildPartitionVertexMass279Certificate
import AFTD.Kb.Tcs.WildPartitionPositionMass279Certificate
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.G

/-!
# wild_number_complete_graph_279_min_proper_coloring_eq

Topic: graphs   Node: 57b881c3de0c

Provenance: original. Related work: Partial case of arXiv:2610.22142, Section 6 conjecture. The paper proves equality only for 3<=n<=12. Proposed here using canonical permutation seal events and the exact rational certificate at n=279; no wild-number bound at 279 is claimed proved.

Proposed new case of OP-306: every minimum proper edge colouring of K_279 has wild number 186. The proposed permutation-event proof and its translation to the graph statement remain unproved; the numerical condition alone does not prove this case.
-/

theorem w279_colorable (n : ℕ) (hn : 3 ≤ n) : (⊤ : SimpleGraph (Fin n)).lineGraph.Colorable n := by
  let col : Sym2 (Fin n) → Fin n := Sym2.lift ⟨fun a b => (⟨(a.val + b.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n),
    fun a b => by simp [Nat.add_comm]⟩
  refine ⟨SimpleGraph.Coloring.mk (fun e => col e.val) ?_⟩
  intro e₁ e₂ h
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  obtain ⟨hne, v, h1, h2⟩ := h
  obtain ⟨a, ha⟩ : ∃ a, (e₁ : Sym2 (Fin n)) = s(v, a) := (Sym2.mem_iff_exists.mp h1).imp fun a h => h
  obtain ⟨b, hb⟩ : ∃ b, (e₂ : Sym2 (Fin n)) = s(v, b) := (Sym2.mem_iff_exists.mp h2).imp fun a h => h
  intro hc
  apply hne
  apply Subtype.ext
  rw [ha, hb]
  simp only [col, ha, hb, Sym2.lift_mk, Fin.mk.injEq] at hc
  have h3 := Nat.ModEq.add_left_cancel' v.val hc
  have : a.val = b.val := Nat.ModEq.eq_of_lt_of_lt h3 a.isLt b.isLt
  rw [Fin.ext this]

theorem w279_color_card_at {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (v : Fin n) (i0 : Fin k) :
    ((Finset.univ.erase v).image
      (fun x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0)).card = n - 1 := by
  rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  intro a ha b hb hab
  have ha' := Ne.symm (Finset.ne_of_mem_erase ha)
  have hb' := Ne.symm (Finset.ne_of_mem_erase hb)
  simp only [dif_pos ha', dif_pos hb'] at hab
  exact wild_kn_same_color c ha' hb' hab

/-- No colour class is a perfect matching of an odd complete graph. -/
theorem w279_color_missed_of_odd {n k : ℕ} (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (i0 : Fin k) :
    ∃ v : Fin n, ∀ x (hx : v ≠ x), c ⟨s(v, x), wild_kn_mem hx⟩ ≠ i0 := by
  classical
  by_contra hno
  simp only [not_exists, not_forall, not_not] at hno
  choose partner hpne hpi using hno
  have hpp : ∀ v, partner (partner v) = v := by
    intro v
    have h1 := hpi (partner v)
    have h2 := hpi v
    have h2' : c ⟨s(partner v, v), wild_kn_mem (Ne.symm (hpne v))⟩ = i0 := by
      rw [← h2]; congr 2; exact Sym2.eq_swap
    exact wild_kn_same_color c (hpne (partner v)) (Ne.symm (hpne v)) (h1.trans h2'.symm)
  let e : Fin n → Sym2 (Fin n) := fun v => s(v, partner v)
  have hfib : ∀ v, (Finset.univ.filter fun w => e w = e v) = {v, partner v} := by
    intro v
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, e, Sym2.eq_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, hpp v⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (f := e) (s := Finset.univ)
    (t := Finset.univ.image e) (fun x _ => Finset.mem_image_of_mem e (Finset.mem_univ x))
  have h2 : ∀ b ∈ Finset.univ.image e, (Finset.univ.filter fun a => e a = b).card = 2 := by
    intro b hb
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hfib v, Finset.card_pair (hpne v)]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hsum
  omega

theorem w279_missing_vertex_equiv (n k : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k) (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) : ∃ m : Fin k ≃ Fin n, ∀ (i : Fin k) (v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), by simpa using hvw⟩ ≠ i) ↔ v = m i := by
  classical
  have hkn : k ≤ n := by
    have := (w279_colorable n hn).chromaticNumber_le
    rw [hk] at this
    exact_mod_cast this
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let i0 := c ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), wild_kn_mem h01⟩
  let col : Fin n → Fin n → Fin k := fun v x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0
  have hcol : ∀ v x (h : v ≠ x), col v x = c ⟨s(v, x), wild_kn_mem h⟩ := fun v x h => dif_pos h
  let Cv : Fin n → Finset (Fin k) := fun v => (Finset.univ.erase v).image (col v)
  have hCv : ∀ v, (Cv v).card = n - 1 := fun v => w279_color_card_at c v i0
  -- a missed colour at each vertex
  have hmiss : ∀ v, ∃ i, i ∉ Cv v := by
    intro v
    obtain ⟨e, he⟩ := wild_kn_exists_missing_color_of_odd hn hodd c v
    refine ⟨c e, fun h => ?_⟩
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 h
    have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
    rw [hcol v x hx'] at hxc
    exact he x hx' hxc
  have hkn' : n ≤ k := by
    obtain ⟨i, hi⟩ := hmiss ⟨0, by omega⟩
    have : Cv ⟨0, by omega⟩ ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.2
      ⟨Finset.subset_univ _, fun h => hi (h ▸ Finset.mem_univ i)⟩
    have := Finset.card_lt_card this
    rw [hCv, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hk' : k = n := le_antisymm hkn hkn'
  subst hk'
  -- exactly one missed colour at each vertex
  have huniq : ∀ v i j, i ∉ Cv v → j ∉ Cv v → i = j := by
    intro v i j hi hj
    by_contra hij
    have hsub : Cv v ⊆ (Finset.univ.erase i).erase j := by
      intro x hx
      refine Finset.mem_erase.2 ⟨fun h => hj (h ▸ hx), Finset.mem_erase.2 ⟨fun h => hi (h ▸ hx), Finset.mem_univ _⟩⟩
    have := Finset.card_le_card hsub
    rw [hCv, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  choose miss hmissv using hmiss
  have hmissing : ∀ (i : Fin k) (v : Fin k), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ i ∉ Cv v := by
    intro i v
    constructor
    · intro h hi
      obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 hi
      have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
      rw [hcol v x hx'] at hxc
      exact h x hx' hxc
    · intro h w hvw hc
      exact h (Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨Ne.symm hvw, Finset.mem_univ _⟩,
        by rw [hcol v w hvw, hc]⟩)
  have hsurj : Function.Surjective miss := by
    intro i
    obtain ⟨v, hv⟩ := w279_color_missed_of_odd hodd c i
    exact ⟨v, huniq v _ _ (hmissv v) ((hmissing i v).1 hv)⟩
  have hbij : Function.Bijective miss := (Finite.injective_iff_surjective.2 hsurj) |> fun h => ⟨h, hsurj⟩
  let E := Equiv.ofBijective miss hbij
  refine ⟨E.symm, fun i v => ?_⟩
  rw [hmissing i v, Equiv.eq_symm_apply]
  constructor
  · intro h
    exact huniq v _ _ (hmissv v) h
  · intro h
    rw [← h]
    exact hmissv v

/-- `U` is closed under the edges of colour `i`. -/
def w279_closed {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (i : Fin k)
    (U : Finset (Fin n)) : Prop :=
  ∀ u ∈ U, ∀ w (h : u ≠ w), c ⟨s(u, w), wild_kn_mem h⟩ = i → w ∈ U

/-- The partner of `v` in colour `i` (or `v` itself if there is none). -/
noncomputable def w279_pc {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (i : Fin k)
    (v : Fin n) : Fin n :=
  open Classical in
  if h : ∃ w, ∃ h : v ≠ w, c ⟨s(v, w), wild_kn_mem h⟩ = i then h.choose else v

theorem w279_c_swap {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) {u v : Fin n}
    (h : u ≠ v) : c ⟨s(u, v), wild_kn_mem h⟩ = c ⟨s(v, u), wild_kn_mem (Ne.symm h)⟩ := by
  have : (⟨s(u, v), wild_kn_mem h⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) = ⟨s(v, u), wild_kn_mem (Ne.symm h)⟩ :=
    Subtype.ext Sym2.eq_swap
  rw [this]

theorem w279_closed_univ {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (i : Fin k) :
    w279_closed c i Finset.univ :=
  fun _ _ w _ _ => Finset.mem_univ w

section
variable {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (m : Fin k → Fin n)
  (hm : ∀ (i : Fin k) (v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
include hm

theorem w279_pc_spec (i : Fin k) (v : Fin n) (hv : v ≠ m i) :
    ∃ h : v ≠ w279_pc c i v, c ⟨s(v, w279_pc c i v), wild_kn_mem h⟩ = i := by
  have hex : ∃ w, ∃ h : v ≠ w, c ⟨s(v, w), wild_kn_mem h⟩ = i := by
    by_contra hno
    simp only [not_exists] at hno
    exact hv ((hm i v).1 fun w hvw h => hno w hvw h)
  unfold w279_pc
  rw [dif_pos hex]
  exact hex.choose_spec

theorem w279_pc_unique (i : Fin k) {v w : Fin n} (h : v ≠ w) (hc : c ⟨s(v, w), wild_kn_mem h⟩ = i) :
    w = w279_pc c i v := by
  have hv : v ≠ m i := fun hv => (hm i v).2 hv w h hc
  obtain ⟨h', hc'⟩ := w279_pc_spec c m hm i v hv
  exact wild_kn_same_color c h h' (hc.trans hc'.symm)

theorem w279_pc_ne (i : Fin k) (v : Fin n) (hv : v ≠ m i) : w279_pc c i v ≠ m i := by
  obtain ⟨h', hc'⟩ := w279_pc_spec c m hm i v hv
  intro he
  exact (hm i (w279_pc c i v)).2 he v (Ne.symm h') ((w279_c_swap c (Ne.symm h')).trans hc')

theorem w279_pc_pc (i : Fin k) (v : Fin n) (hv : v ≠ m i) : w279_pc c i (w279_pc c i v) = v := by
  obtain ⟨h', hc'⟩ := w279_pc_spec c m hm i v hv
  exact (w279_pc_unique c m hm i (Ne.symm h') ((w279_c_swap c (Ne.symm h')).trans hc')).symm

theorem w279_closed_iff (i : Fin k) (U : Finset (Fin n)) :
    w279_closed c i U ↔ ∀ u ∈ U, u ≠ m i → w279_pc c i u ∈ U := by
  constructor
  · intro hU u hu hum
    obtain ⟨h', hc'⟩ := w279_pc_spec c m hm i u hum
    exact hU u hu _ h' hc'
  · intro hU u hu w h hc
    have hum : u ≠ m i := fun hv => (hm i u).2 hv w h hc
    rw [w279_pc_unique c m hm i h hc]
    exact hU u hu hum

/-- representatives of the colour-`i` edges -/
noncomputable def w279_R (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun v => v ≠ m i ∧ v < w279_pc c i v

theorem w279_card_closed (i : Fin k) (U : Finset (Fin n)) (hU : w279_closed c i U) :
    U.card = 2 * (U.filter (· ∈ w279_R c m i)).card + (if m i ∈ U then 1 else 0) := by
  classical
  rw [w279_closed_iff c m hm] at hU
  set A := U.filter (· ∈ w279_R c m i)
  let B := U.filter (fun v => v ≠ m i ∧ w279_pc c i v < v)
  let C := U.filter (fun v => v = m i)
  have hAB : B.card = A.card := by
    refine Finset.card_nbij' (w279_pc c i) (w279_pc c i) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [B, Finset.coe_filter, Set.mem_setOf_eq] at hv
      simp only [A, w279_R, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq]
      refine ⟨hU v hv.1 hv.2.1, w279_pc_ne c m hm i v hv.2.1, ?_⟩
      rw [w279_pc_pc c m hm i v hv.2.1]; exact hv.2.2
    · intro v hv
      simp only [A, w279_R, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hv
      simp only [B, Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨hU v hv.1 hv.2.1, w279_pc_ne c m hm i v hv.2.1, ?_⟩
      rw [w279_pc_pc c m hm i v hv.2.1]; exact hv.2.2
    · intro v hv
      simp only [B, Finset.coe_filter, Set.mem_setOf_eq] at hv
      exact w279_pc_pc c m hm i v hv.2.1
    · intro v hv
      simp only [A, w279_R, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hv
      exact w279_pc_pc c m hm i v hv.2.1
  have hC : C.card = if m i ∈ U then 1 else 0 := by
    split_ifs with h
    · rw [Finset.card_eq_one]; refine ⟨m i, ?_⟩
      ext v; simp only [C, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hv'; exact h (hv' ▸ hv)
  have hU' : U = A ∪ B ∪ C := by
    ext v
    simp only [A, B, C, w279_R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      by_cases hvm : v = m i
      · exact Or.inr ⟨hv, hvm⟩
      · obtain ⟨h', -⟩ := w279_pc_spec c m hm i v hvm
        rcases lt_or_gt_of_ne h' with h1 | h1
        · exact Or.inl (Or.inl ⟨hv, hvm, h1⟩)
        · exact Or.inl (Or.inr ⟨hv, hvm, h1⟩)
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1
  have hd1 : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v ha hb
    simp only [A, B, w279_R, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact lt_asymm ha.2.2 hb.2.2
  have hd2 : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro v ha hc
    simp only [A, B, C, w279_R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    rcases ha with h | h
    · exact h.2.1 hc.2
    · exact h.2.1 hc.2
  conv_lhs => rw [hU']
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hAB, hC]
  ring

theorem w279_card_R (i : Fin k) : n = 2 * (w279_R c m i).card + 1 := by
  classical
  have h := w279_card_closed c m hm i Finset.univ (w279_closed_univ c i)
  rw [Finset.card_univ, Fintype.card_fin, if_pos (Finset.mem_univ _)] at h
  have he : Finset.univ.filter (· ∈ w279_R c m i) = w279_R c m i := by ext; simp
  rw [he] at h
  exact h

theorem w279_closed_eq (i : Fin k) (U V : Finset (Fin n)) (hU : w279_closed c i U)
    (hV : w279_closed c i V) (hc : U.card = V.card)
    (h : U.filter (· ∈ w279_R c m i) = V.filter (· ∈ w279_R c m i)) : U = V := by
  classical
  have h1 := w279_card_closed c m hm i U hU
  have h2 := w279_card_closed c m hm i V hV
  have hmm : m i ∈ U ↔ m i ∈ V := by
    rw [h] at h1
    constructor
    · intro hu; by_contra hv; rw [if_pos hu] at h1; rw [if_neg hv] at h2; omega
    · intro hv; by_contra hu; rw [if_neg hu] at h1; rw [if_pos hv] at h2; omega
  have hR : ∀ v ∈ w279_R c m i, (v ∈ U ↔ v ∈ V) := by
    intro v hv
    have := congrArg (fun X => v ∈ X) h
    simpa [hv] using this
  rw [w279_closed_iff c m hm] at hU hV
  ext v
  by_cases hvm : v = m i
  · rw [hvm]; exact hmm
  by_cases hvR : v ∈ w279_R c m i
  · exact hR v hvR
  have hpR : w279_pc c i v ∈ w279_R c m i := by
    simp only [w279_R, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hvR ⊢
    obtain ⟨h', -⟩ := w279_pc_spec c m hm i v hvm
    refine ⟨w279_pc_ne c m hm i v hvm, ?_⟩
    rw [w279_pc_pc c m hm i v hvm]
    exact lt_of_le_of_ne (hvR hvm) (Ne.symm h')
  have hpm := w279_pc_ne c m hm i v hvm
  have hpp := w279_pc_pc c m hm i v hvm
  constructor
  · intro hv
    have := (hR _ hpR).1 (hU v hv hvm)
    have := hV _ this hpm
    rwa [hpp] at this
  · intro hv
    have := (hR _ hpR).2 (hV v hv hvm)
    have := hU _ this hpm
    rwa [hpp] at this

open Classical in
theorem w279_count_closed (i : Fin k) (s : ℕ) :
    (Finset.univ.filter fun U : Finset (Fin n) => U.card = s ∧ w279_closed c i U).card ≤
      (w279_R c m i).card.choose (s / 2) := by
  classical
  rw [← Finset.card_powersetCard]
  refine Finset.card_le_card_of_injOn (fun U => U.filter (· ∈ w279_R c m i)) ?_ ?_
  · intro U hU
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨fun v hv => (Finset.mem_filter.1 hv).2, ?_⟩
    have := w279_card_closed c m hm i U hU.2
    split_ifs at this <;> omega
  · intro U hU V hV h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hU hV
    exact w279_closed_eq c m hm i U V hU.2 hV.2 (hU.1.trans hV.1.symm) h

open Classical in
theorem w279_count_closed_mem (i : Fin k) (s : ℕ) (w : Fin n) (hw : w ≠ m i) :
    (Finset.univ.filter fun U : Finset (Fin n) => U.card = s ∧ w279_closed c i U ∧ w ∈ U).card ≤
      ((w279_R c m i).card - 1).choose (s / 2 - 1) := by
  classical
  let x := if w ∈ w279_R c m i then w else w279_pc c i w
  have hx : x ∈ w279_R c m i := by
    simp only [x]
    split_ifs with h
    · exact h
    · simp only [w279_R, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at h ⊢
      obtain ⟨h', -⟩ := w279_pc_spec c m hm i w hw
      refine ⟨w279_pc_ne c m hm i w hw, ?_⟩
      rw [w279_pc_pc c m hm i w hw]
      exact lt_of_le_of_ne (h hw) (Ne.symm h')
  have hxU : ∀ U, w279_closed c i U → w ∈ U → x ∈ U := by
    intro U hU hwU
    simp only [x]
    split_ifs
    · exact hwU
    · exact (w279_closed_iff c m hm i U).1 hU w hwU hw
  have hcardR := Finset.card_erase_of_mem hx
  rw [← hcardR, ← Finset.card_powersetCard]
  refine Finset.card_le_card_of_injOn (fun U => (U.filter (· ∈ w279_R c m i)).erase x) ?_ ?_
  · intro U hU
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase _ (fun v hv => (Finset.mem_filter.1 hv).2), ?_⟩
    have hxU' : x ∈ U.filter (· ∈ w279_R c m i) := Finset.mem_filter.2 ⟨hxU U hU.2.1 hU.2.2, hx⟩
    have key : (U.filter (· ∈ w279_R c m i)).card = s / 2 := by
      have h5 := w279_card_closed c m hm i U hU.2.1
      have h6 := hU.1
      split_ifs at h5 <;> omega
    rw [Finset.card_erase_of_mem hxU', key]
  · intro U hU V hV h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hU hV
    refine w279_closed_eq c m hm i U V hU.2.1 hV.2.1 (hU.1.trans hV.1.symm) ?_
    have h' := congrArg (insert x) h
    simp only at h'
    rwa [Finset.insert_erase (Finset.mem_filter.2 ⟨hxU U hU.2.1 hU.2.2, hx⟩),
      Finset.insert_erase (Finset.mem_filter.2 ⟨hxU V hV.2.1 hV.2.2, hx⟩)] at h'

open Classical in
theorem w279_count_closed_mem_m (i : Fin k) (s : ℕ) :
    (Finset.univ.filter fun U : Finset (Fin n) => U.card = s ∧ w279_closed c i U ∧ m i ∈ U).card ≤
      if s % 2 = 1 then (w279_R c m i).card.choose (s / 2) else 0 := by
  classical
  split_ifs with hs
  · refine le_trans (Finset.card_le_card ?_) (w279_count_closed c m hm i s)
    intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    exact ⟨hU.1, hU.2.1⟩
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro U - ⟨h1, h2, h3⟩
    have := w279_card_closed c m hm i U h2
    rw [if_pos h3] at this
    omega

end

/-- events with domain `D` and closed image are at most `|D|!` per image -/
theorem w279_count_maps {n : ℕ} (D U : Finset (Fin n)) (hU : U.card = D.card) :
    (Finset.univ.filter (fun f : Fin n → Fin n => (∀ v ∉ D, f v = v) ∧ Set.InjOn f ↑D ∧
      D.image f = U)).card ≤ D.card.factorial := by
  classical
  set S := Finset.univ.filter (fun f : Fin n → Fin n => (∀ v ∉ D, f v = v) ∧ Set.InjOn f ↑D ∧
      D.image f = U) with hS
  have mem : ∀ f ∈ S, (∀ v ∉ D, f v = v) ∧ Set.InjOn f ↑D ∧ D.image f = U := by
    intro f hf; simpa [hS] using hf
  let Φ : S → (D ↪ U) := fun f => ⟨fun x => ⟨f.1 x.1, by
      rw [← (mem f.1 f.2).2.2]; exact Finset.mem_image_of_mem _ x.2⟩,
    fun x y h => Subtype.ext ((mem f.1 f.2).2.1 x.2 y.2 (congrArg Subtype.val h))⟩
  have hΦ : Function.Injective Φ := by
    intro f f' hff
    apply Subtype.ext; funext v
    by_cases hv : v ∈ D
    · have := congrArg (fun φ : D ↪ U => (φ ⟨v, hv⟩ : Fin n)) hff
      exact this
    · rw [(mem f.1 f.2).1 v hv, (mem f'.1 f'.2).1 v hv]
  have := Fintype.card_le_of_injective Φ hΦ
  rwa [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe, hU,
    Nat.descFactorial_self] at this

theorem w279_count_events {n : ℕ} (D : Finset (Fin n)) (P : Finset (Fin n) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun f : Fin n → Fin n => (∀ v ∉ D, f v = v) ∧ Set.InjOn f ↑D ∧
      P (D.image f))).card ≤ D.card.factorial *
      (Finset.univ.filter fun U : Finset (Fin n) => U.card = D.card ∧ P U).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => D.image f)
    (t := Finset.univ.filter fun U : Finset (Fin n) => U.card = D.card ∧ P U)]
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun U hU => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    refine le_trans (Finset.card_le_card ?_) (w279_count_maps D U hU.1)
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨hf.1.1, hf.1.2.1, hf.2⟩
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact ⟨Finset.card_image_of_injOn hf.2.1, hf.2.2⟩


def w279_blk (v : Fin 279) : Fin 93 := ⟨v.val / 3, by omega⟩

def w279_pos (T : Finset (Fin 93)) : Finset (Fin 279) :=
  Finset.univ.filter fun v => w279_blk v ∈ T

theorem w279_mem_pos {v : Fin 279} {T : Finset (Fin 93)} : v ∈ w279_pos T ↔ w279_blk v ∈ T := by
  simp [w279_pos]

theorem w279_blk_fibre (b : Fin 93) :
    (Finset.univ.filter fun v : Fin 279 => w279_blk v = b).card = 3 := by
  have hb := b.isLt
  have : (Finset.univ.filter fun v : Fin 279 => w279_blk v = b) =
      {⟨3 * b.val, by omega⟩, ⟨3 * b.val + 1, by omega⟩, ⟨3 * b.val + 2, by omega⟩} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, w279_blk, Fin.ext_iff]
    omega
  rw [this, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_pair (by simp [Fin.ext_iff])]

theorem w279_card_pos (T : Finset (Fin 93)) : (w279_pos T).card = 3 * T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := w279_blk) (t := T)]
  · rw [Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const, smul_eq_mul, mul_comm]
    intro b hb
    rw [← w279_blk_fibre b]
    have : (w279_pos T).filter (fun v => w279_blk v = b) = Finset.univ.filter (fun v => w279_blk v = b) := by
      ext v
      rw [Finset.mem_filter, Finset.mem_filter, w279_mem_pos]
      constructor
      · exact fun h => ⟨Finset.mem_univ _, h.2⟩
      · intro h; exact ⟨h.2 ▸ hb, h.2⟩
    rw [this]
  · intro v hv
    exact w279_mem_pos.1 hv

noncomputable def w279_wt (d : ℕ) : ℝ := (323 / 279 : ℝ) ^ d / ((Nat.descFactorial 279 d : ℕ) : ℝ)

theorem w279_wt_nonneg (d : ℕ) : 0 ≤ w279_wt d := by
  unfold w279_wt; positivity

theorem w279_wt_lt_one (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 138) : w279_wt d < 1 := by
  unfold w279_wt
  have hdesc : (142 : ℕ) ^ d ≤ Nat.descFactorial 279 d :=
    le_trans (Nat.pow_le_pow_left (by omega) d) (Nat.pow_sub_le_descFactorial 279 d)
  have hpos : (0 : ℝ) < ((Nat.descFactorial 279 d : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  rw [div_lt_one hpos]
  calc (323 / 279 : ℝ) ^ d < (142 : ℝ) ^ d := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    _ ≤ _ := by exact_mod_cast hdesc

open Classical in
@[irreducible] noncomputable def w279_E (c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin 279)) :
    Finset (Fin 279 × Finset (Fin 93) × (Fin 279 → Fin 279)) :=
  Finset.univ.filter fun t => 1 ≤ t.2.1.card ∧ t.2.1.card ≤ 46 ∧
    (∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧
    w279_closed c t.1 ((w279_pos t.2.1).image t.2.2)

theorem w279_mem_filter_univ {α : Type*} {fi : Fintype α} {P : α → Prop} {inst : DecidablePred P} {a : α} :
    a ∈ @Finset.filter α P inst (@Finset.univ α fi) ↔ P a :=
  ⟨fun h => ((@Finset.mem_filter α P inst _ a).1 h).2,
    fun h => (@Finset.mem_filter α P inst _ a).2 ⟨@Finset.mem_univ α fi a, h⟩⟩

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem w279_mem_E {c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin 279)}
    {t : Fin 279 × Finset (Fin 93) × (Fin 279 → Fin 279)} :
    t ∈ w279_E c ↔ 1 ≤ t.2.1.card ∧ t.2.1.card ≤ 46 ∧
      (∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧
      w279_closed c t.1 ((w279_pos t.2.1).image t.2.2) := by
  unfold w279_E
  exact w279_mem_filter_univ

theorem w279_num_pos :
    ∑ m ∈ Finset.range 93, ((Nat.choose 92 m : ℕ) : ℝ) *
      (if m + 1 ≤ 46 then (279 : ℝ) * (((3 * (m + 1)).factorial * Nat.choose 139 (3 * (m + 1) / 2) : ℕ) : ℝ) *
        w279_wt (3 * (m + 1)) else 0) ≤ 701 / 10000 := by
  have hq := wild_partition_position_mass_279_certificate
  have h2 := (Rat.cast_le (K := ℝ)).2 hq
  rw [Rat.cast_sum] at h2
  refine le_trans (le_of_eq ?_) (h2.trans (by norm_num))
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold w279_wt
  split_ifs <;> push_cast <;> ring

theorem w279_num_vert :
    ∑ m ∈ Finset.range 94, ((Nat.choose 93 m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ 46 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose 139 (3 * m / 2) else 0)
        + 278 * ((3 * m).factorial * Nat.choose 138 (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        w279_wt (3 * m) else 0) ≤ 701 / 10000 := by
  have hq := wild_partition_vertex_mass_279_certificate
  have h2 := (Rat.cast_le (K := ℝ)).2 hq
  rw [Rat.cast_sum] at h2
  refine le_trans (le_of_eq ?_) (h2.trans (by norm_num))
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold w279_wt
  split_ifs <;> push_cast <;> ring

section
variable (c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin 279)) (m : Fin 279 ≃ Fin 279)
  (hm : ∀ (i : Fin 279) (v : Fin 279), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
include hm

theorem w279_R_card (i : Fin 279) : (w279_R c m i).card = 139 := by
  have := w279_card_R c m hm i
  omega

set_option maxRecDepth 100000 in
/-- the events of colour `i` on blocks `T` -/
theorem w279_fibre_card (i : Fin 279) (T : Finset (Fin 93)) (P : Finset (Fin 279) → Prop) [DecidablePred P]
    (Fsel : Finset (Fin 279 × Finset (Fin 93) × (Fin 279 → Fin 279)))
    (hF : ∀ t ∈ Fsel, t.1 = i → t.2.1 = T → (∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧
      P ((w279_pos t.2.1).image t.2.2)) :
    (Fsel.filter fun t => (t.1, t.2.1) = (i, T)).card ≤ (3 * T.card).factorial *
      (Finset.univ.filter fun U : Finset (Fin 279) => U.card = 3 * T.card ∧ P U).card := by
  classical
  rw [← w279_card_pos]
  refine le_trans ?_ (w279_count_events (w279_pos T) P)
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht
    obtain ⟨ht, h1, h2⟩ := ht
    obtain ⟨g1, g2, g3⟩ := hF t ht h1 h2
    rw [h2] at g1 g2 g3
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨g1, g2, g3⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht ht'
    obtain ⟨-, h1, h2⟩ := ht
    obtain ⟨-, h1', h2'⟩ := ht'
    exact Prod.ext (h1.trans h1'.symm) (Prod.ext (h2.trans h2'.symm) h)

set_option maxRecDepth 100000 in
theorem w279_pos_mass (p : Fin 279) :
    ∑ t ∈ (w279_E c).filter (fun t => p ∈ w279_pos t.2.1), w279_wt (w279_pos t.2.1).card ≤ 701 / 10000 := by
  classical
  set Fsel := (w279_E c).filter (fun t => p ∈ w279_pos t.2.1) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ 46 ∧ w279_blk p ∈ t.2.1) ∧
      ((∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧
      w279_closed c t.1 ((w279_pos t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, w279_mem_E] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1, w279_mem_pos.1 ht.2⟩, ht.1.2.2⟩
  let 𝒯 : Finset (Finset (Fin 93)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ 46 ∧ w279_blk p ∈ T
  let φ : ℕ → ℝ := fun h => (((3 * h).factorial * Nat.choose 139 (3 * h / 2) : ℕ) : ℝ) * w279_wt (3 * h)
  have step1 : ∑ t ∈ Fsel, w279_wt (w279_pos t.2.1).card ≤ ∑ x ∈ (Finset.univ : Finset (Fin 279)) ×ˢ 𝒯, φ x.2.card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), w279_wt (w279_pos t.2.1).card = w279_wt (3 * x.2.card) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [w279_card_pos, ← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := w279_fibre_card c m hm x.1 x.2 (fun U => w279_closed c x.1 U) Fsel ?_
      · have hc2 := w279_count_closed c m hm x.1 (3 * x.2.card)
        rw [w279_R_card c m hm] at hc2
        have hc3 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (3 * x.2.card).factorial * Nat.choose 139 (3 * x.2.card / 2) := by
          refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
          intro U hU
          simp only [Finset.mem_filter] at hU ⊢
          exact hU
        simp only [φ]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc3) (w279_wt_nonneg _)
      · intro t ht hi _
        obtain ⟨-, h1, h2, h3⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin 279)) ×ˢ 𝒯, φ x.2.card = 279 * ∑ T ∈ 𝒯, φ T.card := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have step3 : ∑ T ∈ 𝒯, φ T.card = ∑ m ∈ Finset.range 93, ((Nat.choose 92 m : ℕ) : ℝ) *
      (if m + 1 ≤ 46 then φ (m + 1) else 0) := by
    set b := w279_blk p
    have hcard : (Finset.univ.erase b).card = 92 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have e1 : ∑ T ∈ 𝒯, φ T.card = ∑ T' ∈ (Finset.univ.erase b).powerset.filter (fun T' => T'.card + 1 ≤ 46),
        φ (T'.card + 1) := by
      refine Finset.sum_nbij' (fun T => T.erase b) (fun T' => insert b T') ?_ ?_ ?_ ?_ ?_
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_add_one hT.2.2]; exact hT.2.1
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.card_insert_of_notMem hb]
        exact ⟨by omega, hT'.2, Finset.mem_insert_self _ _⟩
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        exact Finset.insert_erase hT.2.2
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        exact Finset.erase_insert hb
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        rw [Finset.card_erase_add_one hT.2.2]
    rw [e1, Finset.sum_filter]
    have := Finset.sum_powerset_apply_card (fun m => if m + 1 ≤ 46 then φ (m + 1) else 0)
      (x := Finset.univ.erase b)
    rw [hcard] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := by rw [step2, step3]
    _ = ∑ m ∈ Finset.range 93, ((Nat.choose 92 m : ℕ) : ℝ) *
      (if m + 1 ≤ 46 then (279 : ℝ) * (((3 * (m + 1)).factorial * Nat.choose 139 (3 * (m + 1) / 2) : ℕ) : ℝ) *
        w279_wt (3 * (m + 1)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs
      · simp only [φ]; ring
      · ring
    _ ≤ 701 / 10000 := w279_num_pos

set_option maxRecDepth 100000 in
theorem w279_vert_mass (w : Fin 279) :
    ∑ t ∈ (w279_E c).filter (fun t => w ∈ (w279_pos t.2.1).image t.2.2),
      w279_wt (w279_pos t.2.1).card ≤ 701 / 10000 := by
  classical
  set Fsel := (w279_E c).filter (fun t => w ∈ (w279_pos t.2.1).image t.2.2) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ 46) ∧
      ((∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧
      (w279_closed c t.1 ((w279_pos t.2.1).image t.2.2) ∧ w ∈ (w279_pos t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, w279_mem_E] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1⟩, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2, ht.2⟩
  let 𝒯 : Finset (Finset (Fin 93)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ 46
  let X : ℕ → ℕ := fun s => if s % 2 = 1 then Nat.choose 139 (s / 2) else 0
  let Y : ℕ → ℕ := fun s => Nat.choose 138 (s / 2 - 1)
  let bnd : Fin 279 → ℕ → ℝ := fun i s => (s.factorial : ℝ) * (if m i = w then (X s : ℝ) else (Y s : ℝ))
  have step1 : ∑ t ∈ Fsel, w279_wt (w279_pos t.2.1).card ≤
      ∑ x ∈ (Finset.univ : Finset (Fin 279)) ×ˢ 𝒯, bnd x.1 (3 * x.2.card) * w279_wt (3 * x.2.card) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), w279_wt (w279_pos t.2.1).card = w279_wt (3 * x.2.card) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [w279_card_pos, ← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := w279_fibre_card c m hm x.1 x.2 (fun U => w279_closed c x.1 U ∧ w ∈ U) Fsel ?_
      · have hc2 : (Finset.univ.filter fun U : Finset (Fin 279) => U.card = 3 * x.2.card ∧
            (w279_closed c x.1 U ∧ w ∈ U)).card ≤ if m x.1 = w then X (3 * x.2.card) else Y (3 * x.2.card) := by
          split_ifs with hmw
          · have := w279_count_closed_mem_m c m hm x.1 (3 * x.2.card)
            rw [w279_R_card c m hm, hmw] at this
            exact this
          · have := w279_count_closed_mem c m hm x.1 (3 * x.2.card) w (Ne.symm hmw)
            rw [w279_R_card c m hm] at this
            exact this
        have hc3 : ((Fsel.filter fun t => (t.1, t.2.1) = x).card : ℝ) ≤ bnd x.1 (3 * x.2.card) := by
          have h4 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (3 * x.2.card).factorial *
              (if m x.1 = w then X (3 * x.2.card) else Y (3 * x.2.card)) := by
            refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
            intro U hU
            simp only [Finset.mem_filter] at hU ⊢
            exact hU
          simp only [bnd]
          split_ifs at h4 ⊢ <;> exact_mod_cast h4
        exact mul_le_mul_of_nonneg_right hc3 (w279_wt_nonneg _)
      · intro t ht hi _
        obtain ⟨-, h1, h2, h3, h4⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3, h4⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hsumcol : ∀ s, ∑ i : Fin 279, bnd i s = (((s.factorial * X s + 278 * (s.factorial * Y s)) : ℕ) : ℝ) := by
    intro s
    have h1 : (Finset.univ.filter fun i : Fin 279 => m i = w) = {m.symm w} := by
      ext i; simp [Equiv.apply_eq_iff_eq_symm_apply]
    have h2 : (Finset.univ.filter fun i : Fin 279 => ¬ m i = w).card = 278 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 279)))
        (p := fun i => m i = w)
      rw [h1, Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at this
      omega
    simp only [bnd, mul_ite]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_singleton]
    push_cast
    ring
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin 279)) ×ˢ 𝒯, bnd x.1 (3 * x.2.card) * w279_wt (3 * x.2.card) =
      ∑ T ∈ 𝒯, (((3 * T.card).factorial * X (3 * T.card) + 278 * ((3 * T.card).factorial * Y (3 * T.card)) : ℕ) : ℝ)
        * w279_wt (3 * T.card) := by
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    dsimp only
    rw [← Finset.sum_mul, hsumcol]
  have step3 : ∑ T ∈ 𝒯, (((3 * T.card).factorial * X (3 * T.card) + 278 * ((3 * T.card).factorial * Y (3 * T.card)) : ℕ) : ℝ)
        * w279_wt (3 * T.card) = ∑ m ∈ Finset.range 94, ((Nat.choose 93 m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ 46 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose 139 (3 * m / 2) else 0)
        + 278 * ((3 * m).factorial * Nat.choose 138 (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        w279_wt (3 * m) else 0) := by
    rw [Finset.sum_filter, ← Finset.powerset_univ]
    have := Finset.sum_powerset_apply_card (fun m => if 1 ≤ m ∧ m ≤ 46 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose 139 (3 * m / 2) else 0)
        + 278 * ((3 * m).factorial * Nat.choose 138 (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        w279_wt (3 * m) else 0) (x := (Finset.univ : Finset (Fin 93)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := by rw [step2, step3]
    _ ≤ 701 / 10000 := w279_num_vert

end

set_option maxRecDepth 100000 in
theorem w279_avoid (c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin 279)) (m : Fin 279 ≃ Fin 279)
    (hm : ∀ (i : Fin 279) (v : Fin 279), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ σ : Equiv.Perm (Fin 279), ∀ t ∈ w279_E c, ∃ v ∈ w279_pos t.2.1, σ v ≠ t.2.2 v := by
  classical
  have hmemE : ∀ t ∈ w279_E c, 1 ≤ t.2.1.card ∧ t.2.1.card ≤ 46 ∧ (∀ v ∉ w279_pos t.2.1, t.2.2 v = v) ∧
      Set.InjOn t.2.2 ↑(w279_pos t.2.1) ∧ w279_closed c t.1 ((w279_pos t.2.1).image t.2.2) := by
    intro t ht; exact w279_mem_E.1 ht
  let D : ↥(w279_E c) → Finset (Fin 279) := fun j => w279_pos j.1.2.1
  let f : ↥(w279_E c) → Fin 279 → Fin 279 := fun j => j.1.2.2
  let x : ↥(w279_E c) → ℝ := fun j => w279_wt (D j).card
  have hDcard : ∀ j : ↥(w279_E c), 3 ≤ (D j).card ∧ (D j).card ≤ 138 := by
    intro j; have := hmemE j.1 j.2; simp only [D, w279_card_pos]; omega
  have hsumI : ∀ (P : (Fin 279 × Finset (Fin 93) × (Fin 279 → Fin 279)) → Prop) [DecidablePred P],
      ∑ j ∈ (Finset.univ : Finset ↥(w279_E c)).filter (fun j => P j.1), x j =
        ∑ t ∈ (w279_E c).filter P, w279_wt (w279_pos t.2.1).card := by
    intro P _
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_coe_sort (w279_E c) (fun t => if P t then w279_wt (w279_pos t.2.1).card else 0)
  have hx0 : ∀ j, 0 ≤ x j := fun j => w279_wt_nonneg _
  have hx1 : ∀ j, x j < 1 := fun j => w279_wt_lt_one _ (by have := hDcard j; omega) (hDcard j).2
  have hprob : ∀ i, (1 : ℝ) / ((279 : ℕ).descFactorial (D i).card : ℝ) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
        ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))), (1 - x j) := by
    intro i
    set d := (D i).card with hd
    set N := Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
      ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))) with hN
    let Fsel : ↥(w279_E c) → Fin 279 ⊕ Fin 279 := fun j =>
      if h : (D i ∩ D j).Nonempty then Sum.inl (Classical.choose h)
      else if h' : ((D i).image (f i) ∩ (D j).image (f j)).Nonempty then Sum.inr (Classical.choose h')
      else Sum.inl 0
    let S : Finset (Fin 279 ⊕ Fin 279) :=
      (D i).map Function.Embedding.inl ∪ ((D i).image (f i)).map Function.Embedding.inr
    have hNmem : ∀ j ∈ N, (D i ∩ D j).Nonempty ∨ ((D i).image (f i) ∩ (D j).image (f j)).Nonempty := by
      intro j hj
      rw [hN, Finset.mem_filter] at hj
      rw [← Finset.not_disjoint_iff_nonempty_inter, ← Finset.not_disjoint_iff_nonempty_inter]
      exact hj.2.2
    have hfS : ∀ j ∈ N, Fsel j ∈ S := by
      intro j hj
      have h0 := hNmem j hj
      simp only [Fsel]
      split_ifs with h h'
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h)).1, rfl⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h')).1, rfl⟩))
      · exact absurd h0 (by tauto)
    have hmass : ∀ r ∈ S, ∑ j ∈ N.filter (fun j => Fsel j = r), x j ≤ 701 / 10000 := by
      intro r _
      rcases r with p | w
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(w279_E c)).filter (fun j => p ∈ w279_pos j.1.2.1), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              · have := (Finset.mem_inter.1 (Classical.choose_spec h)).2
                rw [Sum.inl.injEq] at hF
                rw [← hF]; exact this
              · exact absurd h0 (by tauto)
          _ = _ := hsumI (fun t => p ∈ w279_pos t.2.1)
          _ ≤ _ := w279_pos_mass c m hm p
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(w279_E c)).filter
                (fun j => w ∈ (w279_pos j.1.2.1).image j.1.2.2), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              have := (Finset.mem_inter.1 (Classical.choose_spec h')).2
              rw [Sum.inr.injEq] at hF
              rw [← hF]; exact this
          _ = _ := hsumI (fun t => w ∈ (w279_pos t.2.1).image t.2.2)
          _ ≤ _ := w279_vert_mass c m hm w
    have hfib := finite_product_one_sub_lower_bound_by_fibres N S Fsel x (701 / 10000) (by norm_num) (by norm_num)
      (fun j _ => ⟨hx0 j, (hx1 j).le⟩) hfS hmass
    have hcardS : S.card ≤ 2 * d := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_map, Finset.card_map]
      have := Finset.card_image_le (s := D i) (f := f i)
      omega
    have hM : (1 - 701 / 10000 : ℝ) ^ (2 * d) ≤ (1 - 701 / 10000) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcardS
    have hpos : (0 : ℝ) < ((Nat.descFactorial 279 d : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.2 (by have := hDcard i; omega)
    change (1 : ℝ) / _ ≤ w279_wt d * ∏ j ∈ N, (1 - x j)
    unfold w279_wt
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    calc (1 : ℝ) ≤ ((323 / 279 : ℝ) * (1 - 701 / 10000) ^ 2) ^ d := one_le_pow₀ (by norm_num)
      _ = (323 / 279 : ℝ) ^ d * (1 - 701 / 10000) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
      _ ≤ (323 / 279 : ℝ) ^ d * ∏ j ∈ N, (1 - x j) :=
        mul_le_mul_of_nonneg_left (hM.trans hfib) (by positivity)
  obtain ⟨σ, hσ⟩ := canonical_permutation_avoidance_of_local_lemma 279 (by norm_num) D f
    (fun j => Finset.card_pos.1 (by have := hDcard j; omega)) (fun j => (hmemE j.1 j.2).2.2.2.1) x hx0 hx1 hprob
  exact ⟨σ, fun t ht => hσ ⟨t, ht⟩⟩

set_option maxRecDepth 100000 in
theorem w279_upper (c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin 279)) (m : Fin 279 ≃ Fin 279)
    (hm : ∀ (i : Fin 279) (v : Fin 279), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin 279)) c ≤ 186 := by
  classical
  obtain ⟨σ, hσ⟩ := w279_avoid c m hm
  have hup := simple_graph_wild_number_le_of_block_cut_condition (n := 279) (q := 93) (by norm_num) c
    (fun v => w279_blk (σ.symm v)) (fun b => σ ⟨3 * b.val, by omega⟩) ?_ ?_
  · simpa using hup
  · intro b
    show w279_blk (σ.symm (σ _)) = b
    apply Fin.ext
    simp only [Equiv.symm_apply_apply, w279_blk]
    omega
  · intro e S hS hSu
    by_contra hcon
    have hno : ∀ u v (huv : u ≠ v), w279_blk (σ.symm u) ∈ S → w279_blk (σ.symm v) ∉ S →
        c ⟨s(u, v), wild_kn_mem huv⟩ ≠ c e := by
      intro u v huv hu hv hc; exact hcon ⟨u, v, huv, hu, hv, hc⟩
    have hScard : 1 ≤ S.card ∧ S.card ≤ 92 := by
      refine ⟨Finset.card_pos.2 hS, ?_⟩
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ S, hSu⟩)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    set T := if S.card ≤ 46 then S else Finset.univ \ S with hTdef
    have hT : 1 ≤ T.card ∧ T.card ≤ 46 := by
      rw [hTdef]; split_ifs with h
      · omega
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega
    have hTclosed : ∀ u w (huw : u ≠ w), w279_blk (σ.symm u) ∈ T →
        c ⟨s(u, w), wild_kn_mem huw⟩ = c e → w279_blk (σ.symm w) ∈ T := by
      intro u w huw hu hc
      rw [hTdef] at hu ⊢
      split_ifs at hu ⊢ with h
      · by_contra hw; exact hno u w huw hu hw hc
      · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hu ⊢
        intro hw
        refine hno w u (Ne.symm huw) hw hu ?_
        exact (w279_c_swap c (Ne.symm huw)).trans hc
    let gext : Fin 279 → Fin 279 := fun v => if v ∈ w279_pos T then σ v else v
    have himg : ∀ u, u ∈ (w279_pos T).image gext ↔ w279_blk (σ.symm u) ∈ T := by
      intro u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
        simp only [gext, if_pos hv, Equiv.symm_apply_apply]
        exact w279_mem_pos.1 hv
      · intro hu
        have hu' : σ.symm u ∈ w279_pos T := w279_mem_pos.2 hu
        exact Finset.mem_image.2 ⟨σ.symm u, hu', by simp only [gext, if_pos hu', Equiv.apply_symm_apply]⟩
    have hmem : (c e, T, gext) ∈ w279_E c := by
      rw [w279_mem_E]
      refine ⟨hT.1, hT.2, ?_, ?_, ?_⟩
      · intro v hv; simp only [gext, if_neg hv]
      · intro a ha b hb hab
        simp only [gext, Finset.mem_coe] at ha hb hab
        rw [if_pos ha, if_pos hb] at hab
        exact σ.injective hab
      · intro u hu w huw hc
        rw [himg] at hu ⊢
        exact hTclosed u w huw hu hc
    obtain ⟨v, hv, hne⟩ := hσ _ hmem
    simp only [gext] at hne
    exact hne (by rw [if_pos hv])

theorem wild_number_complete_graph_279_min_proper_coloring_eq (k : ℕ)
    (hk : (⊤ : SimpleGraph (Fin 279)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin 279)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin 279)) c = 186 := by
  obtain ⟨m, hm⟩ := w279_missing_vertex_equiv 279 k (by norm_num) (by norm_num) hk c
  have hk' : k = 279 := by simpa using Fintype.card_congr m
  subst hk'
  have hlow := wild_number_complete_graph_min_proper_coloring_ge 279 279 (by norm_num) hk c
  norm_num at hlow
  exact le_antisymm (w279_upper c m hm) hlow
