import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.Tcs.RegularBipartiteHasPerfectMatching

/-!
# equal_marginal_balanced_high_count_allocations

Topic: fair_division   Node: 0aa482248efb

Provenance: helper lemma. Sorted-slot matching construction, arXiv:2609.35280, Section 3.1, specialized to equal-sized slots.

For at least two agents, k at least two, and n*k chores, each agent has an arbitrary set of high chores. There are n allocations such that each chore goes once to each agent across the n allocations; in each allocation every agent receives exactly k chores and her high chore count times n is at most the total number of her high chores plus n minus one.
-/

/-- Hall: a d-regular bipartite relation (d > 0) between equal-size sides has a matching
covering X. -/
theorem equal_marginal_alloc_hall {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (R : X → Finset Y) (d : ℕ) (hd : 0 < d)
    (hX : ∀ x, (R x).card = d)
    (hY : ∀ y, (Finset.univ.filter (fun x => y ∈ R x)).card ≤ d) :
    ∃ f : X → Y, Function.Injective f ∧ ∀ x, f x ∈ R x := by
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  intro s
  set T := s.biUnion R
  have h1 : ∑ x ∈ s, (R x).card = s.card * d := by
    rw [Finset.sum_congr rfl (fun x _ => hX x)]; simp
  have h2 : ∑ x ∈ s, (R x).card = ∑ y ∈ T, (s.filter (fun x => y ∈ R x)).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun x y => y ∈ R x) (s := s) (t := T)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun hy => ⟨Finset.mem_biUnion.2 ⟨x, hx, hy⟩, hy⟩, fun h => h.2⟩
  have h3 : ∑ y ∈ T, (s.filter (fun x => y ∈ R x)).card ≤ T.card * d := by
    calc ∑ y ∈ T, (s.filter (fun x => y ∈ R x)).card ≤ ∑ y ∈ T, d := by
          refine Finset.sum_le_sum (fun y _ => le_trans ?_ (hY y))
          exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      _ = T.card * d := by simp
  have : s.card * d ≤ T.card * d := by omega
  exact Nat.le_of_mul_le_mul_right this hd

/-- Decomposition of a d-regular bipartite relation between equal-size sides into d
bijections. -/
theorem equal_marginal_alloc_decomp {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (hcard : Fintype.card X = Fintype.card Y) :
    ∀ (d : ℕ) (R : X → Finset Y), (∀ x, (R x).card = d) →
    (∀ y, (Finset.univ.filter (fun x => y ∈ R x)).card = d) →
    ∃ f : Fin d → X → Y, (∀ t x, f t x ∈ R x) ∧ (∀ t, Function.Injective (f t)) ∧
      (∀ x, Function.Injective (fun t => f t x)) := by
  intro d
  induction d with
  | zero =>
    intro R _ _
    exact ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t,
      fun x a => Fin.elim0 a⟩
  | succ d ih =>
    intro R hX hY
    obtain ⟨g, hginj, hgR⟩ := equal_marginal_alloc_hall R (d + 1) (Nat.succ_pos d) hX (fun y => (hY y).le)
    have hgbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, hcard⟩
    set R' : X → Finset Y := fun x => (R x).erase (g x) with hR'
    have hX' : ∀ x, (R' x).card = d := by
      intro x; simp [hR', Finset.card_erase_of_mem (hgR x), hX x]
    have hY' : ∀ y, (Finset.univ.filter (fun x => y ∈ R' x)).card = d := by
      intro y
      obtain ⟨x0, hx0⟩ := hgbij.2 y
      have hmem : x0 ∈ Finset.univ.filter (fun x => y ∈ R x) := by
        simp [← hx0, hgR x0]
      have : Finset.univ.filter (fun x => y ∈ R' x) =
          (Finset.univ.filter (fun x => y ∈ R x)).erase x0 := by
        ext x
        simp only [hR', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hne, hy⟩
          refine ⟨?_, hy⟩
          rintro rfl
          exact hne hx0.symm
        · rintro ⟨hne, hy⟩
          refine ⟨?_, hy⟩
          intro hyg
          exact hne (hginj (hx0.trans hyg)).symm
      simp [this, Finset.card_erase_of_mem hmem, hY y]
    obtain ⟨f', hf'R, hf'inj, hf'col⟩ := ih R' hX' hY'
    refine ⟨(Fin.cons g f' : Fin (d + 1) → X → Y), ?_, ?_, ?_⟩
    · intro t x
      refine Fin.cases ?_ (fun t => ?_) t
      · simpa using hgR x
      · simpa using Finset.mem_of_mem_erase (hf'R t x)
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · simpa using hginj
      · simpa using hf'inj t
    · intro x t1 t2 h
      have key : ∀ t, f' t x ≠ g x := fun t => Finset.ne_of_mem_erase (hf'R t x)
      induction t1 using Fin.cases with
      | zero =>
        induction t2 using Fin.cases with
        | zero => rfl
        | succ t2 => simp at h; exact absurd h.symm (key t2)
      | succ t1 =>
        induction t2 using Fin.cases with
        | zero => simp at h; exact absurd h (key t1)
        | succ t2 =>
          simp at h
          rw [hf'col x h]

/-- An ordering of `Fin N` putting `H` first. -/
theorem equal_marginal_alloc_order (N : ℕ) (H : Finset (Fin N)) :
    ∃ e : Fin N ≃ Fin N, ∀ g, g ∈ H ↔ (e g).val < H.card := by
  have hle : H.card ≤ N := by simpa using Finset.card_le_univ H
  have hc : Fintype.card {x // x ∉ H} = N - H.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
  let e1 : Fin N ≃ {x // x ∈ H} ⊕ {x // x ∉ H} := (Equiv.sumCompl (· ∈ H)).symm
  let e3 : {x // x ∉ H} ≃ Fin (N - H.card) := Fintype.equivFinOfCardEq hc
  let e := e1.trans ((H.equivFin.sumCongr e3).trans
    (finSumFinEquiv.trans (finCongr (by omega : H.card + (N - H.card) = N))))
  refine ⟨e, fun g => ?_⟩
  by_cases hg : g ∈ H
  · simp [e, e1, hg, Equiv.sumCompl_symm_apply_of_pos hg]
  · simp [e, e1, hg, Equiv.sumCompl_symm_apply_of_neg hg]

theorem equal_marginal_alloc_block_card (n k : ℕ) (a : Fin k) :
    (Finset.univ.filter (fun p : Fin (n * k) => p.val / n = a.val)).card = n := by
  have hn : 0 < n ∨ n = 0 := by omega
  rcases hn with hn | hn
  · have hb : ∀ r : Fin n, a.val * n + r.val < n * k := by
      intro r
      have h1 : a.val + 1 ≤ k := a.isLt
      have h2 : (a.val + 1) * n ≤ k * n := Nat.mul_le_mul_right n h1
      have h3 : (a.val + 1) * n = a.val * n + n := by ring
      have h4 : k * n = n * k := by ring
      have := r.isLt
      omega
    have : Finset.univ.filter (fun p : Fin (n * k) => p.val / n = a.val) =
        (Finset.univ : Finset (Fin n)).map
          ⟨fun r => ⟨a.val * n + r.val, hb r⟩, fun r s h => by
            simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h; exact Fin.ext h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hp
        refine ⟨⟨p.val % n, Nat.mod_lt _ hn⟩, ?_⟩
        apply Fin.ext
        have := Nat.div_add_mod p.val n
        rw [hp] at this
        rw [mul_comm] at this
        omega
      · rintro ⟨r, rfl⟩
        show (a.val * n + r.val) / n = a.val
        apply Nat.div_eq_of_lt_le
        · omega
        · have := r.isLt
          simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
          omega
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · subst hn
    apply Finset.card_eq_zero.2
    ext p
    have := p.isLt
    simp at this

theorem equal_marginal_balanced_high_count_allocations (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (H : Fin n → Finset (Fin (n*k))) : ∃ F : Fin n → Fin (n*k) → Fin n, (∀ g, Function.Bijective (fun t => F t g)) ∧ ∀ t i, (bundle_of (F t) i).card = k ∧ n * ((bundle_of (F t) i ∩ H i).card) ≤ (H i).card + n - 1 := by
  have hn0 : 0 < n := by omega
  choose e he using fun i => equal_marginal_alloc_order (n * k) (H i)
  let C : Fin n × Fin k → Finset (Fin (n * k)) :=
    fun x => Finset.univ.filter (fun g => (e x.1 g).val / n = x.2.val)
  have hmemC : ∀ x g, g ∈ C x ↔ (e x.1 g).val / n = x.2.val := by
    intro x g; simp [C]
  have hX : ∀ x, (C x).card = n := by
    intro x
    exact (Finset.card_equiv (e x.1) (fun g => by simp [C])).trans (equal_marginal_alloc_block_card n k x.2)
  have hlt : ∀ i g, (e i g).val / n < k := by
    intro i g
    exact (Nat.div_lt_iff_lt_mul hn0).2 (lt_of_lt_of_eq (e i g).isLt (mul_comm n k))
  have hY : ∀ g, (Finset.univ.filter (fun x => g ∈ C x)).card = n := by
    intro g
    have : Finset.univ.filter (fun x => g ∈ C x) =
        (Finset.univ : Finset (Fin n)).map
          ⟨fun i => (i, ⟨(e i g).val / n, hlt i g⟩), fun i j h => by
            simpa using congrArg Prod.fst h⟩ := by
      ext ⟨i, a⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk, hmemC]
      constructor
      · intro h
        exact ⟨i, by rw [Prod.mk.injEq]; exact ⟨rfl, Fin.ext h⟩⟩
      · rintro ⟨j, hj⟩
        rw [Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        rfl
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcard : Fintype.card (Fin n × Fin k) = Fintype.card (Fin (n * k)) := by
    simp [Fintype.card_prod]
  obtain ⟨f, hfC, hfinj, hfcol⟩ := equal_marginal_alloc_decomp hcard n C hX hY
  have hbij : ∀ t, Function.Bijective (f t) := fun t =>
    (Fintype.bijective_iff_injective_and_card (f t)).2 ⟨hfinj t, hcard⟩
  let F : Fin n → Fin (n * k) → Fin n :=
    fun t g => ((Equiv.ofBijective (f t) (hbij t)).symm g).1
  have hF : ∀ t g i, F t g = i ↔ ∃ a, f t (i, a) = g := by
    intro t g i
    constructor
    · intro h
      refine ⟨((Equiv.ofBijective (f t) (hbij t)).symm g).2, ?_⟩
      have h2 : (i, ((Equiv.ofBijective (f t) (hbij t)).symm g).2) =
          (Equiv.ofBijective (f t) (hbij t)).symm g := by
        rw [← h]
      rw [h2]
      exact Equiv.ofBijective_apply_symm_apply (f t) (hbij t) g
    · rintro ⟨a, rfl⟩
      simp only [F, Equiv.ofBijective_symm_apply_apply]
  refine ⟨F, ?_, ?_⟩
  · intro g
    rw [← Finite.injective_iff_bijective]
    intro t1 t2 h
    obtain ⟨a1, ha1⟩ := (hF t1 g (F t1 g)).1 rfl
    obtain ⟨a2, ha2⟩ := (hF t2 g (F t1 g)).1 h.symm
    have e1 := (hmemC _ _).1 (ha1 ▸ hfC t1 (F t1 g, a1))
    have e2 := (hmemC _ _).1 (ha2 ▸ hfC t2 (F t1 g, a2))
    have : a1 = a2 := Fin.ext (by simp only at e1 e2; omega)
    subst this
    exact hfcol _ (ha1.trans ha2.symm)
  · intro t i
    have hbund : bundle_of (F t) i = (Finset.univ : Finset (Fin k)).image (fun a => f t (i, a)) := by
      ext g
      simp [bundle_of, hF]
    have hinj : Function.Injective (fun a : Fin k => f t (i, a)) := by
      intro a b h
      have := hfinj t h
      simpa using this
    refine ⟨?_, ?_⟩
    · rw [hbund, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · set h := (H i).card
      have hsub : bundle_of (F t) i ∩ H i ⊆
          (Finset.univ.filter (fun a : Fin k => a.val * n < h)).image (fun a => f t (i, a)) := by
        intro g hg
        rw [Finset.mem_inter, hbund, Finset.mem_image] at hg
        obtain ⟨⟨a, _, rfl⟩, hgH⟩ := hg
        refine Finset.mem_image.2 ⟨a, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 := (he i _).1 hgH
        have h2 := (hmemC _ _).1 (hfC t (i, a))
        simp only at h2
        have h3 : (e i (f t (i, a))).val / n * n ≤ (e i (f t (i, a))).val := Nat.div_mul_le_self _ _
        rw [h2] at h3
        omega
      have hc1 : (bundle_of (F t) i ∩ H i).card ≤
          (Finset.univ.filter (fun a : Fin k => a.val * n < h)).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      have hc2 : (Finset.univ.filter (fun a : Fin k => a.val * n < h)).card ≤ (h + n - 1) / n := by
        have := Finset.card_le_card_of_injOn (fun a : Fin k => a.val)
          (s := Finset.univ.filter (fun a : Fin k => a.val * n < h))
          (t := Finset.range ((h + n - 1) / n))
          (by
            intro a ha
            rw [Finset.mem_coe, Finset.mem_filter] at ha
            replace ha := ha.2
            rw [Finset.mem_coe, Finset.mem_range]
            show a.val < (h + n - 1) / n
            rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hn0]
            have : (a.val + 1) * n = a.val * n + n := by ring
            omega)
          (by intro a _ b _ hab; exact Fin.ext hab)
        simpa using this
      calc n * (bundle_of (F t) i ∩ H i).card ≤ n * ((h + n - 1) / n) :=
            Nat.mul_le_mul_left n (hc1.trans hc2)
        _ ≤ h + n - 1 := Nat.mul_div_le _ _
