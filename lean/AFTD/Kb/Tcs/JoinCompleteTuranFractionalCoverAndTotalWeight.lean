import AFTD.Prelude
import AFTD.Kb.Tcs.JoinCompleteTuranDecidableRel
import AFTD.Kb.Tcs.IsFractionalCliqueCover
import AFTD.Kb.Tcs.JoinCompleteTuranWeight
import AFTD.Kb.Tcs.FractionalKrCoverCliqueWeightAlgebraic
import AFTD.Kb.Tcs.FractionalKrCoverCliqueWeightGeOne
import AFTD.Kb.Tcs.JoinCompleteTuran
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.F

/-!
# join_complete_turan_fractional_cover_and_total_weight

Topic: graphs   Node: 3303312dfeb3

Provenance: formalization of a published result. Source: arXiv:2610.41371 Lemma 3.2

Let n, r, a be integers with r ≥ 3 and a ≤ n. The edge weighting w_a is a fractional K_r-cover of G_a = K_a ∨ T_{r-1}(n-a), and the total weight of w_a over all edges of G_a equals an/(r-1) - a^2/r - a/(r(r-1)).
-/

open Finset

lemma jctf_image_sum {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset V) (w : Sym2 V → ℚ) :
    2 * ∑ e ∈ Q.offDiag.image (fun p => s(p.1, p.2)), w e = ∑ p ∈ Q.offDiag, w s(p.1, p.2) := by
  classical
  set g : V × V → Sym2 V := fun p => s(p.1, p.2) with hg
  have h1 : ∑ e : Sym2 V, (∑ p ∈ Q.offDiag.filter (fun p => g p = e), w (g p)) =
      ∑ p ∈ Q.offDiag, w (g p) :=
    Finset.sum_fiberwise Q.offDiag g (fun p => w (g p))
  have hfib : ∀ e ∈ Q.offDiag.image g,
      (∑ p ∈ Q.offDiag.filter (fun p => g p = e), w (g p)) = 2 * w e := by
    intro e he
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
    obtain ⟨x, y⟩ := p
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hx, hy, hne⟩ := hp
    rw [← hpe]
    have hset : Q.offDiag.filter (fun p => g p = s(x, y)) = {(x, y), (y, x)} := by
      ext q
      obtain ⟨p1, p2⟩ := q
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, hpg⟩
        have hh : s(p1, p2) = s(x, y) := hpg
        rw [Sym2.eq_iff] at hh
        rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨hx, hy, hne⟩, rfl⟩
        · exact ⟨⟨hy, hx, hne.symm⟩, by rw [Sym2.eq_swap]⟩
    rw [hset]
    have hne2 : (x, y) ≠ (y, x) := by intro h; exact hne (congrArg Prod.fst h)
    rw [Finset.sum_pair hne2]
    simp only [hg]
    rw [Sym2.eq_swap]
    ring
  have hzero : ∀ e ∈ (Finset.univ : Finset (Sym2 V)), e ∉ Q.offDiag.image g →
      (∑ p ∈ Q.offDiag.filter (fun p => g p = e), w (g p)) = 0 := by
    intro e _ he
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    exact absurd (Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩) he
  have h2 : ∑ e ∈ Q.offDiag.image g, (∑ p ∈ Q.offDiag.filter (fun p => g p = e), w (g p))
      = ∑ e ∈ (Finset.univ : Finset (Sym2 V)),
          (∑ p ∈ Q.offDiag.filter (fun p => g p = e), w (g p)) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro e _ he; exact hzero e (Finset.mem_univ e) he
  rw [← h1, ← h2, Finset.sum_congr rfl hfib, Finset.mul_sum]

lemma jctf_ordered (n r a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    (∑ p ∈ Q.offDiag, join_complete_turan_weight n r a s(p.1, p.2))
      = ∑ x ∈ Q, ∑ y ∈ Q, (if x ≠ y then join_complete_turan_weight n r a s(x, y) else 0) := by
  classical
  have h : Q.offDiag = (Q ×ˢ Q).filter
      (fun p : (Fin a ⊕ Fin (n - a)) × (Fin a ⊕ Fin (n - a)) => p.1 ≠ p.2) := by
    ext p
    rw [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [h, Finset.sum_filter, Finset.sum_product]

lemma jctf_notleft (n a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    Q.filter (fun y => ¬ Sum.isLeft y = true) = Q.filter (fun y => Sum.isRight y = true) := by
  apply Finset.filter_congr
  intro y _; cases y <;> simp

lemma jctf_disjoint (n a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    Disjoint (Q.filter (fun y => Sum.isLeft y = true)) (Q.filter (fun y => Sum.isRight y = true)) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  simp only [Finset.mem_filter] at hy1 hy2
  cases y <;> simp_all

lemma jctf_split (n a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    Q.filter (fun y => Sum.isLeft y = true) ∪ Q.filter (fun y => Sum.isRight y = true) = Q := by
  ext y; cases y <;> simp

lemma jctf_card_split (n a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    (Q.filter (fun y => Sum.isLeft y = true)).card +
      (Q.filter (fun y => Sum.isRight y = true)).card = Q.card := by
  rw [← Finset.card_union_of_disjoint (jctf_disjoint n a Q), jctf_split]

lemma jctf_inner_left (n r a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) (u : Fin a)
    (hu : Sum.inl u ∈ Q) :
    (∑ y ∈ Q, if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
      = ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
        - (2/((r:ℚ)*((r:ℚ)-1)))
        + ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) * (1/((r:ℚ)-1)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun y => Sum.isLeft y = true)
    (fun y => if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0),
    jctf_notleft]
  have hL : (∑ y ∈ Q.filter (fun y => Sum.isLeft y = true),
        if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
      = ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
        - (2/((r:ℚ)*((r:ℚ)-1))) := by
    have hcons : ∀ y ∈ Q.filter (fun y => Sum.isLeft y = true),
        (if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
          = if y ≠ Sum.inl u then (2/((r:ℚ)*((r:ℚ)-1))) else 0 := by
      intro y hy
      obtain ⟨u', rfl⟩ := Sum.isLeft_iff.mp (Finset.mem_filter.mp hy).2
      by_cases h : u = u'
      · subst h; simp
      · rw [if_pos (by simp [Sum.inl.injEq]; exact h),
          if_pos (by simp [Sum.inl.injEq]; exact fun hh => h hh.symm)]
        rfl
    rw [Finset.sum_congr rfl hcons]
    have hmem : Sum.inl u ∈ Q.filter (fun y => Sum.isLeft y = true) :=
      Finset.mem_filter.mpr ⟨hu, Sum.isLeft_inl⟩
    have hpos : 0 < (Q.filter (fun y => Sum.isLeft y = true)).card :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    rw [← Finset.sum_filter (p := fun y => y ≠ Sum.inl u)
      (f := fun _ => (2/((r:ℚ)*((r:ℚ)-1))))]
    rw [Finset.filter_ne', Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hmem,
      Nat.cast_sub (by omega : 1 ≤ (Q.filter (fun y => Sum.isLeft y = true)).card)]
    ring
  have hR : (∑ y ∈ Q.filter (fun y => Sum.isRight y = true),
        if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
      = ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) * (1/((r:ℚ)-1)) := by
    have hcons : ∀ y ∈ Q.filter (fun y => Sum.isRight y = true),
        (if Sum.inl u ≠ y then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
          = (1/((r:ℚ)-1)) := by
      intro y hy
      obtain ⟨v, rfl⟩ := Sum.isRight_iff.mp (Finset.mem_filter.mp hy).2
      rw [if_pos (by simp)]
      rfl
    rw [Finset.sum_congr rfl hcons, Finset.sum_const, nsmul_eq_mul]
  rw [hL, hR]

lemma jctf_inner_right (n r a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) (v : Fin (n - a)) :
    (∑ y ∈ Q, if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0)
      = ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (1/((r:ℚ)-1)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun y => Sum.isLeft y = true)
    (fun y => if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0),
    jctf_notleft]
  have hL : (∑ y ∈ Q.filter (fun y => Sum.isLeft y = true),
        if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0)
      = ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (1/((r:ℚ)-1)) := by
    have hcons : ∀ y ∈ Q.filter (fun y => Sum.isLeft y = true),
        (if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0)
          = (1/((r:ℚ)-1)) := by
      intro y hy
      obtain ⟨u, rfl⟩ := Sum.isLeft_iff.mp (Finset.mem_filter.mp hy).2
      rw [if_pos (by simp)]
      rfl
    rw [Finset.sum_congr rfl hcons, Finset.sum_const, nsmul_eq_mul]
  have hR : (∑ y ∈ Q.filter (fun y => Sum.isRight y = true),
        if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0) = 0 := by
    have hcons : ∀ y ∈ Q.filter (fun y => Sum.isRight y = true),
        (if Sum.inr v ≠ y then join_complete_turan_weight n r a s(Sum.inr v, y) else 0) = 0 := by
      intro y hy
      obtain ⟨w, rfl⟩ := Sum.isRight_iff.mp (Finset.mem_filter.mp hy).2
      by_cases h : v = w
      · subst h; simp
      · rw [if_pos (by simp [Sum.inr.injEq]; exact h)]
        rfl
    rw [Finset.sum_congr rfl hcons, Finset.sum_const, smul_zero]
  rw [hL, hR, add_zero]

lemma jctf_inner_const (n r a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a)))
    (x : Fin a ⊕ Fin (n - a)) (hx : x ∈ Q) :
    (∑ y ∈ Q, if x ≠ y then join_complete_turan_weight n r a s(x, y) else 0)
      = if Sum.isLeft x = true
          then ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
            - (2/((r:ℚ)*((r:ℚ)-1)))
            + ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) * (1/((r:ℚ)-1))
          else ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (1/((r:ℚ)-1)) := by
  cases x with
  | inl u => rw [if_pos Sum.isLeft_inl, jctf_inner_left n r a Q u hx]
  | inr v => rw [if_neg (by simp), jctf_inner_right n r a Q v]

lemma jctf_clique_sum (n r a : ℕ) (Q : Finset (Fin a ⊕ Fin (n - a))) :
    (∑ e ∈ Q.offDiag.image (fun p => s(p.1, p.2)), join_complete_turan_weight n r a e) * 2
      = ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) *
          (((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
            - (2/((r:ℚ)*((r:ℚ)-1)))
            + ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) * (1/((r:ℚ)-1)))
        + ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) *
          (((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) * (1/((r:ℚ)-1))) := by
  classical
  have step : 2 * (∑ e ∈ Q.offDiag.image (fun p => s(p.1, p.2)),
        join_complete_turan_weight n r a e)
      = ∑ x ∈ Q, ∑ y ∈ Q, (if x ≠ y then join_complete_turan_weight n r a s(x, y) else 0) := by
    rw [jctf_image_sum]
    exact jctf_ordered n r a Q
  rw [mul_comm, step]
  rw [Finset.sum_congr rfl (fun x hx => jctf_inner_const n r a Q x hx)]
  rw [Finset.sum_ite]
  rw [jctf_notleft, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

lemma jctf_alg (r j k : ℚ) (hr : 0 < r) (hr1 : 0 < r - 1) (hk0 : 0 ≤ k)
    (hjk : j + k = r) (hj1 : 1 ≤ j) :
    1 ≤ (j * (j * (2/(r*(r-1))) - 2/(r*(r-1)) + k * (1/(r-1))) + k * (j * (1/(r-1)))) / 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hk : k = r - j := by linarith
  have hj1' : (0:ℚ) ≤ j - 1 := by linarith
  have hkj : (0:ℚ) ≤ r - j := by linarith
  have hkey : j * (j * (2/(r*(r-1))) - 2/(r*(r-1)) + (r-j) * (1/(r-1)))
      + (r-j) * (j * (1/(r-1))) = 2 + 2 * ((j-1)*(r-j)/r) := by
    field_simp
    try ring
  rw [hk, hkey]
  have hnn : (0:ℚ) ≤ (j-1)*(r-j)/r := div_nonneg (mul_nonneg hj1' hkj) (le_of_lt hr)
  linarith

lemma jctf_weight_bounds (n r a : ℕ) (hr : 3 ≤ r) :
    ∀ e ∈ (join_complete_turan n r a).edgeSet,
      0 ≤ join_complete_turan_weight n r a e ∧ join_complete_turan_weight n r a e ≤ 1 := by
  intro e he
  have hr3 : (3:ℚ) ≤ (r:ℚ) := by exact_mod_cast hr
  have hr0 : (0:ℚ) < (r:ℚ) := by linarith
  have hr1 : (0:ℚ) < (r:ℚ) - 1 := by linarith
  have hprod : (0:ℚ) < (r:ℚ) * ((r:ℚ) - 1) := mul_pos hr0 hr1
  induction e using Sym2.ind with
  | _ x y =>
    rcases x with u | u <;> rcases y with v | v
    · rw [join_complete_turan_weight]; simp only [Sym2.lift_mk]
      exact ⟨div_nonneg (by norm_num) (le_of_lt hprod),
        by rw [div_le_one hprod]; nlinarith⟩
    · rw [join_complete_turan_weight]; simp only [Sym2.lift_mk]
      exact ⟨div_nonneg (by norm_num) (le_of_lt hr1),
        by rw [div_le_one hr1]; linarith⟩
    · rw [join_complete_turan_weight]; simp only [Sym2.lift_mk]
      exact ⟨div_nonneg (by norm_num) (le_of_lt hr1),
        by rw [div_le_one hr1]; linarith⟩
    · rw [join_complete_turan_weight]; simp only [Sym2.lift_mk]
      exact ⟨le_refl 0, by norm_num⟩

lemma jctf_j_pos (n r a : ℕ) (hr : 3 ≤ r) (Q : Finset (Fin a ⊕ Fin (n - a)))
    (hQ : (join_complete_turan n r a).IsNClique r Q) :
    1 ≤ (Q.filter (fun y => Sum.isLeft y = true)).card := by
  rcases Nat.eq_zero_or_pos (Q.filter (fun y => Sum.isLeft y = true)).card with h | h
  · exfalso
    have hk : (Q.filter (fun y => Sum.isRight y = true)).card = r := by
      have := jctf_card_split n a Q
      have hc : Q.card = r := hQ.card_eq
      omega
    set T := Finset.univ.filter (fun v : Fin (n - a) => Sum.inr v ∈ Q) with hT
    have hmemT : ∀ v, v ∈ T ↔ Sum.inr v ∈ Q := by
      intro v; simp [hT]
    have himg : Q.filter (fun y => Sum.isRight y = true) = T.image Sum.inr := by
      ext y
      constructor
      · intro hy
        obtain ⟨v, hv⟩ := Sum.isRight_iff.mp (Finset.mem_filter.mp hy).2
        have hmem : Sum.inr v ∈ Q := hv ▸ (Finset.mem_filter.mp hy).1
        exact Finset.mem_image.mpr ⟨v, (hmemT v).mpr hmem, hv.symm⟩
      · intro hy
        obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hy
        rw [← hve]
        exact Finset.mem_filter.mpr ⟨(hmemT v).mp hv, Sum.isRight_inr⟩
    have hTcard : T.card = r := by
      rw [← hk, himg, Finset.card_image_of_injective _ Sum.inr_injective]
    have hcf := SimpleGraph.turanGraph_cliqueFree (n := n - a) (r := r - 1)
      (by omega : 0 < r - 1)
    refine hcf T ⟨?_, by omega⟩
    intro x hx y hy hxy
    have hx' : Sum.inr x ∈ Q := (hmemT x).mp hx
    have hy' : Sum.inr y ∈ Q := (hmemT y).mp hy
    exact hQ.isClique hx' hy' (fun hh => hxy (Sum.inr_injective hh))
  · exact h

lemma jctf_edge_fiber (n r a : ℕ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin a ⊕ Fin (n - a)) × (Fin a ⊕ Fin (n - a)))).filter
        (fun p => (join_complete_turan n r a).Adj p.1 p.2),
        join_complete_turan_weight n r a s(p.1, p.2)
      = ∑ e ∈ (join_complete_turan n r a).edgeFinset, 2 * join_complete_turan_weight n r a e := by
  classical
  set F := (Finset.univ : Finset ((Fin a ⊕ Fin (n - a)) × (Fin a ⊕ Fin (n - a)))).filter
    (fun p => (join_complete_turan n r a).Adj p.1 p.2) with hF
  set g : (Fin a ⊕ Fin (n - a)) × (Fin a ⊕ Fin (n - a)) → Sym2 (Fin a ⊕ Fin (n - a)) :=
    fun p => s(p.1, p.2) with hg
  have h1 : ∑ e : Sym2 (Fin a ⊕ Fin (n - a)),
      (∑ p ∈ F.filter (fun p => g p = e), join_complete_turan_weight n r a (g p))
      = ∑ p ∈ F, join_complete_turan_weight n r a (g p) :=
    Finset.sum_fiberwise F g (fun p => join_complete_turan_weight n r a (g p))
  have hfib : ∀ e ∈ (join_complete_turan n r a).edgeFinset,
      (∑ p ∈ F.filter (fun p => g p = e), join_complete_turan_weight n r a (g p))
        = 2 * join_complete_turan_weight n r a e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hab : (join_complete_turan n r a).Adj x y := by
        have h := SimpleGraph.mem_edgeFinset.mp he
        rwa [SimpleGraph.mem_edgeSet] at h
      have hset : F.filter (fun p => g p = s(x, y)) = {(x, y), (y, x)} := by
        ext p
        obtain ⟨p1, p2⟩ := p
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨hpA, hpg⟩
          have hh : s(p1, p2) = s(x, y) := hpg
          rw [Sym2.eq_iff] at hh
          rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨hab, rfl⟩
          · refine ⟨?_, by rw [Sym2.eq_swap]⟩
            exact (SimpleGraph.adj_comm (join_complete_turan n r a) _ _).mpr hab
      rw [hset]
      have hne : (x, y) ≠ (y, x) := by
        intro h; exact (join_complete_turan n r a).ne_of_adj hab (congrArg Prod.fst h)
      rw [Finset.sum_pair hne]
      simp only [hg]
      rw [Sym2.eq_swap]
      ring
  have hzero : ∀ e ∈ (Finset.univ : Finset (Sym2 (Fin a ⊕ Fin (n - a)))),
      e ∉ (join_complete_turan n r a).edgeFinset →
      (∑ p ∈ F.filter (fun p => g p = e), join_complete_turan_weight n r a (g p)) = 0 := by
    intro e _ he
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpF, hpg⟩ := hp
    have hadj : (join_complete_turan n r a).Adj p.1 p.2 := by
      simpa only [hF, Finset.mem_filter, Finset.mem_univ, true_and] using hpF
    have hmem : g p ∈ (join_complete_turan n r a).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      simpa only [hg] using hadj
    rw [hpg] at hmem
    exact absurd hmem he
  have h3 : ∑ e ∈ (join_complete_turan n r a).edgeFinset,
        (∑ p ∈ F.filter (fun p => g p = e), join_complete_turan_weight n r a (g p))
      = ∑ e ∈ (Finset.univ : Finset (Sym2 (Fin a ⊕ Fin (n - a)))),
        (∑ p ∈ F.filter (fun p => g p = e), join_complete_turan_weight n r a (g p)) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro e _ he
    exact hzero e (Finset.mem_univ e) he
  rw [← h1, ← h3, Finset.sum_congr rfl hfib]

lemma jctf_ordered_total (n r a : ℕ) :
    (∑ p ∈ (Finset.univ : Finset ((Fin a ⊕ Fin (n - a)) × (Fin a ⊕ Fin (n - a)))).filter
        (fun p => (join_complete_turan n r a).Adj p.1 p.2),
        join_complete_turan_weight n r a s(p.1, p.2))
    = (a:ℚ) * ((a-1 : ℕ):ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
        + 2 * ((a:ℚ) * ((n-a : ℕ):ℚ) * (1/((r:ℚ)-1))) := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_sum_type]
  have hinl : ∀ u : Fin a,
      (∑ y : Fin a ⊕ Fin (n - a),
        if (join_complete_turan n r a).Adj (Sum.inl u) y
          then join_complete_turan_weight n r a s(Sum.inl u, y) else 0)
      = ((a-1 : ℕ):ℚ) * (2/((r:ℚ)*((r:ℚ)-1))) + ((n-a : ℕ):ℚ) * (1/((r:ℚ)-1)) := by
    intro u
    rw [Fintype.sum_sum_type]
    have h1 : (∑ v : Fin a, if (join_complete_turan n r a).Adj (Sum.inl u) (Sum.inl v)
          then join_complete_turan_weight n r a s(Sum.inl u, Sum.inl v) else 0)
        = ∑ v : Fin a, if u ≠ v then 2/((r:ℚ)*((r:ℚ)-1)) else 0 := by
      apply Finset.sum_congr rfl; intro v _; rfl
    have h2 : (∑ w : Fin (n - a), if (join_complete_turan n r a).Adj (Sum.inl u) (Sum.inr w)
          then join_complete_turan_weight n r a s(Sum.inl u, Sum.inr w) else 0)
        = ∑ w : Fin (n - a), (1/((r:ℚ)-1)) := by
      apply Finset.sum_congr rfl; intro w _
      rw [if_pos (show (join_complete_turan n r a).Adj (Sum.inl u) (Sum.inr w) from trivial)]
      rfl
    rw [h1, h2]
    rw [← Finset.sum_filter (p := fun v => u ≠ v)
      (f := fun _ => (2/((r:ℚ)*((r:ℚ)-1))))]
    rw [Finset.sum_const, Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, nsmul_eq_mul]
  have hinr : ∀ w : Fin (n - a),
      (∑ y : Fin a ⊕ Fin (n - a),
        if (join_complete_turan n r a).Adj (Sum.inr w) y
          then join_complete_turan_weight n r a s(Sum.inr w, y) else 0)
      = (a:ℚ) * (1/((r:ℚ)-1)) := by
    intro w
    rw [Fintype.sum_sum_type]
    have h1 : (∑ v : Fin a, if (join_complete_turan n r a).Adj (Sum.inr w) (Sum.inl v)
          then join_complete_turan_weight n r a s(Sum.inr w, Sum.inl v) else 0)
        = ∑ v : Fin a, (1/((r:ℚ)-1)) := by
      apply Finset.sum_congr rfl; intro v _
      rw [if_pos (show (join_complete_turan n r a).Adj (Sum.inr w) (Sum.inl v) from trivial)]
      rfl
    have h2 : (∑ w' : Fin (n - a), if (join_complete_turan n r a).Adj (Sum.inr w) (Sum.inr w')
          then join_complete_turan_weight n r a s(Sum.inr w, Sum.inr w') else 0)
        = ∑ w' : Fin (n - a), (0:ℚ) := by
      apply Finset.sum_congr rfl; intro w' _
      by_cases h : (join_complete_turan n r a).Adj (Sum.inr w) (Sum.inr w')
      · rw [if_pos h]; rfl
      · rw [if_neg h]
    rw [h1, h2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  rw [Finset.sum_congr rfl (fun u _ => hinl u), Finset.sum_congr rfl (fun w _ => hinr w)]
  rw [Finset.sum_const, Finset.sum_const]
  rw [nsmul_eq_mul, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
  ring

lemma jctf_algebra (n r a : ℕ) (hr : 3 ≤ r) (ha : a ≤ n) :
    ((a:ℚ) * ((a-1:ℕ):ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
        + 2 * ((a:ℚ) * ((n-a:ℕ):ℚ) * (1/((r:ℚ)-1)))) / 2
    = (a * n : ℚ)/(r-1) - (a^2:ℚ)/r - (a:ℚ)/(r*(r-1)) := by
  have hr3 : (3:ℚ) ≤ (r:ℚ) := by exact_mod_cast hr
  have hr0 : (r:ℚ) ≠ 0 := by linarith
  have hr1 : (r:ℚ) - 1 ≠ 0 := by linarith
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0; simp
  · have hca : ((a-1:ℕ):ℚ) = (a:ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ a)]; norm_num
    have hcn : ((n-a:ℕ):ℚ) = (n:ℚ) - (a:ℚ) := by
      rw [Nat.cast_sub ha]
    rw [hca, hcn]
    field_simp
    ring

/-- Lemma 3.2 of arXiv:2610.41371: w_a is a fractional K_r-cover of G_a with total weight an/(r-1) - a^2/r - a/(r(r-1)). -/
theorem join_complete_turan_fractional_cover_and_total_weight (n r a : ℕ)
    (hr : 3 ≤ r) (ha : a ≤ n) :
    is_fractional_clique_cover (join_complete_turan n r a) (join_complete_turan_weight n r a) r ∧
    ∑ e ∈ (join_complete_turan n r a).edgeFinset, join_complete_turan_weight n r a e =
      (a * n : ℚ) / (r - 1) - (a ^ 2 : ℚ) / r - (a : ℚ) / (r * (r - 1)) := by
  refine ⟨⟨jctf_weight_bounds n r a hr, ?_⟩, ?_⟩
  · intro Q hQ
    have hr3 : (3:ℚ) ≤ (r:ℚ) := by exact_mod_cast hr
    have hr0 : (0:ℚ) < (r:ℚ) := by linarith
    have hr1 : (0:ℚ) < (r:ℚ) - 1 := by linarith
    have hsum := jctf_clique_sum n r a Q
    have hcard := jctf_card_split n a Q
    have hQcard : Q.card = r := hQ.card_eq
    have hjk : ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) +
        ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) = (r:ℚ) := by
      have h : (Q.filter (fun y => Sum.isLeft y = true)).card +
          (Q.filter (fun y => Sum.isRight y = true)).card = r := by omega
      exact_mod_cast h
    have hj1 : 1 ≤ ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ) := by
      exact_mod_cast jctf_j_pos n r a hr Q hQ
    have hk0 : (0:ℚ) ≤ ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) :=
      Nat.cast_nonneg _
    have hge := jctf_alg (r:ℚ) ((Q.filter (fun y => Sum.isLeft y = true)).card : ℚ)
      ((Q.filter (fun y => Sum.isRight y = true)).card : ℚ) hr0 hr1 hk0 hjk hj1
    linarith
  · have hfib := jctf_edge_fiber n r a
    have hord := jctf_ordered_total n r a
    have key : 2 * (∑ e ∈ (join_complete_turan n r a).edgeFinset,
        join_complete_turan_weight n r a e)
        = (a:ℚ) * ((a-1 : ℕ):ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
          + 2 * ((a:ℚ) * ((n-a : ℕ):ℚ) * (1/((r:ℚ)-1))) := by
      rw [Finset.mul_sum, ← hfib, hord]
    have hhalf : (∑ e ∈ (join_complete_turan n r a).edgeFinset,
        join_complete_turan_weight n r a e)
        = ((a:ℚ) * ((a-1 : ℕ):ℚ) * (2/((r:ℚ)*((r:ℚ)-1)))
          + 2 * ((a:ℚ) * ((n-a : ℕ):ℚ) * (1/((r:ℚ)-1)))) / 2 := by
      rw [eq_div_iff (by norm_num : (2:ℚ) ≠ 0), mul_comm]
      exact key
    rw [hhalf, jctf_algebra n r a hr ha]
