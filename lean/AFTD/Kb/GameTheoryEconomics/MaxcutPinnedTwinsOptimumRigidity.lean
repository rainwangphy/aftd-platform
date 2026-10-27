import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard

/-!
# maxcut_pinned_twins_optimum_rigidity

Topic: equilibria   Node: da923567e471

Provenance: helper lemma. Rigidity premise of maxcut_pinned_twins_refutes_of_rigidity, towards OP-89 (arXiv:2610.04948, Section 4, Question 2).

Every welfare-maximizing 3-coloring ρ of the 182-vertex pinned twins graph maxcut_pinned_twins_graph is, up to one global permutation p of the three colors, the doubled initial coloring: ρ = fun v => p (maxcut_anchor_three_initial_coloring v.1).
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000

open scoped BigOperators

namespace MaxcutPinnedTwinsRigidity

private abbrev PV := Fin 16 ⊕ (Fin 3 × Fin 25)
private abbrev PW := PV × Fin 2

private instance maxcut_pinned_twins_optimum_rigidity_base_dec : DecidableRel maxcut_anchor_three_graph.Adj := by
  unfold maxcut_anchor_three_graph; infer_instance
private instance maxcut_pinned_twins_optimum_rigidity_pinned_dec : DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph; infer_instance

private lemma lift_adj (a b : PW) (h : maxcut_anchor_three_graph.Adj a.1 b.1) :
    maxcut_pinned_twins_graph.Adj a b := by
  simp only [maxcut_pinned_twins_graph, SimpleGraph.fromRel_adj]
  exact ⟨fun hab => h.ne (congrArg Prod.fst hab), Or.inl (Or.inl h)⟩

private def pin (a b : PW) : Prop :=
  match a.1, b.1 with
  | .inl i, .inr (j, x) => x.val = 24 ∧ b.2.val = 0 ∧
      j ≠ maxcut_anchor_three_initial_coloring (.inl i)
  | _, _ => False

private lemma adj_iff (a b : PW) : maxcut_pinned_twins_graph.Adj a b ↔
    a ≠ b ∧ ((maxcut_anchor_three_graph.Adj a.1 b.1 ∨ pin a b) ∨
      (maxcut_anchor_three_graph.Adj b.1 a.1 ∨ pin b a)) := Iff.rfl

private lemma pin_ne (a b : PW) (h : pin a b) :
    maxcut_anchor_three_initial_coloring b.1 ≠ maxcut_anchor_three_initial_coloring a.1 := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  cases a1 with
  | inl i =>
    cases b1 with
    | inl i' => exact h.elim
    | inr jx =>
      obtain ⟨j, x⟩ := jx
      exact h.2.2
  | inr jx => exact h.elim

private lemma pin_adj : ∀ (u : Fin 16) (s : Fin 2) (j : Fin 3),
    j ≠ maxcut_anchor_three_initial_coloring (.inl u) →
    maxcut_pinned_twins_graph.Adj (.inl u, s) (.inr (j, 24), 0) ∧
    ¬ maxcut_anchor_three_graph.Adj (.inl u) (.inr (j, 24)) := by
  decide

private def mono {X : Type} [Fintype X] (H : SimpleGraph X) [DecidableRel H.Adj] (ρ : X → Fin 3) : ℕ :=
  ∑ v, (Finset.univ.filter fun w => H.Adj v w ∧ ρ w = ρ v).card

private lemma mono_sum {X : Type} [Fintype X] (H : SimpleGraph X) [DecidableRel H.Adj] (ρ : X → Fin 3) :
    mono H ρ = ∑ v, ∑ w, if H.Adj v w ∧ ρ w = ρ v then 1 else 0 := by
  simp only [mono, Finset.card_filter]

private lemma welfare_add_mono {X : Type} [Fintype X] (H : SimpleGraph X) [DecidableRel H.Adj]
    (ρ : X → Fin 3) : maxcut_welfare H ρ + mono H ρ = ∑ v, H.degree v := by
  rw [maxcut_welfare, mono, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => maxcut_utility_add_monochromatic_card H ρ v

private lemma mono_le_of_optimal {X : Type} [Fintype X] (H : SimpleGraph X) [DecidableRel H.Adj]
    (ρ τ : X → Fin 3) (h : is_maxcut_optimal H ρ) : mono H ρ ≤ mono H τ := by
  have h1 := h τ
  have h2 := welfare_add_mono H ρ
  have h3 := welfare_add_mono H τ
  omega

private lemma independent_mono_bound {X : Type} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (ρ : X → Fin 3)
    (S : Finset X) (hind : ∀ v ∈ S, ∀ w ∈ S, ¬ H.Adj v w) :
    2 * (∑ v ∈ S, (Finset.univ.filter fun w => H.Adj v w ∧ ρ w = ρ v).card)
      ≤ mono H ρ := by
  classical
  let f : X → X → ℕ := fun v w => if H.Adj v w ∧ ρ w = ρ v then 1 else 0
  have hsym (v w : X) : f v w = f w v := by
    dsimp [f]
    congr 1
    exact propext ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hzero : ∑ v ∈ S, ∑ w ∈ S, f v w = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    simp [f, hind v hv w hw]
  have hcross : ∑ v ∈ Sᶜ, ∑ w ∈ S, f v w = ∑ v ∈ S, ∑ w ∈ Sᶜ, f v w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => hsym w v
  have hsplit (v : X) : ∑ w, f v w = ∑ w ∈ S, f v w + ∑ w ∈ Sᶜ, f v w :=
    (Finset.sum_add_sum_compl S _).symm
  have hall : mono H ρ =
      2 * (∑ v ∈ S, ∑ w ∈ Sᶜ, f v w) + ∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, f v w := by
    rw [mono_sum]
    change (∑ v, ∑ w, f v w) = _
    rw [← Finset.sum_add_sum_compl S]
    simp only [hsplit, Finset.sum_add_distrib, hzero, hcross]
    omega
  have hpart : (∑ v ∈ S, (Finset.univ.filter fun w => H.Adj v w ∧ ρ w = ρ v).card) =
      ∑ v ∈ S, ∑ w ∈ Sᶜ, f v w := by
    simp only [Finset.card_filter]
    change (∑ v ∈ S, ∑ w, f v w) = _
    simp only [hsplit, Finset.sum_add_distrib, hzero, zero_add]
  rw [hpart, hall]
  omega

private lemma exists_good_of_independent {X : Type} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (ρ : X → Fin 3)
    (S : Finset X) (hind : ∀ v ∈ S, ∀ w ∈ S, ¬ H.Adj v w)
    (hsmall : mono H ρ < 2 * S.card) :
    ∃ v ∈ S, ∀ w, H.Adj v w → ρ w ≠ ρ v := by
  classical
  by_contra h
  push Not at h
  have hpos : ∀ v ∈ S, 1 ≤ (Finset.univ.filter fun w => H.Adj v w ∧ ρ w = ρ v).card := by
    intro v hv
    obtain ⟨w, hadj, hc⟩ := h v hv
    exact Finset.card_pos.mpr ⟨w, by simp [hadj, hc]⟩
  have hsum := Finset.sum_le_sum hpos
  have hb := independent_mono_bound H ρ S hind
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega

private lemma anchor_adj (j l : Fin 3) (i t : Fin 25) :
    maxcut_anchor_three_graph.Adj (.inr (j,i)) (.inr (l,t)) ↔ j ≠ l := by
  change ((Sum.inr (j,i) : PV) ≠ Sum.inr (l,t) ∧ (j ≠ l ∨ l ≠ j)) ↔ j ≠ l
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    exact h (congrArg Prod.fst (Sum.inr.inj heq))

private lemma mono_sigma :
    mono maxcut_anchor_three_graph maxcut_anchor_three_initial_coloring = 48 := by
  decide

private lemma mono_G_ge (ρ : PV → Fin 3) : 48 ≤ mono maxcut_anchor_three_graph ρ := by
  have h := mono_le_of_optimal maxcut_anchor_three_graph maxcut_anchor_three_initial_coloring ρ
    maxcut_anchor_three_initial_optimal
  rw [mono_sigma] at h
  exact h

private lemma anchor_rigidity (ρ : PV → Fin 3) (hsmall : mono maxcut_anchor_three_graph ρ < 50) :
    ∃ p : Equiv.Perm (Fin 3), ∀ j i, ρ (.inr (j,i)) = p j := by
  classical
  have hgood : ∀ j : Fin 3, ∃ i : Fin 25,
      ∀ w, maxcut_anchor_three_graph.Adj (.inr (j,i)) w → ρ w ≠ ρ (.inr (j,i)) := by
    intro j
    let S : Finset PV := Finset.univ.image fun i : Fin 25 => Sum.inr (j,i)
    have hcard : S.card = 25 := by
      rw [Finset.card_image_of_injective _ (by intro a b h; simpa using h)]
      decide
    have hind : ∀ v ∈ S, ∀ w ∈ S, ¬ maxcut_anchor_three_graph.Adj v w := by
      intro v hv w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      simp [anchor_adj]
    obtain ⟨v, hv, hg⟩ := exists_good_of_independent maxcut_anchor_three_graph ρ S hind
      (by omega)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i, hg⟩
  choose gi hg using hgood
  let c : Fin 3 → Fin 3 := fun j => ρ (.inr (j, gi j))
  have hi : Function.Injective c := by
    intro j l heq
    by_contra hne
    exact hg j (.inr (l, gi l)) ((anchor_adj j l _ _).2 hne) heq.symm
  have hb : Function.Bijective c := (Fintype.bijective_iff_injective_and_card c).2 ⟨hi, rfl⟩
  refine ⟨Equiv.ofBijective c hb, ?_⟩
  intro j i
  obtain ⟨l, hl⟩ := hb.2 (ρ (.inr (j,i)))
  have heq : l = j := by
    by_contra hne
    exact hg l (.inr (j,i)) ((anchor_adj l j _ _).2 hne) hl.symm
  subst l
  exact hl.symm

/-- Monochromatic ordered pairs of the twin graph that come from edges of `G_3`. -/
private def twinBase (ρ : PW → Fin 3) : ℕ :=
  ∑ a : PW, ∑ b : PW, if maxcut_anchor_three_graph.Adj a.1 b.1 ∧ ρ b = ρ a then 1 else 0

private lemma base_split (ρ : PW → Fin 3) : twinBase ρ = ∑ v : PV, ∑ w : PV, ∑ s : Fin 2, ∑ t : Fin 2,
    if maxcut_anchor_three_graph.Adj v w ∧ ρ (w, t) = ρ (v, s) then 1 else 0 := by
  unfold twinBase
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_comm

private lemma ind_le (ρ : PW → Fin 3) (a b : PW) :
    (if maxcut_anchor_three_graph.Adj a.1 b.1 ∧ ρ b = ρ a then 1 else 0) ≤
      (if maxcut_pinned_twins_graph.Adj a b ∧ ρ b = ρ a then 1 else 0) := by
  by_cases h : maxcut_anchor_three_graph.Adj a.1 b.1 ∧ ρ b = ρ a
  · rw [if_pos h, if_pos ⟨lift_adj a b h.1, h.2⟩]
  · rw [if_neg h]
    exact Nat.zero_le _

private lemma base_le_mono (ρ : PW → Fin 3) : twinBase ρ ≤ mono maxcut_pinned_twins_graph ρ := by
  rw [mono_sum]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ind_le ρ a b

private lemma base_lt_mono (ρ : PW → Fin 3) (u : Fin 16) (s : Fin 2) (j : Fin 3)
    (hj : j ≠ maxcut_anchor_three_initial_coloring (.inl u))
    (heq : ρ (.inr (j, 24), 0) = ρ (.inl u, s)) :
    twinBase ρ < mono maxcut_pinned_twins_graph ρ := by
  rw [mono_sum]
  apply Finset.sum_lt_sum
  · exact fun a _ => Finset.sum_le_sum fun b _ => ind_le ρ a b
  · refine ⟨(.inl u, s), Finset.mem_univ _, ?_⟩
    apply Finset.sum_lt_sum
    · exact fun b _ => ind_le ρ _ b
    · refine ⟨(.inr (j, 24), 0), Finset.mem_univ _, ?_⟩
      obtain ⟨hadj, hnot⟩ := pin_adj u s j hj
      rw [if_neg (fun h => hnot h.1), if_pos ⟨hadj, heq⟩]
      exact Nat.zero_lt_one

private lemma mono_sigma' :
    mono maxcut_pinned_twins_graph (fun v => maxcut_anchor_three_initial_coloring v.1) = 192 := by
  have hpt : ∀ a b : PW,
      (if maxcut_pinned_twins_graph.Adj a b ∧ maxcut_anchor_three_initial_coloring b.1 =
          maxcut_anchor_three_initial_coloring a.1 then 1 else 0) =
      (if maxcut_anchor_three_graph.Adj a.1 b.1 ∧ maxcut_anchor_three_initial_coloring b.1 =
          maxcut_anchor_three_initial_coloring a.1 then 1 else 0) := by
    intro a b
    congr 1
    apply propext
    constructor
    · rintro ⟨hadj, hc⟩
      refine ⟨?_, hc⟩
      rcases (adj_iff a b).1 hadj with ⟨_, (h | h) | (h | h)⟩
      · exact h
      · exact absurd hc (pin_ne a b h)
      · exact h.symm
      · exact absurd hc.symm (pin_ne b a h)
    · rintro ⟨hadj, hc⟩
      exact ⟨lift_adj a b hadj, hc⟩
  rw [mono_sum]
  simp only [hpt]
  change twinBase (fun v => maxcut_anchor_three_initial_coloring v.1) = 192
  rw [base_split]
  have h48 := mono_sigma
  rw [mono_sum] at h48
  rw [show (192 : ℕ) = 4 * 48 from rfl, ← h48, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Fin.sum_univ_two]
  ring

private def slice (ρ : PW → Fin 3) (c : PV → Fin 2) : PV → Fin 3 := fun v => ρ (v, c v)

private lemma pair_avg {X : Type} [Fintype X] [DecidableEq X] (v w : X) (hvw : v ≠ w)
    (Fv : Fin 2 → Fin 2 → ℕ) :
    4 * ∑ c : X → Fin 2, Fv (c v) (c w) = Fintype.card (X → Fin 2) * ∑ s, ∑ t, Fv s t := by
  have hz : ∀ z a : Fin 2, z + a + a = z := by decide
  have key : ∀ a b : Fin 2, ∑ c : X → Fin 2, Fv (c v + a) (c w + b) =
      ∑ c : X → Fin 2, Fv (c v) (c w) := by
    intro a b
    let e : (X → Fin 2) → (X → Fin 2) := fun c x =>
      if x = v then c x + a else if x = w then c x + b else c x
    have he : Function.Involutive e := by
      intro c
      funext x
      simp only [e]
      by_cases h1 : x = v
      · simp [h1, hz]
      · by_cases h2 : x = w
        · simp [h2, Ne.symm hvw, hz]
        · simp [h1, h2]
    have hev : ∀ c, e c v = c v + a := by intro c; simp [e]
    have hew : ∀ c, e c w = c w + b := by intro c; simp [e, Ne.symm hvw]
    calc ∑ c : X → Fin 2, Fv (c v + a) (c w + b)
        = ∑ c : X → Fin 2, (fun d : X → Fin 2 => Fv (d v) (d w))
            (Function.Involutive.toPerm e he c) := by
          apply Finset.sum_congr rfl
          intro c _
          simp only [Function.Involutive.coe_toPerm, hev, hew]
      _ = ∑ c : X → Fin 2, Fv (c v) (c w) := Equiv.sum_comp (Function.Involutive.toPerm e he) (fun d : X → Fin 2 => Fv (d v) (d w))
  have hinner : ∀ c : X → Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, Fv (c v + a) (c w + b) =
      ∑ s, ∑ t, Fv s t := by
    intro c
    have h1 := Equiv.sum_comp (Equiv.addLeft (c v)) (fun s => ∑ t, Fv s t)
    rw [← h1]
    apply Finset.sum_congr rfl
    intro a _
    exact (Equiv.sum_comp (Equiv.addLeft (c w)) (fun t => Fv (c v + a) t))
  calc 4 * ∑ c : X → Fin 2, Fv (c v) (c w)
      = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : X → Fin 2, Fv (c v + a) (c w + b) := by
        simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring
    _ = ∑ a : Fin 2, ∑ c : X → Fin 2, ∑ b : Fin 2, Fv (c v + a) (c w + b) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c : X → Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, Fv (c v + a) (c w + b) := Finset.sum_comm
    _ = ∑ c : X → Fin 2, ∑ s, ∑ t, Fv s t := Finset.sum_congr rfl (fun c _ => hinner c)
    _ = Fintype.card (X → Fin 2) * ∑ s, ∑ t, Fv s t := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]

private lemma avg (ρ : PW → Fin 3) :
    4 * ∑ c : PV → Fin 2, mono maxcut_anchor_three_graph (slice ρ c) =
      Fintype.card (PV → Fin 2) * twinBase ρ := by
  simp only [mono_sum, slice]
  rw [base_split]
  have hswap : ∀ I : (PV → Fin 2) → PV → PV → ℕ,
      ∑ c, ∑ v, ∑ w, I c v w = ∑ v, ∑ w, ∑ c, I c v w := by
    intro I
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_comm
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hvw : maxcut_anchor_three_graph.Adj v w
  · simp only [hvw, true_and]
    exact pair_avg v w hvw.ne (fun s t => if ρ (w, t) = ρ (v, s) then 1 else 0)
  · simp [hvw]

private theorem rigidity (ρ : PW → Fin 3) (hopt : is_maxcut_optimal maxcut_pinned_twins_graph ρ) :
    ∃ p : Equiv.Perm (Fin 3), ρ = fun v => p (maxcut_anchor_three_initial_coloring v.1) := by
  classical
  have hMpos : 0 < Fintype.card (PV → Fin 2) := Fintype.card_pos
  have hup : mono maxcut_pinned_twins_graph ρ ≤ 192 := by
    have h := mono_le_of_optimal maxcut_pinned_twins_graph ρ
      (fun v => maxcut_anchor_three_initial_coloring v.1) hopt
    rw [mono_sigma'] at h
    exact h
  have havg := avg ρ
  have hge : Fintype.card (PV → Fin 2) * 48 ≤
      ∑ c : PV → Fin 2, mono maxcut_anchor_three_graph (slice ρ c) := by
    have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (PV → Fin 2))) =>
      mono_G_ge (slice ρ c))
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using h
  have hbase_ge : 192 ≤ twinBase ρ := by
    by_contra h
    push Not at h
    have h2 : Fintype.card (PV → Fin 2) * twinBase ρ < Fintype.card (PV → Fin 2) * 192 :=
      Nat.mul_lt_mul_of_pos_left h hMpos
    generalize Fintype.card (PV → Fin 2) * twinBase ρ = q at havg h2
    omega
  have hall : ∀ c, mono maxcut_anchor_three_graph (slice ρ c) ≤ 48 := by
    intro c
    by_contra h
    push Not at h
    have hlt : Fintype.card (PV → Fin 2) * 48 <
        ∑ c : PV → Fin 2, mono maxcut_anchor_three_graph (slice ρ c) := by
      have h' := Finset.sum_lt_sum
        (fun c' (_ : c' ∈ (Finset.univ : Finset (PV → Fin 2))) => mono_G_ge (slice ρ c'))
        ⟨c, Finset.mem_univ _, h⟩
      simpa [Finset.sum_const, Finset.card_univ, mul_comm] using h'
    have hb := base_le_mono ρ
    have h3 : Fintype.card (PV → Fin 2) * twinBase ρ ≤ Fintype.card (PV → Fin 2) * 192 :=
      Nat.mul_le_mul_left _ (hb.trans hup)
    generalize Fintype.card (PV → Fin 2) * twinBase ρ = q at havg h3
    omega
  have hnopin : ∀ (u : Fin 16) (s : Fin 2) (j : Fin 3),
      j ≠ maxcut_anchor_three_initial_coloring (.inl u) →
      ρ (.inr (j, 24), 0) ≠ ρ (.inl u, s) := by
    intro u s j hj heq
    have h := base_lt_mono ρ u s j hj heq
    omega
  have hanc : ∀ c : PV → Fin 2, ∃ p : Equiv.Perm (Fin 3),
      ∀ j i, ρ (.inr (j, i), c (.inr (j, i))) = p j := by
    intro c
    exact anchor_rigidity (slice ρ c) (by have := hall c; omega)
  obtain ⟨p, hp⟩ := hanc (fun _ => 0)
  have hA : ∀ (j : Fin 3) (i : Fin 25) (s : Fin 2), ρ (.inr (j, i), s) = p j := by
    intro j i s
    obtain ⟨q, hq⟩ := hanc (Function.update (fun _ => 0) (.inr (j, i)) s)
    let i' : Fin 25 := if i.val = 0 then 1 else 0
    have hi' : (Sum.inr (j, i') : PV) ≠ Sum.inr (j, i) := by
      intro h
      have h' : i' = i := (Prod.mk.inj (Sum.inr.inj h)).2
      have hv := congrArg Fin.val h'
      simp only [i'] at hv
      split_ifs at hv with h0 <;> simp at hv <;> omega
    have h1 := hq j i
    have h2 := hq j i'
    have h3 := hp j i'
    rw [Function.update_self] at h1
    rw [Function.update_of_ne hi'] at h2
    exact h1.trans (h2.symm.trans h3)
  have hC : ∀ (u : Fin 16) (s : Fin 2),
      ρ (.inl u, s) = p (maxcut_anchor_three_initial_coloring (.inl u)) := by
    intro u s
    by_contra hne
    have hc : p (p.symm (ρ (.inl u, s))) = ρ (.inl u, s) := p.apply_symm_apply _
    have hcj : p.symm (ρ (.inl u, s)) ≠ maxcut_anchor_three_initial_coloring (.inl u) := by
      intro h
      apply hne
      rw [← hc, h]
    exact hnopin u s _ hcj (by rw [hA _ 24 0, hc])
  refine ⟨p, ?_⟩
  funext x
  rcases x with ⟨v, s⟩
  cases v with
  | inl u => exact hC u s
  | inr ji =>
    obtain ⟨j, i⟩ := ji
    exact hA j i s

end MaxcutPinnedTwinsRigidity

theorem maxcut_pinned_twins_optimum_rigidity :
    ∀ ρ : ((Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) → Fin 3,
      is_maxcut_optimal maxcut_pinned_twins_graph ρ →
      ∃ p : Equiv.Perm (Fin 3),
        ρ = fun v => p (maxcut_anchor_three_initial_coloring v.1) := MaxcutPinnedTwinsRigidity.rigidity
