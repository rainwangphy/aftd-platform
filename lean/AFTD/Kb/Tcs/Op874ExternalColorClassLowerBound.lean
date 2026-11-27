import AFTD.Prelude
import AFTD.Kb.Tcs.Op874MissingColorInducedEdgesLeVertices
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_external_color_class_lower_bound

Topic: graphs   Node: a65a6826075f

Provenance: helper lemma. Local-state criterion for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

For every color in a strong six-color truncation state on a finite loopless cubic multigraph, at least one sixth of the base vertices' number of external edges have that color. The bound is attained in small simple bridgeless examples.
-/

theorem op874_external_color_class_lower_bound
    {V E Ω : Type*} [Fintype V] [Fintype E] [Fintype Ω]
    [DecidableEq V] [DecidableEq E] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 6)
    (ends : E → Sym2 V) (left right : E → V)
    (hends : ∀ e, ends e = s(left e,right e))
    (hloop : ∀ e, left e ≠ right e)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hcons : ∀ e, c (left e) e = c (right e) e)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (a : Ω) :
    Fintype.card V ≤ 6 * (Finset.univ.filter (fun e : E => c (left e) e = a)).card := by
  open Finset in
  let M := univ.filter (fun e : E => c (left e) e = a)
  let R := M.biUnion (fun e => {left e, right e})
  let S := univ \ R
  let ES := univ.filter (fun e => left e ∈ S ∧ right e ∈ S)
  let ER := univ.filter (fun e => left e ∈ R ∧ right e ∈ R)

  have hR : R.card = 2 * M.card := by
    rw [card_biUnion]
    · have : (∑ u ∈ M, ({left u, right u} : Finset V).card) = ∑ u ∈ M, 2 := by
        refine sum_congr rfl (fun e he => ?_)
        rw [card_pair (hloop e)]
      rw [this, sum_const, smul_eq_mul, mul_comm]
    · intro e1 he1 e2 he2 hne
      dsimp [Function.onFun]
      rw [mem_coe, mem_filter] at he1 he2
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [mem_insert, mem_singleton] at hv1 hv2
      have h1 : v ∈ ends e1 := by rw [hends]; rcases hv1 with rfl | rfl <;> simp
      have h2 : v ∈ ends e2 := by rw [hends]; rcases hv2 with rfl | rfl <;> simp
      have hc1 : c v e1 = a := by
        rcases hv1 with rfl | rfl
        · exact he1.2
        · rw [← hcons e1]; exact he1.2
      have hc2 : c v e2 = a := by
        rcases hv2 with rfl | rfl
        · exact he2.2
        · rw [← hcons e2]; exact he2.2
      have heq : e1 = e2 := hc v e1 e2 h1 h2 (hc1.trans hc2.symm)
      exact hne heq

  have hMER : M.card ≤ ER.card := by
    apply card_le_card
    intro e he
    rw [mem_filter]
    refine ⟨mem_univ e, ?_, ?_⟩
    · rw [mem_biUnion]
      exact ⟨e, he, by simp⟩
    · rw [mem_biUnion]
      exact ⟨e, he, by simp⟩

  have hES_le : ES.card ≤ S.card := by
    have hloop' : ∀ e, ¬ (ends e).IsDiag := by
      intro e; rw [hends, Sym2.mk_isDiag_iff]; exact hloop e
    have hends' : ∀ e ∈ ES, ∃ u ∈ S, ∃ v ∈ S, ends e = s(u, v) := by
      intro e he
      rw [mem_filter] at he
      exact ⟨left e, he.2.1, right e, he.2.2, hends e⟩
    have hmiss : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a := by
      intro v hv e hve hca
      rw [mem_sdiff, mem_biUnion] at hv
      apply hv.2
      refine ⟨e, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ e, ?_⟩
        rw [hends e, Sym2.mem_iff] at hve
        rcases hve with rfl | rfl
        · exact hca
        · rw [hcons]; exact hca
      · rw [hends e, Sym2.mem_iff] at hve
        rcases hve with rfl | rfl <;> simp
    exact op874_missing_color_induced_edges_le_vertices hΩ ends hloop' hcubic c h hc hh hch hs S ES a hends' hmiss

  have hsum_deg : ∀ A : Finset V,
      (∑ e ∈ univ, ((if left e ∈ A then 1 else 0) + (if right e ∈ A then 1 else 0))) = 3 * A.card := by
    intro A
    have hcubic' : ∀ v, (univ.filter (fun e : E => v ∈ ends e)).card = 3 := by
      intro v
      have hv := hcubic v
      have h : {e : E | v ∈ ends e} = (univ.filter (fun e : E => v ∈ ends e) : Set E) := by ext e; simp
      rw [h, Set.ncard_coe_finset] at hv
      exact hv
    have hinner : ∀ e : E, ((if left e ∈ A then 1 else 0) + (if right e ∈ A then 1 else 0)) =
        ∑ v ∈ univ, if v ∈ A ∧ v ∈ ends e then 1 else 0 := by
      intro e
      have hmem : ∀ v, v ∈ ends e ↔ v = left e ∨ v = right e := by
        intro v; rw [hends e, Sym2.mem_iff]
      have : (fun v => (if v ∈ A ∧ v ∈ ends e then 1 else 0)) =
             (fun v => (if v = left e then (if left e ∈ A then 1 else 0) else 0) +
                       (if v = right e then (if right e ∈ A then 1 else 0) else 0)) := by
        ext v
        by_cases hvl : v = left e
        · subst hvl
          have hne : left e ≠ right e := hloop e
          simp [hne, (hmem (left e)).2 (Or.inl rfl)]
        · by_cases hvr : v = right e
          · subst hvr
            simp [hvl, (hmem (right e)).2 (Or.inr rfl)]
          · have : ¬ (v ∈ ends e) := by intro h; rw [hmem] at h; rcases h with rfl | rfl <;> contradiction
            simp [hvl, hvr, this]
      rw [this, sum_add_distrib]
      simp
    simp_rw [hinner]
    rw [sum_comm]
    have hswap : ∀ v ∈ univ, (∑ x ∈ univ, if v ∈ A ∧ v ∈ ends x then 1 else 0) = if v ∈ A then 3 else 0 := by
      intro v hv
      split_ifs with hvA
      · have : (∑ x ∈ univ, if v ∈ A ∧ v ∈ ends x then 1 else 0) =
               (∑ x ∈ univ, if v ∈ ends x then 1 else 0) := by
          refine sum_congr rfl (fun x hx => by simp [hvA])
        rw [this, ← card_filter, hcubic' v]
      · have : (∑ x ∈ univ, if v ∈ A ∧ v ∈ ends x then 1 else 0) = 0 := by
          have : (fun x => if v ∈ A ∧ v ∈ ends x then 1 else 0) = fun _ => 0 := by
            ext x; simp [hvA]
          rw [this, sum_const_zero]
        exact this
    rw [sum_congr rfl hswap]
    rw [sum_ite]
    simp [mul_comm]

  have hdeg : 3 * S.card + 2 * ER.card = 3 * R.card + 2 * ES.card := by
    have hSR : ∀ v, v ∈ S ↔ v ∉ R := by
      intro v; simp [S]
    have hpt : ∀ e : E,
        ((if left e ∈ S then 1 else 0) + (if right e ∈ S then 1 else 0) + 2 * (if left e ∈ R ∧ right e ∈ R then 1 else 0)) =
        ((if left e ∈ R then 1 else 0) + (if right e ∈ R then 1 else 0) + 2 * (if left e ∈ S ∧ right e ∈ S then 1 else 0)) := by
      intro e
      have h1 := hSR (left e)
      have h2 := hSR (right e)
      by_cases hr1 : left e ∈ R <;> by_cases hr2 : right e ∈ R
      · have hs1 : ¬ left e ∈ S := by intro h; rw [h1] at h; contradiction
        have hs2 : ¬ right e ∈ S := by intro h; rw [h2] at h; contradiction
        simp [hr1, hr2, hs1, hs2]
      · have hs1 : ¬ left e ∈ S := by intro h; rw [h1] at h; contradiction
        have hs2 : right e ∈ S := by rwa [h2]
        simp [hr1, hr2, hs1, hs2]
      · have hs1 : left e ∈ S := by rwa [h1]
        have hs2 : ¬ right e ∈ S := by intro h; rw [h2] at h; contradiction
        simp [hr1, hr2, hs1, hs2]
      · have hs1 : left e ∈ S := by rwa [h1]
        have hs2 : right e ∈ S := by rwa [h2]
        simp [hr1, hr2, hs1, hs2]
    have hsum : (∑ e ∈ univ, (((if left e ∈ S then 1 else 0) + (if right e ∈ S then 1 else 0)) + 2 * (if left e ∈ R ∧ right e ∈ R then 1 else 0))) =
                (∑ e ∈ univ, (((if left e ∈ R then 1 else 0) + (if right e ∈ R then 1 else 0)) + 2 * (if left e ∈ S ∧ right e ∈ S then 1 else 0))) :=
      sum_congr rfl (fun e _ => hpt e)
    have hL : (∑ e ∈ univ, (((if left e ∈ S then 1 else 0) + (if right e ∈ S then 1 else 0)) + 2 * (if left e ∈ R ∧ right e ∈ R then 1 else 0))) =
              (∑ e ∈ univ, ((if left e ∈ S then 1 else 0) + (if right e ∈ S then 1 else 0))) + 2 * ER.card := by
      rw [sum_add_distrib, ← mul_sum, ← card_filter]
    have hR' : (∑ e ∈ univ, (((if left e ∈ R then 1 else 0) + (if right e ∈ R then 1 else 0)) + 2 * (if left e ∈ S ∧ right e ∈ S then 1 else 0))) =
               (∑ e ∈ univ, ((if left e ∈ R then 1 else 0) + (if right e ∈ R then 1 else 0))) + 2 * ES.card := by
      rw [sum_add_distrib, ← mul_sum, ← card_filter]
    have hcomb := hL.symm.trans (hsum.trans hR')
    rw [hsum_deg S, hsum_deg R] at hcomb
    exact hcomb

  have hV : Fintype.card V = S.card + R.card := by
    rw [← card_univ]
    have : S = univ \ R := rfl
    rw [this, card_sdiff_add_card_eq_card (subset_univ R)]

  change Fintype.card V ≤ 6 * M.card
  omega
