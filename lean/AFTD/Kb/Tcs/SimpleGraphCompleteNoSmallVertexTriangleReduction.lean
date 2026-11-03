import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_complete_no_small_vertex_triangle_reduction

Topic: graphs   Node: 26fe082b2cb6

Provenance: helper lemma. Related work: arXiv:2610.15269, Definition 2.1 and Lemma 2.2, and its conclusion on nonuniform reductions. This quantitative obstruction is a counting argument for that criterion.

In a complete graph, a nonempty vertex set of size at most one forty-first of the order cannot satisfy the standard vertex packing-cover reduction criterion, even if the packing is allowed to use triangles completely outside the set. Thus there is no universal constant bound on the number of vertices required in that reduction framework.
-/

open Finset in
theorem complete_triangle_reduction_P_le (n : ℕ) (X : Finset (Sym2 (Fin n))) (P : Finset (Fin n × Fin n))
    (hP : ∀ p ∈ P, s(p.1, p.2) ∈ X) : P.card ≤ 2 * X.card := by
  classical
  have h := Finset.card_le_mul_card_image (f := fun p : Fin n × Fin n => s(p.1, p.2)) P 2 ?_
  · have hs : P.image (fun p => s(p.1, p.2)) ⊆ X := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact hP p hp
    have := Finset.card_le_card hs
    omega
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hsub : P.filter (fun x => s(x.1, x.2) = s(p.1, p.2)) ⊆ {(p.1, p.2), (p.2, p.1)} := by
      intro x hx
      have hx2 := (Finset.mem_filter.mp hx).2
      rcases Sym2.eq_iff.mp hx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, h1, h2]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

theorem complete_triangle_reduction_offDiag_sum (n : ℕ) (S : Finset (Finset (Fin n)))
    (h3 : ∀ s ∈ S, s.card = 3)
    (hdis : (S : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1)) :
    6 * S.card = (S.biUnion (fun s => s.offDiag)).card := by
  classical
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun s hs => by rw [Finset.offDiag_card, h3 s hs])]
    simp [mul_comm]
  · intro s hs t ht hst
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_offDiag] at hp hq
    have hsub : ({p.1, p.2} : Finset (Fin n)) ⊆ s ∩ t := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp_all
    have h2 : ({p.1, p.2} : Finset (Fin n)).card = 2 := Finset.card_pair hp.2.2
    have := Finset.card_le_card hsub
    have := hdis hs ht hst
    omega

theorem complete_triangle_reduction_cover (n : ℕ) (U : Finset (Fin n)) (X : Finset (Sym2 (Fin n)))
    (hX : ∀ e ∈ X, e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hcov : ∀ t : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique 3 t → (t ∩ U).Nonempty →
      ∃ e ∈ X, ∀ v ∈ e, v ∈ t)
    (u : Fin n) (hu : u ∈ U) :
    ((Finset.univ.filter (fun w => w ∉ U ∧ s(u, w) ∉ X))).offDiag ⊆
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n =>
        p.1 ∉ U ∧ p.2 ∉ U ∧ s(p.1, p.2) ∈ X) := by
  classical
  intro p hp
  simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨⟨ha, hua⟩, ⟨hb, hub⟩, hab⟩ := hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  refine ⟨ha, hb, ?_⟩
  have hau : u ≠ p.1 := fun h => ha (h ▸ hu)
  have hbu : u ≠ p.2 := fun h => hb (h ▸ hu)
  have hcl : (⊤ : SimpleGraph (Fin n)).IsNClique 3 {u, p.1, p.2} := by
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simpa using hxy
    · rw [Finset.card_insert_of_notMem (by simp [hau, hbu]), Finset.card_pair hab]
  have hne : (({u, p.1, p.2} : Finset (Fin n)) ∩ U).Nonempty := ⟨u, by simp [hu]⟩
  obtain ⟨e, heX, hev⟩ := hcov _ hcl hne
  have hee := hX e heX
  induction e using Sym2.ind with
  | h x y =>
    have hx := hev x (Sym2.mem_mk_left x y)
    have hy := hev y (Sym2.mem_mk_right x y)
    have hxy : x ≠ y := by simpa using hee
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy
      | exact heX
      | exact absurd heX hua
      | exact absurd heX hub
      | (rw [Sym2.eq_swap] at heX; first | exact heX | exact absurd heX hua | exact absurd heX hub)

theorem simple_graph_complete_no_small_vertex_triangle_reduction (n : ℕ) (U : Finset (Fin n)) (hU : 0 < U.card) (hsize : 41 * U.card ≤ n) : ¬ ∃ (S : Finset (Finset (Fin n))) (X : Finset (Sym2 (Fin n))), (∀ s ∈ S, (⊤ : SimpleGraph (Fin n)).IsNClique 3 s) ∧ (S : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ (∀ e ∈ X, e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet) ∧ (∀ t : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique 3 t → (t ∩ U).Nonempty → ∃ e ∈ X, ∀ v ∈ e, v ∈ t) ∧ (∀ s ∈ S, ∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, (∀ v ∈ e, v ∈ s) → (∀ u ∈ U, u ∉ e) → e ∈ X) ∧ X.card ≤ 2 * S.card := by
  classical
  rintro ⟨S, X, hS3, hSdis, hXe, hcov, hforce, hXS⟩
  set k := U.card with hk
  set W : Finset (Fin n) := Finset.univ.filter (fun w => w ∉ U) with hWdef
  have hWc : W.card = n - k := by
    have : W = Finset.univ \ U := by ext w; simp [W]
    rw [this, Finset.card_univ_sdiff, Fintype.card_fin]
  set m := n - k with hm
  have hS3' : ∀ s ∈ S, s.card = 3 := fun s hs => (hS3 s hs).card_eq
  -- ordered pairs
  set P0 := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => s(p.1, p.2) ∈ X)
  set PWW := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n =>
        p.1 ∉ U ∧ p.2 ∉ U ∧ s(p.1, p.2) ∈ X) with hPWW
  set PUW := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n =>
        p.1 ∈ U ∧ p.2 ∉ U ∧ s(p.1, p.2) ∈ X)
  set PWU := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n =>
        p.1 ∉ U ∧ p.2 ∈ U ∧ s(p.1, p.2) ∈ X)
  have hP0 : P0.card ≤ 2 * X.card :=
    complete_triangle_reduction_P_le n X P0 (fun p hp => (Finset.mem_filter.mp hp).2)
  have hsplit : PWW.card + PUW.card + PWU.card ≤ P0.card := by
    have d1 : Disjoint PWW PUW := by
      rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h1.1 h2.1
    have d2 : Disjoint (PWW ∪ PUW) PWU := by
      rw [Finset.disjoint_union_left]; constructor
      · rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h1.2.1 h2.2.1
      · rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h2.1 h1.1
    rw [← Finset.card_union_of_disjoint d1, ← Finset.card_union_of_disjoint d2]
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter, PWW, PUW, PWU, P0] at hp ⊢
    rcases hp with (h | h) | h <;> exact ⟨h.1, h.2.2.2⟩
  have hswap : PWU.card = PUW.card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_univ,
        true_and, PWU, PUW, Prod.fst_swap, Prod.snd_swap] at ha ⊢
      exact ⟨ha.2.1, ha.1, by rw [Sym2.eq_swap]; exact ha.2.2⟩
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_univ,
        true_and, PWU, PUW, Prod.fst_swap, Prod.snd_swap] at ha ⊢
      exact ⟨ha.2.1, ha.1, by rw [Sym2.eq_swap]; exact ha.2.2⟩
    · intro a _; simp
    · intro a _; simp
  let xcnt : Fin n → ℕ := fun u => (W.filter (fun w => s(u, w) ∈ X)).card
  have hsum : PUW.card = ∑ u ∈ U, xcnt u := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := U)]
    · apply Finset.sum_congr rfl
      intro u hu
      apply Finset.card_nbij' Prod.snd (fun w => (u, w))
      · intro a ha
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_univ,
          true_and, PUW, W, Finset.mem_filter] at ha ⊢
        obtain ⟨⟨_, h2, h3⟩, rfl⟩ := ha
        exact ⟨h2, h3⟩
      · intro a ha
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_univ,
          true_and, PUW, W, Finset.mem_filter] at ha ⊢
        exact ⟨⟨hu, ha.1, ha.2⟩, by simp⟩
      · intro a ha
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
        exact Prod.ext ha.2.symm rfl
      · intro a _; rfl
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.1
  have hS : 6 * S.card ≤ k * k + k * m + m * k + PWW.card := by
    rw [complete_triangle_reduction_offDiag_sum n S hS3' hSdis]
    have hsub : S.biUnion (fun s => s.offDiag) ⊆
        ((U ×ˢ U ∪ U ×ˢ W) ∪ W ×ˢ U) ∪ PWW := by
      intro p hp
      obtain ⟨s, hs, hp⟩ := Finset.mem_biUnion.mp hp
      rw [Finset.mem_offDiag] at hp
      by_cases h1 : p.1 ∈ U <;> by_cases h2 : p.2 ∈ U
      · simp [h1, h2]
      · simp [h1, h2, W]
      · simp [h1, h2, W]
      · have hx : s(p.1, p.2) ∈ X := by
          apply hforce s hs
          · simpa using hp.2.2
          · intro v hv
            rcases Sym2.mem_iff.mp hv with rfl | rfl
            · exact hp.1
            · exact hp.2.1
          · intro u hu hv
            rcases Sym2.mem_iff.mp hv with rfl | rfl
            · exact h1 hu
            · exact h2 hu
        simp [h1, h2, PWW, hx]
    calc (S.biUnion (fun s => s.offDiag)).card
        ≤ (((U ×ˢ U ∪ U ×ˢ W) ∪ W ×ˢ U) ∪ PWW).card := Finset.card_le_card hsub
      _ ≤ k * k + k * m + m * k + PWW.card := by
        refine (Finset.card_union_le _ _).trans ?_
        refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
        refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) ?_
        · rw [Finset.card_product, Finset.card_product, hWc]
        · rw [Finset.card_product, hWc]
  have hper : ∀ u ∈ U, 6 * k * m ≤ 6 * k * xcnt u + PWW.card + (3 * k + 1) ^ 2 := by
    intro u hu
    set A := W.filter (fun w => s(u, w) ∉ X) with hA
    have hAx : xcnt u + A.card = m := by
      rw [← hWc]; exact Finset.card_filter_add_card_filter_not _
    have hcov' := complete_triangle_reduction_cover n U X hXe hcov u hu
    have hAeq : A = Finset.univ.filter (fun w => w ∉ U ∧ s(u, w) ∉ X) := by
      rw [hA, hWdef, Finset.filter_filter]
    have hle : A.offDiag.card ≤ PWW.card := by
      rw [hAeq]; exact Finset.card_le_card hcov'
    rw [Finset.offDiag_card] at hle
    have h1 : A.card ≤ A.card * A.card := Nat.le_mul_self _
    have h2 : (A.card : ℤ) * A.card - A.card ≤ PWW.card := by
      have := hle; zify [h1] at this; linarith
    have h3 : ((xcnt u : ℕ) : ℤ) + A.card = m := by exact_mod_cast hAx
    have : (6 * k * m : ℤ) ≤ 6 * k * xcnt u + PWW.card + (3 * k + 1) ^ 2 := by
      nlinarith [sq_nonneg ((A.card : ℤ) - 3 * k - 1)]
    exact_mod_cast this
  have hsumper := Finset.sum_le_sum hper
  rw [Finset.sum_const, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, ← Finset.mul_sum, ← hsum, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hsumper
  have hglob : 6 * PUW.card + PWW.card ≤ 2 * k * k + 4 * k * m := by
    nlinarith
  have hmk : 40 * k ≤ m := by omega
  have hk1 : 1 ≤ k := hU
  nlinarith
