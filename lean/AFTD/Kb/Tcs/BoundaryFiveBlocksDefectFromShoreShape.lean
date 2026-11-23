import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# boundary_five_blocks_defect_from_shore_shape

Topic: graphs   Node: 6e24d9fb1c14

Provenance: helper lemma. OP-1957: final finite-set step from bridge-shore counts to cross-defect restrictions.

Under the displayed four-block degree and anticompleteness hypotheses, the two specified shore-shape implications yield the corresponding cross-nonneighbor defect classification.
-/

theorem boundary_five_blocks_defect_from_shore_shape
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hC : C.card=5) (hsizeCD : C.card+D.card=2*k)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (Q W : Finset (Fin (4*k)))
    (hyQadj : ∀ q ∈ Q, ¬ G.Adj y q)
    (hxWadj : ∀ w ∈ W, ¬ G.Adj x w)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w)
    (hone : (C.filter (fun c => ¬ G.Adj x c)).card ≤ 1 → 2 ≤ (Q ∩ A).card)
    (htwo : (C.filter (fun c => ¬ G.Adj x c)).card = 2 →
      (W ∩ C).card = 2 ∧ (Q ∩ B).card = 1) :
    (((C.filter (fun c => ¬ G.Adj x c)).card = 2) →
      ∀ u ∈ C, ¬ G.Adj x u → (A.filter (fun a => ¬ G.Adj a u)).card = 1) ∧
    (((C.filter (fun c => ¬ G.Adj x c)).card ≤ 1) →
      (A.filter (fun a => ¬ G.Adj a y)).card = 2) := by
  classical
  have nAB : ∀ v, v ∈ A → v ∉ B := fun v h => Finset.disjoint_left.mp hAB h
  have nAC : ∀ v, v ∈ A → v ∉ C := fun v h => Finset.disjoint_left.mp hAC h
  have nAD : ∀ v, v ∈ A → v ∉ D := fun v h => Finset.disjoint_left.mp hAD h
  have nBC : ∀ v, v ∈ B → v ∉ C := fun v h => Finset.disjoint_left.mp hBC h
  have nBD : ∀ v, v ∈ B → v ∉ D := fun v h => Finset.disjoint_left.mp hBD h
  have nCD : ∀ v, v ∈ C → v ∉ D := fun v h => Finset.disjoint_left.mp hCD h
  have hDcard : D.card = 2*k-5 := by omega
  have hbud : ∀ c ∈ C, (((Finset.univ \ D).erase c) \ G.neighborFinset c).card ≤ 2 := by
    intro c hc
    apply anticomplete_neighbor_defect_bound G D c (nCD c hc) (hnoCD c hc) (2*k+4) 2
    · simp only [Fintype.card_fin]; omega
    · have hh := hdegree c; omega
  have hYupper : (A.filter (fun a => ¬ G.Adj a y)).card ≤ 2 := by
    have hsub : A.filter (fun a => ¬ G.Adj a y) ⊆ ((Finset.univ \ D).erase y) \ G.neighborFinset y := by
      intro a ha
      obtain ⟨haA,hano⟩ := Finset.mem_filter.mp ha
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨fun h => nAC y (h ▸ haA) hy, nAD a haA⟩, fun h => hano h.symm⟩
    exact (Finset.card_le_card hsub).trans (hbud y hy)
  constructor
  · intro hr u hu huno
    obtain ⟨hwc,hqb⟩ := htwo hr
    have hWsub : W ∩ C ⊆ C.filter (fun c => ¬ G.Adj x c) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hc).2, hxWadj c (Finset.mem_inter.mp hc).1⟩
    have hWeq : W ∩ C = C.filter (fun c => ¬ G.Adj x c) := by
      apply Finset.eq_of_subset_of_card_le hWsub
      omega
    have huWC : u ∈ W ∩ C := by
      rw [hWeq]
      exact Finset.mem_filter.mpr ⟨hu,huno⟩
    have huW : u ∈ W := (Finset.mem_inter.mp huWC).1
    obtain ⟨b,hbeq⟩ := Finset.card_eq_one.mp hqb
    have hbQB : b ∈ Q∩B := by rw [hbeq]; simp
    have hbQ : b ∈ Q := (Finset.mem_inter.mp hbQB).1
    have hbB : b ∈ B := (Finset.mem_inter.mp hbQB).2
    have hxb : x ≠ b := fun h => nAB b (h ▸ hx) hbB
    let F := ((Finset.univ \ D).erase u) \ G.neighborFinset u
    have hpair : ({x,b} : Finset (Fin (4*k))) ⊆ F := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · subst v
        simp only [F, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
        exact ⟨⟨fun h => nAC u (h ▸ hx) hu, nAD x hx⟩, fun h => huno h.symm⟩
      · subst v
        simp only [F, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
        exact ⟨⟨fun h => nBC u (h ▸ hbB) hu, nBD b hbB⟩, fun h => hcross b hbQ u huW h.symm⟩
    have hF : F = {x,b} := by
      symm
      apply Finset.eq_of_subset_of_card_le hpair
      rw [Finset.card_pair hxb]
      exact hbud u hu
    have hAeq : A.filter (fun a => ¬ G.Adj a u) = {x} := by
      ext a
      constructor
      · intro ha
        obtain ⟨haA,hano⟩ := Finset.mem_filter.mp ha
        have haF : a ∈ F := by
          simp only [F, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
          exact ⟨⟨fun h => nAC u (h ▸ haA) hu, nAD a haA⟩, fun h => hano h.symm⟩
        rw [hF] at haF
        simp only [Finset.mem_insert, Finset.mem_singleton] at haF
        rcases haF with h | h
        · simpa [h]
        · exact False.elim (nAB a haA (h.symm ▸ hbB))
      · intro ha
        have : a=x := Finset.mem_singleton.mp ha
        subst a
        exact Finset.mem_filter.mpr ⟨hx,huno⟩
    rw [hAeq, Finset.card_singleton]
  · intro hr
    have hsub : Q∩A ⊆ A.filter (fun a => ¬ G.Adj a y) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp ha).2, fun h => hyQadj a (Finset.mem_inter.mp ha).1 h.symm⟩
    have hlo := Finset.card_le_card hsub
    have h2 := hone hr
    omega
