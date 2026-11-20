import AFTD.Prelude
import AFTD.Kb.Tcs.FactorCriticalAnticompleteCutSideEven
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# factorcritical_crossing_even_shore_covers_opposite_first_side

Topic: graphs   Node: adb044c8e878

Provenance: helper lemma. OP-1957 factor-critical crossing-cut reduction; experiment 35757 checks the resulting finite set obstruction.

In a 2k-factor-critical complement graph, let A and B be disjoint first shores whose only possible missing H-edge across them is uv. If a second shore W lies in their union, meets A in a nonempty even set, is H-complete to an opposite shore Q and to x,y, and |Q|+|W|=d+1, then B lies in W∪Q.
-/

theorem factorcritical_crossing_even_shore_covers_opposite_first_side (k d : ℕ) (H : SimpleGraph (Fin (2*k+d+3))) [DecidableRel H.Adj] (hcrit : is_k_factor_critical Hᶜ (2*k)) (x y u v : Fin (2*k+d+3)) (hxy : x ≠ y) (A B Q W : Finset (Fin (2*k+d+3))) (hAB : Disjoint A B) (hxu : x ∉ A ∪ B) (hyu : y ∉ A ∪ B) (hqx : x ∉ Q) (hqy : y ∉ Q) (hu : u ∈ A) (hv : v ∈ B) (hcut : ∀ a ∈ A, ∀ b ∈ B, (a ≠ u ∨ b ≠ v) → H.Adj a b) (hwsub : W ⊆ A ∪ B) (heven : Even (W ∩ A).card) (hne : (W ∩ A).Nonempty) (hsize : Q.card + W.card = d+1) (hxyW : ∀ w ∈ W, H.Adj x w ∧ H.Adj y w) (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : B ⊆ W ∪ Q := by
  classical
  intro b hb
  by_contra hbnot
  have hbW : b ∉ W := by intro h; exact hbnot (Finset.mem_union_left Q h)
  have hbQ : b ∉ Q := by intro h; exact hbnot (Finset.mem_union_right W h)
  have hWApos : 0 < (W ∩ A).card := Finset.card_pos.mpr hne
  have herase : (W ∩ A).card - 1 ≤ ((W ∩ A).erase u).card := by
    by_cases h : u ∈ W ∩ A
    · rw [Finset.card_erase_of_mem h]
    · rw [Finset.erase_eq_of_notMem h]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq herase
  have hTWA : T ⊆ W ∩ A := fun a ha => Finset.mem_of_mem_erase (hTsub ha)
  have hTu : ∀ a ∈ T, a ≠ u := fun a ha => Finset.ne_of_mem_erase (hTsub ha)
  let WB := W ∩ B
  have hQW : Disjoint Q W := by
    apply Finset.disjoint_left.mpr
    intro a haQ haW
    exact H.irrefl (hcross a haQ a haW)
  have hQWB : Disjoint Q WB := by
    apply Finset.disjoint_left.mpr
    intro a haQ haWB
    exact (Finset.disjoint_left.mp hQW) haQ (Finset.mem_inter.mp haWB).1
  have hxW : x ∉ W := fun h => hxu (hwsub h)
  have hyW : y ∉ W := fun h => hyu (hwsub h)
  have hxb : x ≠ b := by intro h; apply hxu; rw [h]; exact Finset.mem_union_right A hb
  have hyb : y ≠ b := by intro h; apply hyu; rw [h]; exact Finset.mem_union_right A hb
  have hbx : b ≠ x := hxb.symm
  have hby : b ≠ y := hyb.symm
  have hbWB : b ∉ WB := by intro h; exact hbW (Finset.mem_inter.mp h).1
  have hxWB : x ∉ WB := by intro h; exact hxW (Finset.mem_inter.mp h).1
  have hyWB : y ∉ WB := by intro h; exact hyW (Finset.mem_inter.mp h).1
  let D := insert x (insert y (insert b (Q ∪ WB)))
  have hxD : x ∉ insert y (insert b (Q ∪ WB)) := by simp [hxy, hxb, hqx, hxWB]
  have hyD : y ∉ insert b (Q ∪ WB) := by simp [hyb, hqy, hyWB]
  have hbD : b ∉ Q ∪ WB := by simp [hbQ, hbWB]
  have hDcard : D.card = Q.card + WB.card + 3 := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem hxD, Finset.card_insert_of_notMem hyD,
      Finset.card_insert_of_notMem hbD, Finset.card_union_of_disjoint hQWB]
  have hdisj : Disjoint T D := by
    apply Finset.disjoint_left.mpr
    intro a ha hD
    have haW : a ∈ W := (Finset.mem_inter.mp (hTWA ha)).1
    have haA : a ∈ A := (Finset.mem_inter.mp (hTWA ha)).2
    dsimp [D, WB] at hD
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_inter] at hD
    rcases hD with rfl | rfl | rfl | hQ | ⟨hW,hB⟩
    · exact hxW haW
    · exact hyW haW
    · exact hbW haW
    · exact (Finset.disjoint_left.mp hQW) hQ haW
    · exact (Finset.disjoint_left.mp hAB) haA hB
  have hcrossD : ∀ a ∈ T, ∀ c ∈ D, ¬ Hᶜ.Adj a c := by
    intro a ha c hc hadj
    have haW : a ∈ W := (Finset.mem_inter.mp (hTWA ha)).1
    have haA : a ∈ A := (Finset.mem_inter.mp (hTWA ha)).2
    have hac : H.Adj a c := by
      dsimp [D, WB] at hc
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_inter] at hc
      rcases hc with rfl | rfl | rfl | hQ | ⟨hW,hB⟩
      · exact (hxyW a haW).1.symm
      · exact (hxyW a haW).2.symm
      · exact hcut a haA c hb (Or.inl (hTu a ha))
      · exact (hcross c hQ a haW).symm
      · exact hcut a haA c hB (Or.inl (hTu a ha))
    exact hadj.2 hac
  have hpart : (W ∩ A).card + WB.card = W.card := by
    have hd : Disjoint (W ∩ A) WB := by
      apply Finset.disjoint_left.mpr
      intro a h1 h2
      exact (Finset.disjoint_left.mp hAB) (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
    have hun : (W ∩ A) ∪ WB = W := by
      ext a
      simp only [WB, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
      · intro h
        rcases Finset.mem_union.mp (hwsub h) with hA | hB
        · exact Or.inl ⟨h,hA⟩
        · exact Or.inr ⟨h,hB⟩
    have hc := Finset.card_union_of_disjoint hd
    rw [hun] at hc
    omega
  have hunion : (T ∪ D).card = d+3 := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard, hDcard]
    omega
  have hcomp : ((Finset.univ : Finset (Fin (2*k+d+3))) \ (T ∪ D)).card = 2*k := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (T ∪ D))
    simp only [Finset.card_univ, Fintype.card_fin, hunion] at h
    omega
  have hTeven := factor_critical_anticomplete_cut_side_even Hᶜ (2*k) hcrit T D hdisj hcrossD hcomp
  rw [hTcard] at hTeven
  rcases heven with ⟨a, ha⟩
  rcases hTeven with ⟨c, hc⟩
  omega
