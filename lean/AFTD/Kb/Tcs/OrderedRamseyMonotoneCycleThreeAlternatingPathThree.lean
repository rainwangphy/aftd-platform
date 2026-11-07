import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedRamseyNumber
import AFTD.Kb.Tcs.MonotoneCycle
import AFTD.Kb.Tcs.AlternatingPath
import AFTD.Kb.Tcs.HasOrderedCopy
import AFTD.Kb.Tcs.AlternatingPathVertex
import AFTD.Kb.Tcs.OrderedRamseyProp
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ordered_ramsey_monotone_cycle_three_alternating_path_three

Topic: graphs   Node: b7168882d3b6

Provenance: helper lemma. arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 5

The ordered Ramsey number of the monotone cycle MC_3 and the alternating path AP_3 is equal to 5.
-/

open SimpleGraph

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_mono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (H : SimpleGraph α) (H' : SimpleGraph β) {M N : ℕ} (hMN : M ≤ N)
    (hM : ordered_ramsey_prop H H' M) : ordered_ramsey_prop H H' N := by
  intro G
  let emb : Fin M → Fin N := fun x => ⟨x.val, by omega⟩
  have hemb_mono : StrictMono emb := fun _ _ hxy => hxy
  have hemb_inj : Function.Injective emb := hemb_mono.injective
  let G' : SimpleGraph (Fin M) :=
    { Adj := fun u v => G.Adj (emb u) (emb v)
      symm := ⟨fun {_ _} h => G.adj_symm h⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  rcases hM G' with ⟨f, hf_mono, hf_adj⟩ | ⟨f, hf_mono, hf_adj⟩
  · left
    refine ⟨emb ∘ f, hemb_mono.comp hf_mono, ?_⟩
    intro u v huv
    exact hf_adj huv
  · right
    refine ⟨emb ∘ f, hemb_mono.comp hf_mono, ?_⟩
    intro u v huv
    have := hf_adj huv
    rw [compl_adj] at this ⊢
    refine ⟨fun h => this.1 (hemb_inj h), this.2⟩

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_exists_m_three (P : ℕ → Prop) :
    (∃ m : ℕ, m + 1 < 3 ∧ P m) ↔ P 0 ∨ P 1 := by
  constructor
  · rintro ⟨m, hm, hp⟩
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl
    · left; exact hp
    · right; exact hp
  · rintro (h0 | h1)
    · exact ⟨0, by decide, h0⟩
    · exact ⟨1, by decide, h1⟩

theorem ordered_ramsey_monotone_cycle_three_alternating_path_three_mc3_eq_top : monotone_cycle 3 = ⊤ := by
  ext a b
  simp [monotone_cycle, SimpleGraph.fromRel_adj]
  fin_cases a <;> fin_cases b <;> decide

theorem ordered_ramsey_monotone_cycle_three_alternating_path_three_ap3_adj (a b : Fin 3) :
    (alternating_path 3).Adj a b ↔ (a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0) ∨
      (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 1) := by
  simp only [alternating_path, fromRel_adj, ordered_ramsey_monotone_cycle_three_alternating_path_three_exists_m_three, alternating_path_vertex]
  fin_cases a <;> fin_cases b <;> decide

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 {N : ℕ} (G : SimpleGraph (Fin N)) {u v w : Fin N}
    (huv : u < v) (hvw : v < w) (hadj1 : G.Adj u v) (hadj2 : G.Adj v w) (hadj3 : G.Adj u w) :
    has_ordered_copy G (monotone_cycle 3) := by
  let f : Fin 3 → Fin N := fun x =>
    if x = 0 then u else if x = 1 then v else w
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · exfalso; exact lt_irrefl _ hxy
    · dsimp [f]; exact huv
    · dsimp [f]; exact huv.trans hvw
    · exfalso; revert hxy; decide
    · exfalso; exact lt_irrefl _ hxy
    · dsimp [f]; exact hvw
    · exfalso; revert hxy; decide
    · exfalso; revert hxy; decide
    · exfalso; exact lt_irrefl _ hxy
  · intro x y hxy
    rw [ordered_ramsey_monotone_cycle_three_alternating_path_three_mc3_eq_top, top_adj] at hxy
    fin_cases x <;> fin_cases y
    · exfalso; exact hxy rfl
    · dsimp [f]; exact hadj1
    · dsimp [f]; exact hadj3
    · dsimp [f]; exact hadj1.symm
    · exfalso; exact hxy rfl
    · dsimp [f]; exact hadj2
    · dsimp [f]; exact hadj3.symm
    · dsimp [f]; exact hadj2.symm
    · exfalso; exact hxy rfl

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_has_ap3_compl {N : ℕ} (G : SimpleGraph (Fin N)) {u v w : Fin N}
    (huv : u < v) (hvw : v < w) (hnot1 : ¬ G.Adj u w) (hnot2 : ¬ G.Adj v w) :
    has_ordered_copy Gᶜ (alternating_path 3) := by
  let f : Fin 3 → Fin N := fun x =>
    if x = 0 then u else if x = 1 then v else w
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · exfalso; exact lt_irrefl _ hxy
    · dsimp [f]; exact huv
    · dsimp [f]; exact huv.trans hvw
    · exfalso; revert hxy; decide
    · exfalso; exact lt_irrefl _ hxy
    · dsimp [f]; exact hvw
    · exfalso; revert hxy; decide
    · exfalso; revert hxy; decide
    · exfalso; exact lt_irrefl _ hxy
  · intro x y hxy
    rw [ordered_ramsey_monotone_cycle_three_alternating_path_three_ap3_adj] at hxy
    rw [compl_adj]
    fin_cases x <;> fin_cases y
    · exfalso; revert hxy; decide
    · exfalso; revert hxy; decide
    · dsimp [f]; exact ⟨(huv.trans hvw).ne, hnot1⟩
    · exfalso; revert hxy; decide
    · exfalso; revert hxy; decide
    · dsimp [f]; exact ⟨hvw.ne, hnot2⟩
    · dsimp [f]; exact ⟨(huv.trans hvw).ne', fun h => hnot1 (G.adj_symm h)⟩
    · dsimp [f]; exact ⟨hvw.ne', fun h => hnot2 (G.adj_symm h)⟩
    · exfalso; revert hxy; decide

theorem ordered_ramsey_monotone_cycle_three_alternating_path_three_prop_fast
    (e02 e12 e03 e13 e23 e04 e14 e24 e34 : Prop)
    (h012 : e02 ∨ e12)
    (h013 : e03 ∨ e13)
    (h023 : e03 ∨ e23)
    (h123 : e13 ∨ e23)
    (h014 : e04 ∨ e14)
    (h024 : e04 ∨ e24)
    (h034 : e04 ∨ e34)
    (h124 : e14 ∨ e24)
    (h134 : e14 ∨ e34)
    (h234 : e24 ∨ e34) :
    (e02 ∧ e24 ∧ e04) ∨
    (e12 ∧ e24 ∧ e14) ∨
    (e03 ∧ e34 ∧ e04) ∨
    (e13 ∧ e34 ∧ e14) ∨
    (e23 ∧ e34 ∧ e24) := by
  by_cases h34 : e34
  · by_cases h24 : e24
    · by_cases h23 : e23
      · right; right; right; right; exact ⟨h23, h34, h24⟩
      · have he03 : e03 := by rcases h023 with h | h; exact h; contradiction
        have he13 : e13 := by rcases h123 with h | h; exact h; contradiction
        rcases h014 with he04 | he14
        · right; right; left; exact ⟨he03, h34, he04⟩
        · right; right; right; left; exact ⟨he13, h34, he14⟩
    · have he04 : e04 := by rcases h024 with h | h; exact h; contradiction
      have he14 : e14 := by rcases h124 with h | h; exact h; contradiction
      rcases h013 with he03 | he13
      · right; right; left; exact ⟨he03, h34, he04⟩
      · right; right; right; left; exact ⟨he13, h34, he14⟩
  · have he04 : e04 := by rcases h034 with h | h; exact h; contradiction
    have he14 : e14 := by rcases h134 with h | h; exact h; contradiction
    have he24 : e24 := by rcases h234 with h | h; exact h; contradiction
    rcases h012 with he02 | he12
    · left; exact ⟨he02, he24, he04⟩
    · right; left; exact ⟨he12, he24, he14⟩

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_prop_five :
    ordered_ramsey_prop (monotone_cycle 3) (alternating_path 3) 5 := by
  intro G
  by_cases h_ap : has_ordered_copy Gᶜ (alternating_path 3)
  · right; exact h_ap
  · left
    have H_ap : ∀ ⦃u v w : Fin 5⦄, u < v → v < w → G.Adj u w ∨ G.Adj v w := by
      intro u v w huv hvw
      by_contra! h
      exact h_ap (ordered_ramsey_monotone_cycle_three_alternating_path_three_has_ap3_compl G huv hvw h.1 h.2)
    have h_tri := ordered_ramsey_monotone_cycle_three_alternating_path_three_prop_fast
      (G.Adj 0 2) (G.Adj 1 2) (G.Adj 0 3) (G.Adj 1 3) (G.Adj 2 3)
      (G.Adj 0 4) (G.Adj 1 4) (G.Adj 2 4) (G.Adj 3 4)
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
      (H_ap (by decide) (by decide))
    rcases h_tri with ⟨h02, h24, h04⟩ | ⟨h12, h24, h14⟩ | ⟨h03, h34, h04⟩ | ⟨h13, h34, h14⟩ | ⟨h23, h34, h24⟩
    · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 G (by decide) (by decide) h02 h24 h04
    · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 G (by decide) (by decide) h12 h24 h14
    · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 G (by decide) (by decide) h03 h34 h04
    · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 G (by decide) (by decide) h13 h34 h14
    · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_has_mc3 G (by decide) (by decide) h23 h34 h24

def ordered_ramsey_monotone_cycle_three_alternating_path_three_G4 : SimpleGraph (Fin 4) where
  Adj u v := (u.val = 0 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨
             (u.val = 0 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0) ∨
             (u.val = 1 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 1)
  symm := ⟨by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; exact ⟨h2, h1⟩
    · left; exact ⟨h2, h1⟩
    · right; right; right; left; exact ⟨h2, h1⟩
    · right; right; left; exact ⟨h2, h1⟩
    · right; right; right; right; right; exact ⟨h2, h1⟩
    · right; right; right; right; left; exact ⟨h2, h1⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_fin3_fin4_mono_cases (f : Fin 3 → Fin 4) (hf : StrictMono f) :
    (f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 2) ∨
    (f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 3) ∨
    (f 0 = 0 ∧ f 1 = 2 ∧ f 2 = 3) ∨
    (f 0 = 1 ∧ f 1 = 2 ∧ f 2 = 3) := by
  have h01 := hf (by decide : (0 : Fin 3) < 1)
  have h12 := hf (by decide : (1 : Fin 3) < 2)
  generalize ha : f 0 = a at h01 ⊢
  generalize hb : f 1 = b at h01 h12 ⊢
  generalize hc : f 2 = c at h12 ⊢
  fin_cases a <;> fin_cases b <;> fin_cases c <;> omega

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_G4_not_mc3 :
    ¬ has_ordered_copy ordered_ramsey_monotone_cycle_three_alternating_path_three_G4 (monotone_cycle 3) := by
  intro ⟨f, hf_mono, hf_adj⟩
  have h_cases := ordered_ramsey_monotone_cycle_three_alternating_path_three_fin3_fin4_mono_cases f hf_mono
  have htop : ∀ ⦃u v : Fin 3⦄, u ≠ v → ordered_ramsey_monotone_cycle_three_alternating_path_three_G4.Adj (f u) (f v) := by
    intro u v huv
    apply hf_adj
    rw [ordered_ramsey_monotone_cycle_three_alternating_path_three_mc3_eq_top, top_adj]
    exact huv
  rcases h_cases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have h := htop (by decide : (0 : Fin 3) ≠ 1)
    rw [h0, h1] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · have h := htop (by decide : (0 : Fin 3) ≠ 1)
    rw [h0, h1] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · have h := htop (by decide : (1 : Fin 3) ≠ 2)
    rw [h1, h2] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · have h := htop (by decide : (0 : Fin 3) ≠ 1)
    rw [h0, h1] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_G4_not_ap3 :
    ¬ has_ordered_copy ordered_ramsey_monotone_cycle_three_alternating_path_three_G4ᶜ (alternating_path 3) := by
  intro ⟨f, hf_mono, hf_adj⟩
  have h_cases := ordered_ramsey_monotone_cycle_three_alternating_path_three_fin3_fin4_mono_cases f hf_mono
  have hap : ∀ ⦃u v : Fin 3⦄, (alternating_path 3).Adj u v → ¬ ordered_ramsey_monotone_cycle_three_alternating_path_three_G4.Adj (f u) (f v) := by
    intro u v huv
    have := hf_adj huv
    rw [compl_adj] at this
    exact this.2
  have h02 : (alternating_path 3).Adj 0 2 := by
    rw [ordered_ramsey_monotone_cycle_three_alternating_path_three_ap3_adj]
    decide
  rcases h_cases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have h := hap h02
    rw [h0, h2] at h
    apply h
    left; decide
  · have h := hap h02
    rw [h0, h2] at h
    apply h
    right; right; left; decide
  · have h := hap h02
    rw [h0, h2] at h
    apply h
    right; right; left; decide
  · have h := hap h02
    rw [h0, h2] at h
    apply h
    right; right; right; right; left; decide

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_not_prop_four :
    ¬ ordered_ramsey_prop (monotone_cycle 3) (alternating_path 3) 4 := by
  intro hprop
  rcases hprop ordered_ramsey_monotone_cycle_three_alternating_path_three_G4 with h | h
  · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_G4_not_mc3 h
  · exact ordered_ramsey_monotone_cycle_three_alternating_path_three_G4_not_ap3 h

lemma ordered_ramsey_monotone_cycle_three_alternating_path_three_forall_lt_not_prop (M : ℕ) (hM : M < 5) :
    ¬ ordered_ramsey_prop (monotone_cycle 3) (alternating_path 3) M := by
  intro hprop
  have h4 : ordered_ramsey_prop (monotone_cycle 3) (alternating_path 3) 4 :=
    ordered_ramsey_monotone_cycle_three_alternating_path_three_mono _ _ (by omega) hprop
  exact ordered_ramsey_monotone_cycle_three_alternating_path_three_not_prop_four h4

/-- The ordered Ramsey number of the monotone cycle MC_3 versus the alternating path AP_3 is 5. -/
theorem ordered_ramsey_monotone_cycle_three_alternating_path_three :
    ordered_ramsey_number (monotone_cycle 3) (alternating_path 3) = 5 := by
  have hupper := ordered_ramsey_monotone_cycle_three_alternating_path_three_prop_five
  have hlower := ordered_ramsey_monotone_cycle_three_alternating_path_three_forall_lt_not_prop
  dsimp [ordered_ramsey_number]
  have hnonempty : (Set.Nonempty {n | ordered_ramsey_prop (monotone_cycle 3) (alternating_path 3) n}) :=
    ⟨5, hupper⟩
  rw [csInf_eq_iff hnonempty]
  refine ⟨hupper, ?_⟩
  intro M hM
  by_contra! hlt
  exact hlower M hlt hM
