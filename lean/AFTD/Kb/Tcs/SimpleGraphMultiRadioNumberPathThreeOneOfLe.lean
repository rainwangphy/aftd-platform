import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumberPathLeEightMul
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumberPathMono
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_multi_radio_number_path_three_one_of_le

Topic: graphs   Node: 481e047f2acc

Provenance: helper lemma. Special case m = 1 of the thread goal simple_graph_multi_radio_number_path_three_of_le (the case k = 3 of Conjecture 1 of arXiv:2610.25863, OP-384). For m = 1 an (m,3)-radio labeling is an L(3,2,1)-labeling, whose value on long paths is known in that literature; this is a base case of the ladder, not a new result.

For every n >= 8 the (1,3)-radio number of the path P_n is exactly 7: the case m = 1 of the thread's goal (8m - 1 for n >= 4m + 4).
-/

/-- Separation `|x - y| ≥ k` of two labels, in ℕ. -/
def path_radio_sep (k x y : ℕ) : Prop := x + k ≤ y ∨ y + k ≤ x

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
theorem radio_three_one_path_eight_core :
    ∀ b0 : Fin 7,
    ∀ b1 : Fin 7, path_radio_sep 3 b0.val b1.val →
    ∀ b2 : Fin 7, path_radio_sep 2 b0.val b2.val → path_radio_sep 3 b1.val b2.val →
    ∀ b3 : Fin 7, path_radio_sep 1 b0.val b3.val → path_radio_sep 2 b1.val b3.val → path_radio_sep 3 b2.val b3.val →
    ∀ b4 : Fin 7, path_radio_sep 1 b1.val b4.val → path_radio_sep 2 b2.val b4.val → path_radio_sep 3 b3.val b4.val →
    ∀ b5 : Fin 7, path_radio_sep 1 b2.val b5.val → path_radio_sep 2 b3.val b5.val → path_radio_sep 3 b4.val b5.val →
    ∀ b6 : Fin 7, path_radio_sep 1 b3.val b6.val → path_radio_sep 2 b4.val b6.val → path_radio_sep 3 b5.val b6.val →
    ∀ b7 : Fin 7, path_radio_sep 1 b4.val b7.val → path_radio_sep 2 b5.val b7.val → path_radio_sep 3 b6.val b7.val → False := by
  unfold path_radio_sep
  decide +kernel

theorem path_graph_dist_le_add (n i d : ℕ) (h : i + d < n) :
    (SimpleGraph.pathGraph n).dist ⟨i, by omega⟩ ⟨i + d, h⟩ ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have : Nonempty (Fin n) := ⟨⟨i, by omega⟩⟩
    have hc : (SimpleGraph.pathGraph n).Connected := ⟨SimpleGraph.pathGraph_preconnected n⟩
    have hadj : (SimpleGraph.pathGraph n).Adj ⟨i + d, by omega⟩ ⟨i + (d + 1), h⟩ := by
      rw [SimpleGraph.pathGraph_adj]; left; simp; omega
    have h1 : (SimpleGraph.pathGraph n).dist ⟨i + d, by omega⟩ ⟨i + (d + 1), h⟩ ≤ 1 := by
      have := SimpleGraph.dist_le hadj.toWalk; simpa using this
    have h2 := ih (by omega)
    have h3 := hc.dist_triangle (u := ⟨i, by omega⟩) (v := ⟨i + d, by omega⟩) (w := ⟨i + (d + 1), h⟩)
    omega

theorem path_graph_dist_le_sub {n : ℕ} (x y : Fin n) (hxy : x.val ≤ y.val) :
    (SimpleGraph.pathGraph n).dist x y ≤ y.val - x.val := by
  have := path_graph_dist_le_add n x.val (y.val - x.val) (by omega)
  have hy : (⟨x.val + (y.val - x.val), by omega⟩ : Fin n) = y := Fin.ext (by simp; omega)
  rw [hy] at this
  simpa using this

theorem radio_three_one_path_eight_span_ge (f : Fin 8 → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph 8) 1 3 f) :
    7 ≤ multi_label_span f := by
  have h1 : ∀ v, ∃ x, f v = {x} := fun v => Finset.card_eq_one.mp (hf.1 v)
  choose a ha using h1
  have hfa : f = fun v => {a v} := funext ha
  have hsepZ : ∀ x y : Fin 8, x.val < y.val →
      (3 + 1 : ℤ) - ((y.val - x.val : ℕ) : ℤ) ≤ |(a x : ℤ) - a y| := by
    intro x y hxy
    have hne : (x, a x) ≠ (y, a y) := by
      intro h; have := congrArg Prod.fst h; simp at this; subst this; omega
    have := hf.2 x y (a x) (by rw [ha x]; simp) (a y) (by rw [ha y]; simp) hne
    have hd := path_graph_dist_le_sub x y hxy.le
    push_cast at this ⊢
    have : ((SimpleGraph.pathGraph 8).dist x y : ℤ) ≤ ((y.val - x.val : ℕ) : ℤ) := by exact_mod_cast hd
    linarith
  by_contra hlt
  push Not at hlt
  have hspan : ∀ x y : Fin 8, a y - a x ≤ 6 := by
    intro x y
    have : a y - a x ≤ multi_label_span f := by
      rw [hfa]; unfold multi_label_span
      simp only [Finset.sup_singleton]
      exact le_trans (Finset.le_sup (f := fun y => a y - a x) (Finset.mem_univ y))
        (Finset.le_sup (f := fun x => Finset.univ.sup fun y => a y - a x) (Finset.mem_univ x))
    omega
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ a ⟨0, Finset.mem_univ _⟩
  set b : Fin 8 → ℕ := fun v => a v - a i0 with hbdef
  have hb : ∀ v, b v < 7 := fun v => by have := hspan i0 v; simp only [hbdef]; omega
  have hsep : ∀ i j : Fin 8, i.val < j.val → j.val ≤ i.val + 3 →
      path_radio_sep (4 - (j.val - i.val)) (b i) (b j) := by
    intro i j hij hj
    have h := hsepZ i j hij
    have hi := hi0 i (Finset.mem_univ _)
    have hj' := hi0 j (Finset.mem_univ _)
    unfold path_radio_sep; simp only [hbdef]
    rw [le_abs] at h
    omega
  exact radio_three_one_path_eight_core ⟨b 0, hb 0⟩ ⟨b 1, hb 1⟩ (hsep 0 1 (by decide) (by decide)) ⟨b 2, hb 2⟩ (hsep 0 2 (by decide) (by decide)) (hsep 1 2 (by decide) (by decide)) ⟨b 3, hb 3⟩ (hsep 0 3 (by decide) (by decide)) (hsep 1 3 (by decide) (by decide)) (hsep 2 3 (by decide) (by decide)) ⟨b 4, hb 4⟩ (hsep 1 4 (by decide) (by decide)) (hsep 2 4 (by decide) (by decide)) (hsep 3 4 (by decide) (by decide)) ⟨b 5, hb 5⟩ (hsep 2 5 (by decide) (by decide)) (hsep 3 5 (by decide) (by decide)) (hsep 4 5 (by decide) (by decide)) ⟨b 6, hb 6⟩ (hsep 3 6 (by decide) (by decide)) (hsep 4 6 (by decide) (by decide)) (hsep 5 6 (by decide) (by decide)) ⟨b 7, hb 7⟩ (hsep 4 7 (by decide) (by decide)) (hsep 5 7 (by decide) (by decide)) (hsep 6 7 (by decide) (by decide))

theorem simple_graph_multi_radio_number_path_three_one_of_le (n : ℕ) (hn : 8 ≤ n) :
    simple_graph_multi_radio_number (SimpleGraph.pathGraph n) 1 3 = 7 := by
  have hup := simple_graph_multi_radio_number_path_le_eight_mul n 1 (by omega) le_rfl
  have h8 : 7 ≤ simple_graph_multi_radio_number (SimpleGraph.pathGraph 8) 1 3 := by
    have hne : {s | ∃ f, simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph 8) 1 3 f ∧
        multi_label_span f = s}.Nonempty := by
      obtain ⟨f, hf⟩ :=
        simple_graph_multi_radio_number_path_mono_exists_labeling (SimpleGraph.pathGraph 8) 1 3
      exact ⟨_, f, hf, rfl⟩
    obtain ⟨f, hf, hs⟩ := Nat.sInf_mem hne
    unfold simple_graph_multi_radio_number
    rw [← hs]
    exact radio_three_one_path_eight_span_ge f hf
  have hmono : ∀ d, simple_graph_multi_radio_number (SimpleGraph.pathGraph 8) 1 3 ≤
      simple_graph_multi_radio_number (SimpleGraph.pathGraph (8 + d)) 1 3 := by
    intro d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact le_trans ih (simple_graph_multi_radio_number_path_mono (8 + d) 1 3 (by omega))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := hmono d
  omega
