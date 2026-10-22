import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.SimpleGraphPathGraphDistGe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# path_three_radio_labeling_span_ge_seven

Topic: graphs   Node: ee3d8970b03d

Provenance: helper lemma. step towards simple_graph_multi_radio_number_path_three_of_le

For n >= 8, every (1,3)-radio labeling of the path P_n has span at least 7; combined with the upper bound 8m-1 at m = 1 this gives that the (1,3)-radio number of P_n is 7 for all n >= 8.
-/

def path_three_radio_labeling_span_ge_seven_sep (k x y : ℕ) : Prop := x + k ≤ y ∨ y + k ≤ x

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
theorem path_three_radio_labeling_span_ge_seven_core :
    ∀ b0 : Fin 7,
    ∀ b1 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 3 b0.val b1.val →
    ∀ b2 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 2 b0.val b2.val → path_three_radio_labeling_span_ge_seven_sep 3 b1.val b2.val →
    ∀ b3 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 1 b0.val b3.val → path_three_radio_labeling_span_ge_seven_sep 2 b1.val b3.val → path_three_radio_labeling_span_ge_seven_sep 3 b2.val b3.val →
    ∀ b4 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 1 b1.val b4.val → path_three_radio_labeling_span_ge_seven_sep 2 b2.val b4.val → path_three_radio_labeling_span_ge_seven_sep 3 b3.val b4.val →
    ∀ b5 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 1 b2.val b5.val → path_three_radio_labeling_span_ge_seven_sep 2 b3.val b5.val → path_three_radio_labeling_span_ge_seven_sep 3 b4.val b5.val →
    ∀ b6 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 1 b3.val b6.val → path_three_radio_labeling_span_ge_seven_sep 2 b4.val b6.val → path_three_radio_labeling_span_ge_seven_sep 3 b5.val b6.val →
    ∀ b7 : Fin 7, path_three_radio_labeling_span_ge_seven_sep 1 b4.val b7.val → path_three_radio_labeling_span_ge_seven_sep 2 b5.val b7.val → path_three_radio_labeling_span_ge_seven_sep 3 b6.val b7.val → False := by
  unfold path_three_radio_labeling_span_ge_seven_sep
  decide +kernel

theorem path_three_radio_labeling_span_ge_seven_dist_le_add (n i d : ℕ) (h : i + d < n) :
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

theorem path_three_radio_labeling_span_ge_seven_dist_le_sub {n : ℕ} (x y : Fin n) (hxy : x.val ≤ y.val) :
    (SimpleGraph.pathGraph n).dist x y ≤ y.val - x.val := by
  have := path_three_radio_labeling_span_ge_seven_dist_le_add n x.val (y.val - x.val) (by omega)
  have hy : (⟨x.val + (y.val - x.val), by omega⟩ : Fin n) = y := Fin.ext (by simp; omega)
  rw [hy] at this
  simpa using this

/-- The m = 1 base case of the k = 3 lower bound: span 6 cannot cover 8 vertices. -/
theorem path_three_radio_labeling_span_ge_seven (n : ℕ) (hn : 8 ≤ n) (f : Fin n → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph n) 1 3 f) :
    7 ≤ multi_label_span f := by
  have h1 : ∀ v, ∃ x, f v = {x} := fun v => Finset.card_eq_one.mp (hf.1 v)
  choose a ha using h1
  have hfa : f = fun v => {a v} := funext ha
  let v (k : Fin 8) : Fin n := ⟨k.val, by omega⟩
  have hsepZ : ∀ x y : Fin 8, x.val < y.val →
      (3 + 1 : ℤ) - ((y.val - x.val : ℕ) : ℤ) ≤ |(a (v x) : ℤ) - a (v y)| := by
    intro x y hxy
    have hne : (v x, a (v x)) ≠ (v y, a (v y)) := by
      intro h; have := congrArg Prod.fst h; simp [v] at this; omega
    have := hf.2 (v x) (v y) (a (v x)) (by rw [ha]; simp) (a (v y)) (by rw [ha]; simp) hne
    have hd := path_three_radio_labeling_span_ge_seven_dist_le_sub (v x) (v y) (by simp [v]; omega)
    push_cast at this ⊢
    have : ((SimpleGraph.pathGraph n).dist (v x) (v y) : ℤ) ≤ ((y.val - x.val : ℕ) : ℤ) := by
      exact_mod_cast hd
    linarith
  by_contra hlt
  push Not at hlt
  have hspan : ∀ x y : Fin n, a y - a x ≤ 6 := by
    intro x y
    have : a y - a x ≤ multi_label_span f := by
      rw [hfa]; unfold multi_label_span
      simp only [Finset.sup_singleton]
      exact le_trans (Finset.le_sup (f := fun y => a y - a x) (Finset.mem_univ y))
        (Finset.le_sup (f := fun x => Finset.univ.sup fun y => a y - a x) (Finset.mem_univ x))
    omega
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun k : Fin 8 => a (v k)) ⟨0, Finset.mem_univ _⟩
  set b : Fin 8 → ℕ := fun k => a (v k) - a (v i0) with hbdef
  have hb : ∀ k, b k < 7 := fun k => by have := hspan (v i0) (v k); simp only [hbdef]; omega
  have hsep : ∀ i j : Fin 8, i.val < j.val → j.val ≤ i.val + 3 →
      path_three_radio_labeling_span_ge_seven_sep (4 - (j.val - i.val)) (b i) (b j) := by
    intro i j hij hj
    have h := hsepZ i j hij
    have hi := hi0 i (Finset.mem_univ _)
    have hj' := hi0 j (Finset.mem_univ _)
    unfold path_three_radio_labeling_span_ge_seven_sep; simp only [hbdef]
    rw [le_abs] at h
    omega
  exact path_three_radio_labeling_span_ge_seven_core
    ⟨b 0, hb 0⟩ ⟨b 1, hb 1⟩ (hsep 0 1 (by decide) (by decide))
    ⟨b 2, hb 2⟩ (hsep 0 2 (by decide) (by decide)) (hsep 1 2 (by decide) (by decide))
    ⟨b 3, hb 3⟩ (hsep 0 3 (by decide) (by decide)) (hsep 1 3 (by decide) (by decide)) (hsep 2 3 (by decide) (by decide))
    ⟨b 4, hb 4⟩ (hsep 1 4 (by decide) (by decide)) (hsep 2 4 (by decide) (by decide)) (hsep 3 4 (by decide) (by decide))
    ⟨b 5, hb 5⟩ (hsep 2 5 (by decide) (by decide)) (hsep 3 5 (by decide) (by decide)) (hsep 4 5 (by decide) (by decide))
    ⟨b 6, hb 6⟩ (hsep 3 6 (by decide) (by decide)) (hsep 4 6 (by decide) (by decide)) (hsep 5 6 (by decide) (by decide))
    ⟨b 7, hb 7⟩ (hsep 4 7 (by decide) (by decide)) (hsep 5 7 (by decide) (by decide)) (hsep 6 7 (by decide) (by decide))
