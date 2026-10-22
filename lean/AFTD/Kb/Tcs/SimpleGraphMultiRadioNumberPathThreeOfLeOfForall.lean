import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumberPathLeEightMul
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumberPathMono
import AFTD.Kb.Tcs.G

/-!
# simple_graph_multi_radio_number_path_three_of_le_of_forall

Topic: graphs   Node: 12030b7ed530

Provenance: helper lemma. Step toward simple_graph_multi_radio_number_path_three_of_le (thread RT-4; case k = 3 of Conjecture 1 of arXiv:2610.25863, OP-384).

Reduction of the thread goal to one finite statement per m: if no (m,3)-radio labeling of P_{4m+4} has all labels at most 8m - 2, then the (m,3)-radio number of P_n is 8m - 1 for every n >= 4m + 4.
-/

/-- Every label difference `b - a` is at most the span. -/
theorem multi_label_span_sub_le {V : Type*} [Fintype V] (f : V → Finset ℕ) {x y : V} {a b : ℕ}
    (ha : a ∈ f x) (hb : b ∈ f y) : b - a ≤ multi_label_span f :=
  le_trans (Finset.le_sup (f := fun b => b - a) hb)
    (le_trans (Finset.le_sup (f := fun a => (f y).sup fun b => b - a) ha)
      (le_trans (Finset.le_sup (f := fun y => (f x).sup fun a => (f y).sup fun b => b - a)
          (Finset.mem_univ y))
        (Finset.le_sup (f := fun x => Finset.univ.sup fun y =>
          (f x).sup fun a => (f y).sup fun b => b - a) (Finset.mem_univ x))))

/-- Shifting all labels down by the least one keeps a multi-radio labeling, and then every
label is at most the original span. -/
theorem multi_radio_labeling_shift {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (m k : ℕ) (hm : 1 ≤ m) (f : V → Finset ℕ) (hf : simple_graph_is_multi_radio_labeling G m k f) :
    ∃ g : V → Finset ℕ, simple_graph_is_multi_radio_labeling G m k g ∧
      ∀ v, ∀ a ∈ g v, a ≤ multi_label_span f := by
  classical
  obtain ⟨v0⟩ := ‹Nonempty V›
  have hne : (Finset.univ.biUnion f).Nonempty := by
    have : (f v0).Nonempty := Finset.card_pos.mp (by rw [hf.1 v0]; omega)
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_biUnion.mpr ⟨v0, Finset.mem_univ _, ha⟩⟩
  set μ := (Finset.univ.biUnion f).min' hne with hμ
  have hμle : ∀ v, ∀ a ∈ f v, μ ≤ a := fun v a ha =>
    Finset.min'_le _ _ (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, ha⟩)
  obtain ⟨y0, -, hy0⟩ := Finset.mem_biUnion.mp (Finset.min'_mem _ hne)
  refine ⟨fun v => (f v).image (fun a => a - μ), ⟨fun v => ?_, fun x y a' ha' b' hb' hne' => ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injOn, hf.1 v]
    intro a ha b hb hab
    have := hμle v a ha; have := hμle v b hb
    simp only at hab; omega
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    have h1 := hμle x a ha; have h2 := hμle y b hb
    have hne2 : (x, a) ≠ (y, b) := by
      intro h; apply hne'
      have hx : x = y := congrArg Prod.fst h
      have hab : a = b := congrArg Prod.snd h
      rw [hx, hab]
    have := hf.2 x y a ha b hb hne2
    have e : ((a - μ : ℕ) : ℤ) - ((b - μ : ℕ) : ℤ) = (a : ℤ) - b := by push_cast [h1, h2]; ring
    rw [e]; exact this
  · intro v a' ha'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    have := multi_label_span_sub_le f hy0 ha
    rw [← hμ] at this
    exact this

theorem simple_graph_multi_radio_number_path_three_of_le_of_forall (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ f : Fin (4 * m + 4) → Finset ℕ,
      simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph (4 * m + 4)) m 3 f →
      (∀ v, ∀ a ∈ f v, a ≤ 8 * m - 2) → False)
    (n : ℕ) (hn : 4 * m + 4 ≤ n) :
    simple_graph_multi_radio_number (SimpleGraph.pathGraph n) m 3 = 8 * m - 1 := by
  have hup := simple_graph_multi_radio_number_path_le_eight_mul n m (by omega) hm
  have hbase : 8 * m - 1 ≤ simple_graph_multi_radio_number (SimpleGraph.pathGraph (4 * m + 4)) m 3 := by
    have hne : {s | ∃ f, simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph (4 * m + 4)) m 3 f ∧
        multi_label_span f = s}.Nonempty := by
      obtain ⟨f, hf⟩ := simple_graph_multi_radio_number_path_mono_exists_labeling
        (SimpleGraph.pathGraph (4 * m + 4)) m 3
      exact ⟨_, f, hf, rfl⟩
    obtain ⟨f, hf, hs⟩ := Nat.sInf_mem hne
    unfold simple_graph_multi_radio_number
    rw [← hs]
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg, hgb⟩ := multi_radio_labeling_shift _ m 3 hm f hf
    exact h g hg (fun v a ha => by have := hgb v a ha; omega)
  have hmono : ∀ d, simple_graph_multi_radio_number (SimpleGraph.pathGraph (4 * m + 4)) m 3 ≤
      simple_graph_multi_radio_number (SimpleGraph.pathGraph (4 * m + 4 + d)) m 3 := by
    intro d
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact le_trans ih (simple_graph_multi_radio_number_path_mono (4 * m + 4 + d) m 3 (by omega))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := hmono d
  omega
