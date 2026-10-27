import AFTD.Prelude
import AFTD.Kb.Tcs.IsCirculantGraph

/-!
# order_eight_hankel_not_circulant

Topic: combinatorics   Node: 030eeb5effbf

Provenance: helper lemma. step towards exists_non_circulant_sharp_cyclic_graph_order_eight

Any simple graph on ZMod 8 whose adjacency is given by (x + y).val ∈ {1, 3, 5} is not a circulant graph on ZMod 8.
-/

/-- The reduction of `ZMod 8` modulo `2`, used as a 2-colouring of the Hankel graph. -/
private def order_eight_hankel_not_circulant_cast : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num) (ZMod 2)

/-- In `ZMod 2` every element is its own negative. -/
private lemma order_eight_hankel_not_circulant_zmod2_add_self :
    ∀ x : ZMod 2, x + x = 0 := by decide

/-- A negation-closed set of three nonzero residues modulo 8 contains `4`. -/
private lemma order_eight_hankel_not_circulant_four_mem :
    ∀ T : Finset (ZMod 8), T.card = 3 → (∀ t ∈ T, -t ∈ T) → (0 : ZMod 8) ∉ T →
      (4 : ZMod 8) ∈ T := by decide

/-- A set of three residues modulo 8 has an element different from `4`. -/
private lemma order_eight_hankel_not_circulant_exists_ne_four :
    ∀ T : Finset (ZMod 8), T.card = 3 → ∃ a ∈ T, a ≠ 4 := by decide

/-- Every residue modulo 8 other than `0` and `4` satisfies `2a = 4` or `4a = 4`. -/
private lemma order_eight_hankel_not_circulant_two_mul_or_four_mul :
    ∀ a : ZMod 8, a ≠ 0 → a ≠ 4 → 2 * a = 4 ∨ 4 * a = 4 := by decide

/-- In `ZMod 2` two distinct elements differ by `1`. -/
private lemma order_eight_hankel_not_circulant_zmod2_ne :
    ∀ x y : ZMod 2, y ≠ x → y = x + 1 := by decide

/-- In `ZMod 2` adding `1` twice is the identity. -/
private lemma order_eight_hankel_not_circulant_zmod2_add_one_add_one :
    ∀ x : ZMod 2, x + 1 + 1 = x := by decide

/-- Any simple graph on ZMod 8 whose adjacency is given by (x + y).val ∈ {1, 3, 5} is not a circulant graph on ZMod 8. -/
theorem order_eight_hankel_not_circulant
    (G : SimpleGraph (ZMod 8))
    (hG : ∀ x y : ZMod 8, G.Adj x y ↔ (x + y).val = 1 ∨ (x + y).val = 3 ∨ (x + y).val = 5) :
    ¬ is_circulant_graph 8 G := by
  rintro ⟨s, ⟨e⟩⟩
  classical
  have hval : ∀ z : ZMod 8, (z.val = 1 ∨ z.val = 3 ∨ z.val = 5) ↔ (z = 1 ∨ z = 3 ∨ z = 5) := by
    decide
  have hcast1 : ∀ z : ZMod 8, (z.val = 1 ∨ z.val = 3 ∨ z.val = 5) →
      order_eight_hankel_not_circulant_cast z = 1 := by decide
  have hcolorG : ∀ x y : ZMod 8, G.Adj x y →
      order_eight_hankel_not_circulant_cast x ≠ order_eight_hankel_not_circulant_cast y := by
    intro x y hxy
    have hsum : order_eight_hankel_not_circulant_cast x +
        order_eight_hankel_not_circulant_cast y = 1 := by
      have h := hcast1 (x + y) ((hG x y).mp hxy)
      rwa [map_add] at h
    intro heq
    rw [heq] at hsum
    rw [order_eight_hankel_not_circulant_zmod2_add_self] at hsum
    exact zero_ne_one hsum
  have hAdj0 : ∀ y : ZMod 8, G.Adj 0 y ↔ (y = 1 ∨ y = 3 ∨ y = 5) := by
    intro y
    have h := hG 0 y
    rw [zero_add] at h
    exact h.trans (hval y)
  let T : Finset (ZMod 8) := Finset.univ.filter (fun t => t ≠ 0 ∧ (t ∈ s ∨ -t ∈ s))
  have hTmem : ∀ t : ZMod 8, t ∈ T ↔ t ≠ 0 ∧ (t ∈ s ∨ -t ∈ s) := by
    intro t
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  let u : ZMod 8 := e 0
  have hAdjU : ∀ w : ZMod 8,
      (SimpleGraph.circulantGraph s).Adj u w ↔ (w = e 1 ∨ w = e 3 ∨ w = e 5) := by
    intro w
    have key : (SimpleGraph.circulantGraph s).Adj (e 0) w ↔ G.Adj 0 (e.symm w) := by
      conv_lhs => rw [show w = e (e.symm w) from (Equiv.apply_symm_apply _ w).symm]
      exact e.map_adj_iff
    rw [show u = e 0 from rfl, key, hAdj0]
    have h1 : e.symm w = 1 ↔ w = e 1 := Equiv.symm_apply_eq e.toEquiv
    have h3 : e.symm w = 3 ↔ w = e 3 := Equiv.symm_apply_eq e.toEquiv
    have h5 : e.symm w = 5 ↔ w = e 5 := Equiv.symm_apply_eq e.toEquiv
    simp only [h1, h3, h5]
  have hadj_iff : ∀ w : ZMod 8, (SimpleGraph.circulantGraph s).Adj u w ↔ w - u ∈ T := by
    intro w
    rw [hTmem]
    show u ≠ w ∧ (u - w ∈ s ∨ w - u ∈ s) ↔ w - u ≠ 0 ∧ (w - u ∈ s ∨ -(w - u) ∈ s)
    have hA : (u ≠ w) ↔ (w - u ≠ 0) := by rw [sub_ne_zero, ne_comm]
    have hB : (u - w ∈ s ∨ w - u ∈ s) ↔ (w - u ∈ s ∨ -(w - u) ∈ s) := by
      rw [neg_sub]; exact or_comm
    rw [hA, hB]
  have hTeq : T = ({e 1 - u, e 3 - u, e 5 - u} : Finset (ZMod 8)) := by
    ext t
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    have step1 : t ∈ T ↔ (SimpleGraph.circulantGraph s).Adj u (u + t) := by
      rw [hadj_iff (u + t), add_sub_cancel_left]
    rw [step1, hAdjU]
    simp only [eq_sub_iff_add_eq']
  have hTcard : T.card = 3 := by
    rw [hTeq]
    have h13 : e 1 ≠ e 3 := by
      intro hh
      exact absurd (e.injective hh) (by decide)
    have h15 : e 1 ≠ e 5 := by
      intro hh
      exact absurd (e.injective hh) (by decide)
    have h35 : e 3 ≠ e 5 := by
      intro hh
      exact absurd (e.injective hh) (by decide)
    have h12 : e 1 - u ≠ e 3 - u := fun hh => h13 (sub_left_inj.mp hh)
    have h13' : e 1 - u ≠ e 5 - u := fun hh => h15 (sub_left_inj.mp hh)
    have h23 : e 3 - u ≠ e 5 - u := fun hh => h35 (sub_left_inj.mp hh)
    simp [h12, h13', h23]
  have hTneg : ∀ t : ZMod 8, t ∈ T → -t ∈ T := by
    intro t ht
    rw [hTmem] at ht ⊢
    obtain ⟨h0, hs⟩ := ht
    refine ⟨?_, ?_⟩
    · rwa [neg_ne_zero]
    · rcases hs with hs | hs
      · right; simpa using hs
      · left; exact hs
  have hT0 : (0 : ZMod 8) ∉ T := by
    rw [hTmem]; simp
  have h4 : (4 : ZMod 8) ∈ T :=
    order_eight_hankel_not_circulant_four_mem T hTcard hTneg hT0
  obtain ⟨a, haT, ha4⟩ := order_eight_hankel_not_circulant_exists_ne_four T hTcard
  have ha0 : a ≠ 0 := ((hTmem a).mp haT).1
  let F : ZMod 8 → ZMod 2 := fun w => order_eight_hankel_not_circulant_cast (e.symm w)
  have hproper : ∀ v w : ZMod 8, (SimpleGraph.circulantGraph s).Adj v w → F v ≠ F w := by
    intro v w hv
    have hadj' : (SimpleGraph.circulantGraph s).Adj (e (e.symm v)) (e (e.symm w)) := by
      simpa using hv
    exact hcolorG (e.symm v) (e.symm w) ((e.map_adj_iff).mp hadj')
  have hflip : ∀ t : ZMod 8, t ∈ T → ∀ w : ZMod 8, F (w + t) ≠ F w := by
    intro t ht w
    rw [hTmem] at ht
    obtain ⟨ht0, hts⟩ := ht
    have e1 : w - (w + t) = -t := by ring
    have e2 : w + t - w = t := by ring
    have hadj : (SimpleGraph.circulantGraph s).Adj w (w + t) := by
      show w ≠ w + t ∧ (w - (w + t) ∈ s ∨ w + t - w ∈ s)
      refine ⟨?_, ?_⟩
      · intro h
        apply ht0
        have h3 : w + t - w = 0 := by rw [← h, sub_self]
        rwa [e2] at h3
      · rw [e1, e2]
        exact hts.symm
    exact Ne.symm (hproper w (w + t) hadj)
  have hflip4 : ∀ w : ZMod 8, F (w + 4) ≠ F w := hflip 4 h4
  have hflipa : ∀ w : ZMod 8, F (w + a) ≠ F w := hflip a haT
  have hpres2 : ∀ w : ZMod 8, F (w + 2 * a) = F w := by
    intro w
    have h1 : F (w + a) ≠ F w := hflipa w
    have h2 : F (w + a + a) ≠ F (w + a) := hflipa (w + a)
    have hy : F (w + a) = F w + 1 := order_eight_hankel_not_circulant_zmod2_ne _ _ h1
    have hz : F (w + a + a) = F (w + a) + 1 := order_eight_hankel_not_circulant_zmod2_ne _ _ h2
    have harg : w + a + a = w + 2 * a := by ring
    rw [harg] at hz
    rw [hz, hy]
    exact order_eight_hankel_not_circulant_zmod2_add_one_add_one (F w)
  have hab : 2 * a = 4 ∨ 4 * a = 4 :=
    order_eight_hankel_not_circulant_two_mul_or_four_mul a ha0 ha4
  rcases hab with h | h
  · have hp : F (0 + 4) = F 0 := by
      have hq := hpres2 0
      rwa [h] at hq
    exact hflip4 0 hp
  · have h4a : F (0 + 4 * a) = F 0 := by
      have hp1 := hpres2 0
      have hp2 := hpres2 (0 + 2 * a)
      have harg : (0 : ZMod 8) + 2 * a + 2 * a = 0 + 4 * a := by ring
      rw [harg] at hp2
      rw [hp2, hp1]
    rw [h] at h4a
    exact hflip4 0 h4a
