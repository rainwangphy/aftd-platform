import AFTD.Prelude

/-!
# wild_two_leaf_signature_translation_seal

Topic: graphs   Node: bd12b73ae308

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

In a commutative group of exponent two, take two disjoint three-element sets {x,x+e,z} and {y,y+e,w} containing no zero. If x+z equals y+w or y+w+e, their six-element union is closed under translation by z+w; that translator is nonzero and lies outside the union.
-/

open Finset
set_option maxHeartbeats 2000000

private lemma in338_cancel_pair {G : Type*} [AddCommGroup G]
    (h2 : ∀ a : G, a + a = 0) (a b : G) : (a + b) + b = a := by
  rw [add_assoc, h2, add_zero]

private lemma in338_translate_pair {G : Type*} [AddCommGroup G]
    (h2 : ∀ a : G, a + a = 0) (a b c : G) (h : c = a + b) : a + c = b := by
  rw [h, ← add_assoc, h2, zero_add]

private lemma in338_leaf_translation {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h2 : ∀ a : G, a + a = 0) (e x y z w : G)
    (hsig : x + z = y + w ∨ x + z = y + w + e) :
    ∀ v ∈ ({x, x + e, z, y, y + e, w} : Finset G),
      v + (z + w) ∈ ({x, x + e, z, y, y + e, w} : Finset G) := by
  have hzw := in338_translate_pair h2 z w (z + w) rfl
  have hwz : w + (z + w) = z := by
    calc
      _ = (z + (z + w)) + (z + w) := congrArg (fun v => v + (z + w)) hzw.symm
      _ = z := in338_cancel_pair h2 _ _
  have hxc : x + (z + w) = y ∨ x + (z + w) = y + e := by
    rcases hsig with h | h
    · left
      calc
        _ = (x + z) + w := by abel
        _ = (y + w) + w := by rw [h]
        _ = y := in338_cancel_pair h2 _ _
    · right
      calc
        _ = (x + z) + w := by abel
        _ = (y + w + e) + w := by rw [h]
        _ = (y + e + w) + w := by abel
        _ = y + e := in338_cancel_pair h2 _ _
  rcases hxc with hxy | hxye
  · have hyx : y + (z + w) = x := by rw [← hxy, in338_cancel_pair h2]
    have hxeye : (x + e) + (z + w) = y + e := by
      calc
        _ = (x + (z + w)) + e := by abel
        _ = _ := by rw [hxy]
    have hyexe : (y + e) + (z + w) = x + e := by
      rw [← hxeye, in338_cancel_pair h2]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hxy, hyx, hxeye, hyexe, hzw, hwz] <;> tauto
  · have hyex : (y + e) + (z + w) = x := by rw [← hxye, in338_cancel_pair h2]
    have hxey : (x + e) + (z + w) = y := by
      calc
        _ = (x + (z + w)) + e := by abel
        _ = (y + e) + e := by rw [hxye]
        _ = y := in338_cancel_pair h2 _ _
    have hyxe : y + (z + w) = x + e := by rw [← hxey, in338_cancel_pair h2]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hxye, hyex, hxey, hyxe, hzw, hwz] <;> tauto

theorem wild_two_leaf_signature_translation_seal
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h2 : ∀ a : G, a + a = 0) (e x y z w : G)
    (hA : ({x, x + e, z} : Finset G).card = 3)
    (hB : ({y, y + e, w} : Finset G).card = 3)
    (hdis : Disjoint ({x, x + e, z} : Finset G) {y, y + e, w})
    (hzero : (0 : G) ∉ ({x, x + e, z} : Finset G) ∪ {y, y + e, w})
    (hsig : x + z = y + w ∨ x + z = y + w + e) :
    let U := ({x, x + e, z} : Finset G) ∪ {y, y + e, w}
    U.card = 6 ∧ z + w ≠ 0 ∧ z + w ∉ U ∧
      ∀ v ∈ U, v + (z + w) ∈ U := by
  dsimp only
  have hU : ({x, x + e, z} : Finset G) ∪ {y, y + e, w} =
      {x, x + e, z, y, y + e, w} := by ext v; simp; tauto
  have ht := in338_leaf_translation h2 e x y z w hsig
  rw [← hU] at ht
  have hne : z ≠ w := by
    intro h
    exact (Finset.disjoint_left.mp hdis) (by simp : z ∈ ({x, x + e, z} : Finset G))
      (by simp [h] : z ∈ ({y, y + e, w} : Finset G))
  have hc : z + w ≠ 0 := by
    intro h
    exact hne (add_right_cancel (h.trans (h2 w).symm))
  refine ⟨?_, hc, ?_, ht⟩
  · rw [card_union_of_disjoint hdis, hA, hB]
  · intro h
    have hz := ht (z + w) h
    rw [h2] at hz
    exact hzero hz
