import AFTD.Prelude

/-!
# wild_leaf_translation_color_unique

Topic: graphs   Node: 4743e3c4fee6

Provenance: helper lemma. OP-306 / IN-338 general construction helpers related to arXiv:2610.22142, Sections3.3.2 and6. Binary leaf-translation classification and standard maximal rainbow-matching counting, used to repair the diagnosed sampling law (experiments8414 and8442). No new exact wild-number case, numerical bound or research advance is claimed.

In a commutative exponent-two group, let U={x,x+e,z,y,y+e,w}, and assume z+e lies outside U. Any nonzero translation preserving U must have translator exactly z+w.
-/

open Finset
set_option maxHeartbeats 2500000

private lemma in338_reverse_translation {G : Type*} [AddCommGroup G]
    (h2 : ∀ v : G, v + v = 0) (a b c : G) (h : a + c = b) : b + c = a := by
  calc
    _ = (a + c) + c := congrArg (fun v => v + c) h.symm
    _ = a := by rw [add_assoc, h2, add_zero]

private lemma in338_slide_translation {G : Type*} [AddCommGroup G]
    (h2 : ∀ v : G, v + v = 0) (a e c : G) : ((a + e) + c) + e = a + c := by
  calc
    _ = (a + c) + (e + e) := by abel
    _ = a + c := by rw [h2, add_zero]

theorem wild_leaf_translation_color_unique
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h2 : ∀ v : G, v + v = 0) (e x y z w c : G)
    (hzext : z + e ∉ ({x,x+e,z,y,y+e,w} : Finset G)) (hc : c ≠ 0)
    (ht : ∀ v ∈ ({x,x+e,z,y,y+e,w} : Finset G),
      v + c ∈ ({x,x+e,z,y,y+e,w} : Finset G)) : c = z + w := by
  let U : Finset G := {x,x+e,z,y,y+e,w}
  have hp : ∀ t : G, t ∈ U → t + e ∈ U → z + c ≠ t ∧ z + c ≠ t + e := by
    intro t htU hteU
    constructor
    · intro h
      have hb := in338_reverse_translation h2 z t c h
      have heq : (t + e) + c = z + e := by
        calc
          _ = (t + c) + e := by abel
          _ = z + e := by rw [hb]
      exact hzext (heq ▸ ht (t+e) hteU)
    · intro h
      have hb := in338_reverse_translation h2 z (t+e) c h
      have heq : t + c = z + e := by
        calc
          _ = ((t+e)+c)+e := (in338_slide_translation h2 t e c).symm
          _ = z + e := congrArg (fun v => v+e) hb
      exact hzext (heq ▸ ht t htU)
  have hpx := hp x (by simp [U]) (by simp [U])
  have hpy := hp y (by simp [U]) (by simp [U])
  have hz := ht z (by simp)
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with h | h | h | h | h | h
  · exact (hpx.1 h).elim
  · exact (hpx.2 h).elim
  · exact (hc (add_left_cancel (h.trans (add_zero z).symm))).elim
  · exact (hpy.1 h).elim
  · exact (hpy.2 h).elim
  · have hh := congrArg (fun v => z + v) h
    simpa only [← add_assoc, h2, zero_add] using hh
