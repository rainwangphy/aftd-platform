import AFTD.Prelude
import AFTD.Kb.Tcs.WildLeafTranslationColorUnique
import AFTD.Kb.Tcs.WildTwoLeafSignatureTranslationSeal

/-!
# wild_leaf_translation_seal_iff_signature_collision

Topic: graphs   Node: 47bde2399ed9

Provenance: helper lemma. OP-306 / IN-338 general construction helpers related to arXiv:2610.22142, Sections3.3.2 and6. Binary leaf-translation classification and standard maximal rainbow-matching counting, used to repair the diagnosed sampling law (experiments8414 and8442). No new exact wild-number case, numerical bound or research advance is claimed.

For two disjoint nonzero triples {x,x+e,z} and {y,y+e,w} in a commutative exponent-two group, with z+e outside their union, some nonzero translation preserves that union if and only if their leaf signatures x+z and y+w are equal modulo {0,e}.
-/

open Finset
set_option maxHeartbeats 2500000

private lemma in338_reverse_translation_sig {G : Type*} [AddCommGroup G]
    (h2 : ∀ v : G, v + v = 0) (a b c : G) (h : a + c = b) : b + c = a := by
  calc
    _ = (a + c) + c := congrArg (fun v => v + c) h.symm
    _ = a := by rw [add_assoc, h2, add_zero]

private lemma in338_slide_translation_sig {G : Type*} [AddCommGroup G]
    (h2 : ∀ v : G, v + v = 0) (a e c : G) : ((a + e) + c) + e = a + c := by
  calc
    _ = (a + c) + (e + e) := by abel
    _ = a + c := by rw [h2, add_zero]

theorem wild_leaf_translation_seal_iff_signature_collision
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h2 : ∀ v : G, v + v = 0) (e x y z w : G)
    (hA : ({x,x+e,z} : Finset G).card = 3)
    (hB : ({y,y+e,w} : Finset G).card = 3)
    (hdis : Disjoint ({x,x+e,z} : Finset G) {y,y+e,w})
    (hzero : (0 : G) ∉ ({x,x+e,z,y,y+e,w} : Finset G))
    (hzext : z + e ∉ ({x,x+e,z,y,y+e,w} : Finset G)) :
    (∃ c : G, c ≠ 0 ∧ ∀ v ∈ ({x,x+e,z,y,y+e,w} : Finset G),
      v + c ∈ ({x,x+e,z,y,y+e,w} : Finset G)) ↔
      x + z = y + w ∨ x + z = y + w + e := by
  have hU : ({x,x+e,z} : Finset G) ∪ {y,y+e,w} = {x,x+e,z,y,y+e,w} := by
    ext v; simp; tauto
  constructor
  · rintro ⟨c, hc, ht⟩
    have hcw := wild_leaf_translation_color_unique h2 e x y z w c hzext hc ht
    have hxz : x ≠ z := by
      intro h
      subst z
      have hsub : ({x,x+e,x} : Finset G) ⊆ {x,x+e} := by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv ⊢
        tauto
      have hh := (card_le_card hsub).trans (card_le_two (a := x) (b := x+e))
      omega
    have hxw : x ≠ w := by
      intro h
      exact disjoint_left.mp hdis (by simp : x ∈ ({x,x+e,z} : Finset G))
        (by simp [h] : x ∈ ({y,y+e,w} : Finset G))
    have hzw : z + c = w := by rw [hcw, ← add_assoc, h2, zero_add]
    have hwz := in338_reverse_translation_sig h2 z w c hzw
    have hcancel : (x+c)+w = x+z := by
      calc
        _ = ((x+z)+w)+w := by rw [hcw]; abel
        _ = x+z := by rw [add_assoc, h2, add_zero]
    have hx := ht x (by simp)
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h | h | h | h
    · exact (hc (add_left_cancel (h.trans (add_zero x).symm))).elim
    · have hce : c = e := add_left_cancel h
      exact (hzext (hce ▸ ht z (by simp))).elim
    · have hb := in338_reverse_translation_sig h2 x z c h
      exact (hxw (hb.symm.trans hzw)).elim
    · left
      exact hcancel.symm.trans (congrArg (fun v => v+w) h)
    · right
      calc
        _ = (x+c)+w := hcancel.symm
        _ = (y+e)+w := congrArg (fun v => v+w) h
        _ = y+w+e := by abel
    · have hb := in338_reverse_translation_sig h2 x w c h
      exact (hxz (hb.symm.trans hwz)).elim
  · intro hsig
    obtain ⟨_, hc, _, ht⟩ := wild_two_leaf_signature_translation_seal h2 e x y z w
      hA hB hdis (by simpa only [hU] using hzero) hsig
    exact ⟨z+w, hc, by simpa only [hU] using ht⟩
