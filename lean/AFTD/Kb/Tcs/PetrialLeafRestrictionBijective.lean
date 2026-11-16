import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLeafRestriction

/-!
# petrial_leaf_restriction_bijective

Topic: combinatorics   Node: 84aac34f834f

Provenance: helper lemma. Subset-counting helper for the OP-1239 leaf recurrence.

For distinct vertices v and u, a vertex subset omitting v is uniquely determined by its membership bit at u and its restriction to the complement of u and v.
-/

set_option maxRecDepth 10000

theorem petrial_leaf_restriction_bijective {V : Type*} [Fintype V] [DecidableEq V] (v u : V) (hvu : v ≠ u) : Function.Bijective (fun F : {F : Finset V // v ∉ F} => (decide (u ∈ F.1), petrial_leaf_restriction v u F.1)) := by
  classical
  constructor
  · intro F G h
    have hb : (u ∈ F.1) ↔ (u ∈ G.1) := by
      have hb := congrArg Prod.fst h
      simpa using hb
    have hs := congrArg Prod.snd h
    apply Subtype.ext
    ext x
    by_cases hxv : x = v
    · subst x; simp [F.2, G.2]
    · by_cases hxu : x = u
      · subst x; exact hb
      · have hm := congrArg (fun S => (⟨x, by simp [hxu, hxv]⟩ : ({u, v}ᶜ : Set V)) ∈ S) hs
        simpa [petrial_leaf_restriction] using hm
  · rintro ⟨b, S⟩
    let F : Finset V := if b then insert u (S.image Subtype.val) else S.image Subtype.val
    have hsub (x : ({u,v}ᶜ : Set V)) : (x : V) ≠ u ∧ (x : V) ≠ v := by
      constructor
      · intro h; exact x.property (by simp [h])
      · intro h; exact x.property (by simp [h])
    have hnotu : u ∉ S.image Subtype.val := by
      intro h
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
      exact (hsub x).1 he
    have hnotv : v ∉ S.image Subtype.val := by
      intro h
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
      exact (hsub x).2 he
    have hv : v ∉ F := by cases b <;> simp [F, hvu, hnotv]
    refine ⟨⟨F, hv⟩, ?_⟩
    apply Prod.ext
    · cases b <;> simp [F, hnotu]
    · ext x
      have hx := hsub x
      have himage : ((x : V) ∈ S.image Subtype.val) ↔ x ∈ S := by
        constructor
        · intro h
          obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
          have : y = x := Subtype.ext he
          simpa [this] using hy
        · intro h
          exact Finset.mem_image.mpr ⟨x, h, rfl⟩
      cases b <;> simp [petrial_leaf_restriction, F, hx.1, hx.2, himage]
