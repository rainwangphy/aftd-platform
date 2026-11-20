import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ExtendBitsAlongPaths

/-!
# op874_no_partial_mixed_closed_set

Topic: graphs   Node: e4272de61904

Provenance: helper lemma. Any closed-support mixed bit assignment extends along paths.

In a strongly connected directed two-out graph with no globally mixed bit assignment, no nonempty finite set can have a bit assignment where every vertex has an opposite-bit successor inside the set.
-/

theorem op874_no_partial_mixed_closed_set {X : Type*} [Fintype X] [DecidableEq X]
    (p q : Equiv.Perm X)
    (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v)
    (hno : ∀ b : X → Bool, ∃ x, b x = b (p x) ∧ b x = b (q x))
    (S : Finset X) (hS : S.Nonempty) (b0 : X → Bool)
    (hmixed : ∀ x ∈ S, (p x ∈ S ∧ b0 x ≠ b0 (p x)) ∨ (q x ∈ S ∧ b0 x ≠ b0 (q x))) : False := by
  let R : X → X → Prop := fun u v => p u = v ∨ q u = v
  have walk (u : X) (w : List Bool) : Relation.ReflTransGen R u (w.foldl (fun x bit => if bit then p x else q x) u) := by
    induction w generalizing u with
    | nil => exact Relation.ReflTransGen.refl
    | cons bit w ih =>
      simp only [List.foldl_cons]
      apply Relation.ReflTransGen.head _ (ih _)
      cases bit <;> simp [R]
  obtain ⟨z, hz⟩ := hS
  have hreach (u : X) : ∃ v ∈ S, Relation.ReflTransGen R u v := by
    obtain ⟨w, hw⟩ := hstrong u z
    exact ⟨z, hz, hw ▸ walk u w⟩
  obtain ⟨b, hb, hout⟩ := op874_extend_bits_along_paths R S b0 hreach
  obtain ⟨x, hxp, hxq⟩ := hno b
  by_cases hx : x ∈ S
  · rcases hmixed x hx with ⟨hp, hn⟩ | ⟨hq, hn⟩
    · exact hn ((hb x hx).symm.trans (hxp.trans (hb (p x) hp)))
    · exact hn ((hb x hx).symm.trans (hxq.trans (hb (q x) hq)))
  · obtain ⟨y, hxy, hxyb⟩ := hout x hx
    rcases hxy with h | h
    · exact hxyb (h ▸ hxp)
    · exact hxyb (h ▸ hxq)
