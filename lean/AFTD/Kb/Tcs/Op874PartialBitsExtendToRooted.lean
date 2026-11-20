import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ExtendBitsAlongPaths

/-!
# op874_partial_bits_extend_to_rooted

Topic: graphs   Node: c55ad05f248d

Provenance: helper lemma. Extend a partial rooted double-cross bit assignment along directed paths.

A partial bit assignment with the desired rooted mixed and double-cross properties extends to the whole strongly connected directed graph.
-/

theorem op874_partial_bits_extend_to_rooted {X : Type*} [Fintype X] [DecidableEq X]
    (p q : Equiv.Perm X)
    (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v)
    (r x : X) (S : Finset X) (b0 : X → Bool)
    (hr : r ∈ S) (hx : x ∈ S) (hp : p x ∈ S) (hq : q x ∈ S)
    (hpartial : ∀ y ∈ S, y ≠ r → (p y ∈ S ∧ b0 y ≠ b0 (p y)) ∨ (q y ∈ S ∧ b0 y ≠ b0 (q y)))
    (hpx : b0 x ≠ b0 (p x)) (hqx : b0 x ≠ b0 (q x)) :
    ∃ b : X → Bool, (∀ y, y ≠ r → b y ≠ b (p y) ∨ b y ≠ b (q y)) ∧
      b x ≠ b (p x) ∧ b x ≠ b (q x) := by
  let R : X → X → Prop := fun u v => p u = v ∨ q u = v
  have walk (u : X) (w : List Bool) : Relation.ReflTransGen R u (w.foldl (fun x bit => if bit then p x else q x) u) := by
    induction w generalizing u with
    | nil => exact Relation.ReflTransGen.refl
    | cons bit w ih =>
      simp only [List.foldl_cons]
      apply Relation.ReflTransGen.head _ (ih _)
      cases bit <;> simp [R]
  have hreach (u : X) : ∃ v ∈ S, Relation.ReflTransGen R u v := by
    obtain ⟨w, hw⟩ := hstrong u r
    exact ⟨r, hr, hw ▸ walk u w⟩
  obtain ⟨b, hb, hout⟩ := op874_extend_bits_along_paths R S b0 hreach
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y hyr
    by_cases hy : y ∈ S
    · rcases hpartial y hy hyr with ⟨hyp, hne⟩ | ⟨hyq, hne⟩
      · left; rw [hb y hy, hb (p y) hyp]; exact hne
      · right; rw [hb y hy, hb (q y) hyq]; exact hne
    · obtain ⟨z, hyz, hn⟩ := hout y hy
      rcases hyz with hpz | hqz
      · left; exact hpz ▸ hn
      · right; exact hqz ▸ hn
  · rw [hb x hx, hb (p x) hp]; exact hpx
  · rw [hb x hx, hb (q x) hq]; exact hqx
