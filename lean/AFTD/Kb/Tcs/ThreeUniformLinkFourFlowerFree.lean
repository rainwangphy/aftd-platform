import AFTD.Prelude
import AFTD.Kb.Tcs.IsSunflower

/-!
# three_uniform_link_four_flower_free

Topic: combinatorics   Node: 6e1ba844b8bb

Provenance: formalization of a published result. Source: arXiv:2611.13495, Sec. 5

For any 3-uniform 4-flower-free family S, the link of each element x (the family of pairs s \ {x} for s ∈ S containing x) is 2-uniform and 4-flower-free.
-/

/-- The link of any vertex in a 3-uniform 4-flower-free hypergraph is 2-uniform and 4-flower-free. -/
theorem three_uniform_link_four_flower_free {α : Type*} [DecidableEq α]
    (S : Finset (Finset α))
    (h3 : ∀ s ∈ S, s.card = 3)
    (hfree : ¬ ∃ F ⊆ S, F.card = 4 ∧ ∃ C, IsSunflower F C)
    (x : α) :
    let L := (S.filter (x ∈ ·)).image (·.erase x)
    (∀ e ∈ L, e.card = 2) ∧ ¬ ∃ F ⊆ L, F.card = 4 ∧ ∃ C, IsSunflower F C := by
  dsimp only
  constructor
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨s, hs, rfl⟩ := he
    rw [Finset.mem_filter] at hs
    rw [Finset.card_erase_of_mem hs.2, h3 s hs.1]
  · rintro ⟨F, hFsub, hFcard, C, hC⟩
    apply hfree
    have hxnot : ∀ e ∈ F, x ∉ e := by
      intro e he
      have heL : e ∈ (S.filter (x ∈ ·)).image (·.erase x) := hFsub he
      rw [Finset.mem_image] at heL
      obtain ⟨s, hs, hse⟩ := heL
      rw [← hse]
      exact Finset.notMem_erase x s
    refine ⟨F.image (insert x), ?_, ?_, insert x C, ?_⟩
    · intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨e, heF, rfl⟩ := hA
      have heL : e ∈ (S.filter (x ∈ ·)).image (·.erase x) := hFsub heF
      rw [Finset.mem_image] at heL
      obtain ⟨s, hs, hse⟩ := heL
      rw [Finset.mem_filter] at hs
      rw [← hse, Finset.insert_erase hs.2]
      exact hs.1
    · have hinj : Set.InjOn (fun e => insert x e) (F : Set (Finset α)) := by
        intro e1 he1 e2 he2 heq
        have h1 := hxnot e1 he1
        have h2 := hxnot e2 he2
        have h := congrArg (·.erase x) heq
        rwa [Finset.erase_insert h1, Finset.erase_insert h2] at h
      rw [Finset.card_image_of_injOn hinj, hFcard]
    · constructor
      · intro A hA
        rw [Finset.mem_image] at hA
        obtain ⟨e, heF, rfl⟩ := hA
        exact Finset.insert_subset_insert x (hC.1 e heF)
      · intro A hA B hB hAB
        rw [Finset.mem_image] at hA hB
        obtain ⟨e1, he1, rfl⟩ := hA
        obtain ⟨e2, he2, rfl⟩ := hB
        have hne : e1 ≠ e2 := by
          intro h
          exact hAB (by rw [h])
        rw [← Finset.insert_inter_distrib, hC.2 e1 he1 e2 he2 hne]
