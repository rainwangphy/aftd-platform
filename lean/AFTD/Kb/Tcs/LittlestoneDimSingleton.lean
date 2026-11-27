import AFTD.Prelude
import AFTD.Kb.Tcs.LittlestoneDim
import AFTD.Kb.Tcs.LittlestoneShatters

/-!
# littlestone_dim_singleton

Topic: learning   Node: 47237c965e72

Provenance: helper lemma. Sanity check of littlestone_dim; arXiv:2611.26721 (Littlestone dimension and its dual), Section 2 (singleton classes have dimension zero).

A class consisting of a single function X → Bool has Littlestone dimension 0.
-/

theorem littlestone_dim_singleton {X : Type*} (h : X → Bool) :
    littlestone_dim ({h} : Set (X → Bool)) = 0 := by
  refine le_antisymm ?_ bot_le
  apply iSup₂_le
  intro d hd
  cases d with
  | zero => simp
  | succ d =>
    exfalso
    obtain ⟨x, h0, h1⟩ := hd
    have ne : ∀ (S : Set (X → Bool)) (k : ℕ), littlestone_shatters S k → S.Nonempty := by
      intro S k
      induction k generalizing S with
      | zero => exact id
      | succ k ih =>
        rintro ⟨y, hy, _⟩
        obtain ⟨g, hg, _⟩ := ih _ hy
        exact ⟨g, hg⟩
    obtain ⟨g0, hg0, hg0x⟩ := ne _ _ h0
    obtain ⟨g1, hg1, hg1x⟩ := ne _ _ h1
    rw [Set.mem_singleton_iff] at hg0 hg1
    subst hg0 hg1
    rw [hg0x] at hg1x
    exact Bool.false_ne_true hg1x
