import AFTD.Prelude

/-!
# op874_extend_bits_along_paths

Topic: graphs   Node: b734a5ee3a64

Provenance: helper lemma. Finite partial bit assignment extended by reverse reachability.

If every vertex can reach a prescribed finite set, any Boolean assignment on that set extends so that every outside vertex has an outgoing edge to a vertex of the opposite bit.
-/

theorem op874_extend_bits_along_paths {X : Type*} [Fintype X] [DecidableEq X]
    (R : X → X → Prop) (S : Finset X) (b0 : X → Bool)
    (hreach : ∀ x, ∃ y ∈ S, Relation.ReflTransGen R x y) :
    ∃ b : X → Bool, (∀ x ∈ S, b x = b0 x) ∧
      ∀ x, x ∉ S → ∃ y, R x y ∧ b x ≠ b y := by
  classical
  have bridge (S : Finset X) (a b : X) (hp : Relation.ReflTransGen R a b)
      (ha : a ∉ S) (hb : b ∈ S) : ∃ u v, u ∉ S ∧ v ∈ S ∧ R u v := by
    induction hp with
    | refl => exact (ha hb).elim
    | @tail c d hac hcd ih =>
      by_cases hc : c ∈ S
      · exact ih hc
      · exact ⟨c, d, hc, hb, hcd⟩
  have aux (n : ℕ) : ∀ S : Finset X, (Finset.univ \ S).card = n → ∀ b0 : X → Bool,
      (∀ x, ∃ y ∈ S, Relation.ReflTransGen R x y) →
      ∃ b : X → Bool, (∀ x ∈ S, b x = b0 x) ∧
        ∀ x, x ∉ S → ∃ y, R x y ∧ b x ≠ b y := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn b0 hreach
      by_cases hall : S = Finset.univ
      · refine ⟨b0, by simp, ?_⟩
        intro x hx
        exact (hx (hall ▸ Finset.mem_univ x)).elim
      · have hnon : (Finset.univ \ S).Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro h
          apply hall
          ext z
          have : z ∉ Finset.univ \ S := by rw [h]; simp
          simpa using this
        obtain ⟨z, hz⟩ := hnon
        have hzs : z ∉ S := (Finset.mem_sdiff.mp hz).2
        obtain ⟨y, hy, hp⟩ := hreach z
        obtain ⟨u, v, hu, hv, huv⟩ := bridge S z y hp hzs hy
        let T := insert u S
        let b1 := Function.update b0 u (!b0 v)
        have hlt : (Finset.univ \ T).card < n := by
          rw [← hn]
          apply Finset.card_lt_card
          apply Finset.ssubset_iff_subset_ne.mpr
          constructor
          · intro w hw
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hw ⊢
            exact fun hs => hw (Finset.mem_insert_of_mem hs)
          · intro heq
            have hu0 : u ∈ Finset.univ \ S := by simp [hu]
            have hu1 : u ∉ Finset.univ \ T := by simp [T]
            exact hu1 (heq ▸ hu0)
        have hreachT : ∀ x, ∃ y ∈ T, Relation.ReflTransGen R x y := by
          intro x
          obtain ⟨y, hy, hp⟩ := hreach x
          exact ⟨y, Finset.mem_insert_of_mem hy, hp⟩
        obtain ⟨b, hb, hm⟩ := ih _ hlt T rfl b1 hreachT
        refine ⟨b, ?_, ?_⟩
        · intro w hw
          have hwu : w ≠ u := fun he => hu (he ▸ hw)
          rw [hb w (Finset.mem_insert_of_mem hw)]
          simp [b1, hwu]
        · intro w hw
          by_cases hwu : w = u
          · subst w
            refine ⟨v, huv, ?_⟩
            have hvu : v ≠ u := fun he => hu (he ▸ hv)
            rw [hb u (by simp [T]), hb v (Finset.mem_insert_of_mem hv)]
            simp [b1, hvu]
          · apply hm w
            simp [T, hw, hwu]
  exact aux _ S rfl b0 hreach
