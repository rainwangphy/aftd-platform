import AFTD.Prelude

/-!
# prioritized_borel_compact_isolated_paths_finite

Topic: automata   Node: 614e7870aefc

Provenance: helper lemma. IN-829: compactness route to finite compatible plays.

A closed set of infinite paths over a compact discrete alphabet is finite if each of its paths is uniquely determined within the set by a finite prefix.
-/

theorem prioritized_borel_compact_isolated_paths_finite
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
    (S : Set (ℕ → A)) (hclosed : IsClosed S)
    (hisolate : ∀ f ∈ S, ∃ n : ℕ, ∀ g ∈ S, (∀ i < n, g i = f i) → g = f) :
    S.Finite := by
  have hc : IsCompact S := hclosed.isCompact
  apply hc.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro f hf
  obtain ⟨n, hn⟩ := hisolate f hf
  let U : Set (ℕ → A) := {g | ∀ i < n, g i = f i}
  have hUopen : IsOpen U := by
    have he : U = ⋂ i ∈ Finset.range n, {g : ℕ → A | g i = f i} := by
      ext g
      simp [U]
    rw [he]
    apply isOpen_biInter_finset
    intro i hi
    change IsOpen ((fun g : ℕ → A => g i) ⁻¹' ({f i} : Set A))
    exact (isOpen_discrete ({f i} : Set A)).preimage (continuous_apply i)
  refine ⟨U,hUopen,?_⟩
  ext g
  constructor
  · rintro ⟨hgU,hgS⟩
    exact hn g hgS hgU
  · intro hg
    have heq : g=f := by simpa using hg
    subst g
    exact ⟨by simp [U],hf⟩
