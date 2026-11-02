import AFTD.Prelude

/-!
# maxcut_single_vertex_gluing_abstract

Topic: equilibria   Node: a633d3dab0c2

Provenance: helper lemma. General gluing mechanism for the Max-k-Cut strong-equilibrium existence problem OP-85.

For an additively separable game whose player sets cover all players and intersect only at a shared player, stability on each piece implies stability of the combined payoff: whenever any player changes, a changing player fails to improve the sum of its two piece payoffs. Each piece payoff vanishes outside its own player set.
-/

theorem maxcut_single_vertex_gluing_abstract
    {V C : Type} (σ : V → C) (A B : Set V) (o : V)
    (hA : o ∈ A) (hB : o ∈ B)
    (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hinter : ∀ v, v ∈ A → v ∈ B → v = o)
    (a b : (V → C) → V → ℕ)
    (ha0 : ∀ p v, v ∉ A → a p v = 0)
    (hb0 : ∀ p v, v ∉ B → b p v = 0)
    (hstableA : ∀ τ, (∃ v, v ∈ A ∧ τ v ≠ σ v) →
      ∃ v, v ∈ A ∧ τ v ≠ σ v ∧ a τ v ≤ a σ v)
    (hstableB : ∀ τ, (∃ v, v ∈ B ∧ τ v ≠ σ v) →
      ∃ v, v ∈ B ∧ τ v ≠ σ v ∧ b τ v ≤ b σ v) :
    ∀ τ, (∃ v, τ v ≠ σ v) →
      ∃ v, τ v ≠ σ v ∧ a τ v + b τ v ≤ a σ v + b σ v := by
  classical
  intro τ hchanged
  by_contra hbad
  have hgain : ∀ v, τ v ≠ σ v → a σ v + b σ v < a τ v + b τ v := by
    intro v hv
    by_contra hn
    exact hbad ⟨v, hv, by omega⟩
  have left_root : ∀ v, v ∈ A → τ v ≠ σ v → a τ v ≤ a σ v → v = o := by
    intro v hv hdiff hle
    by_contra hne
    have hnot : v ∉ B := fun hmem => hne (hinter v hv hmem)
    have hg := hgain v hdiff
    rw [hb0 τ v hnot, hb0 σ v hnot] at hg
    omega
  have right_root : ∀ v, v ∈ B → τ v ≠ σ v → b τ v ≤ b σ v → v = o := by
    intro v hv hdiff hle
    by_contra hne
    have hnot : v ∉ A := fun hmem => hne (hinter v hmem hv)
    have hg := hgain v hdiff
    rw [ha0 τ v hnot, ha0 σ v hnot] at hg
    omega
  have horoot : τ o ≠ σ o := by
    obtain ⟨v, hv⟩ := hchanged
    rcases hcover v with hvA | hvB
    · obtain ⟨w, hwA, hwd, hwle⟩ := hstableA τ ⟨v, hvA, hv⟩
      have : w = o := left_root w hwA hwd hwle
      simpa [this] using hwd
    · obtain ⟨w, hwB, hwd, hwle⟩ := hstableB τ ⟨v, hvB, hv⟩
      have : w = o := right_root w hwB hwd hwle
      simpa [this] using hwd
  obtain ⟨x, hxA, hxd, hxle⟩ := hstableA τ ⟨o, hA, horoot⟩
  obtain ⟨y, hyB, hyd, hyle⟩ := hstableB τ ⟨o, hB, horoot⟩
  have hx : x = o := left_root x hxA hxd hxle
  have hy : y = o := right_root y hyB hyd hyle
  subst x
  subst y
  have hg := hgain o horoot
  omega
