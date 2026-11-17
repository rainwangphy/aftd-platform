import AFTD.Prelude

/-!
# op1525_finite_action_fiber_stabilizer_or_complement

Topic: combinatorics   Node: beda86860f25

Provenance: helper lemma. Elementary orbit-fiber cardinality, used for the paired-transversal bottleneck in OP-1525.

If a finite group preserves a signature and each signature fiber has at most as many elements as the group, then any point whose complement has the same signature either has a nontrivial stabilizer or can be moved to its complement.
-/

theorem op1525_finite_action_fiber_stabilizer_or_complement
    {G X Y : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq Y]
    [MulAction G X] (signature : X → Y) (complement : X → X)
    (hinv : ∀ (g : G) (x : X), signature (g • x) = signature x)
    (hcomp : ∀ x : X, signature (complement x) = signature x)
    (hsize : ∀ x : X, Fintype.card {y : X // signature y = signature x} ≤ Fintype.card G)
    (x : X) :
    (∃ g : G, g ≠ 1 ∧ g • x = x) ∨ (∃ g : G, g • x = complement x) := by
  classical
  by_cases h : ∃ g : G, g ≠ 1 ∧ g • x = x
  · exact Or.inl h
  · right
    have htriv : ∀ g : G, g • x = x → g = 1 := by
      intro g hg
      by_contra hne
      exact h ⟨g, hne, hg⟩
    let φ : G → {y : X // signature y = signature x} := fun g => ⟨g • x, hinv g x⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      have heq : a • x = b • x := congrArg Subtype.val hab
      have hfix : (a⁻¹ * b) • x = x := by
        have hx := congrArg (fun z : X => a⁻¹ • z) heq
        simpa [mul_smul] using hx.symm
      have hab' := htriv (a⁻¹ * b) hfix
      exact inv_mul_eq_one.mp hab'
    have hcard : Fintype.card G = Fintype.card {y : X // signature y = signature x} :=
      le_antisymm (Fintype.card_le_of_injective φ hinj) (hsize x)
    have hsurj : Function.Surjective φ :=
      ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩).2
    obtain ⟨g, hg⟩ := hsurj ⟨complement x, hcomp x⟩
    exact ⟨g, congrArg Subtype.val hg⟩
