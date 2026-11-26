import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BinaryChain

/-!
# op874_binary_chain_contains_permutation

Topic: graphs   Node: 9f7729dec74d

Provenance: helper lemma. Finite local-phase reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

If each two-state constraint on a finite path contains a bijection, their composition contains a bijection.
-/

theorem op874_binary_chain_contains_permutation
    (rs : List (Bool → Bool → Prop))
    (hr : ∀ R ∈ rs, ∃ f : Bool → Bool, f false ≠ f true ∧ ∀ a, R a (f a)) :
    ∃ f : Bool → Bool, f false ≠ f true ∧ ∀ a, op874_binary_chain rs a (f a) := by
  induction rs with
  | nil => exact ⟨id, by decide, by intro a; rfl⟩
  | cons R rs ih =>
    obtain ⟨f, hfne, hf⟩ := hr R (by simp)
    obtain ⟨g, hgne, hg⟩ := ih (by intro T hT; exact hr T (by simp [hT]))
    have hginj : Function.Injective g := by
      intro a b hab
      cases a <;> cases b <;> simp_all
    refine ⟨fun a => g (f a), ?_, ?_⟩
    · intro he; exact hfne (hginj he)
    · intro a; exact ⟨f a, hf a, hg (f a)⟩
