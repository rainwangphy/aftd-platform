import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# permutation_partial_assignment_card_bound_of_switching

Topic: graphs   Node: 7d602237741e

Provenance: helper lemma. Switching/counting helper for OP-306 and EJC 14 (2007) R63, DOI 10.37236/981, Theorem 1. Independent finite-cardinality formalization; no external Lean proof is reused.

If a finite set of permutations is closed under undoing any one forced assignment by an image swap, its number extending an injective partial assignment, multiplied by the relevant falling factorial, is at most its total cardinality.
-/

theorem permutation_partial_assignment_card_bound_of_switching
    {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (f : α → α) (hf : Set.InjOn f (↑D : Set α))
    (A : Finset (Equiv.Perm α))
    (hA : ∀ a ∈ D, ∀ τ ∈ A, τ a = f a →
      ∀ y, Equiv.swap y (f a) * τ ∈ A) :
    (Fintype.card α).descFactorial D.card *
      (A.filter (fun τ => ∀ a ∈ D, τ a = f a)).card ≤ A.card := by
  classical
  have step : ∀ S ⊆ D, ∀ a ∈ D, a ∉ S →
      (Fintype.card α - S.card) *
        (A.filter (fun τ => ∀ b ∈ insert a S, τ b = f b)).card ≤
          (A.filter (fun τ => ∀ b ∈ S, τ b = f b)).card := by
    intro S hSD a ha haS
    let R : Finset α := Finset.univ \ S.image f
    let B := A.filter (fun τ => ∀ b ∈ insert a S, τ b = f b)
    let C := A.filter (fun τ => ∀ b ∈ S, τ b = f b)
    let g : α × Equiv.Perm α → Equiv.Perm α :=
      fun z => Equiv.swap z.1 (f a) * z.2
    have hB : ∀ τ ∈ B, τ ∈ A ∧ ∀ b ∈ insert a S, τ b = f b := by
      intro τ hτ
      exact Finset.mem_filter.mp hτ
    have hmap : Set.MapsTo g (↑(R ×ˢ B) : Set _) ↑C := by
      rintro ⟨y, τ⟩ hz
      obtain ⟨hy, hτ⟩ := Finset.mem_product.mp hz
      obtain ⟨hτA, hτfix⟩ := hB τ hτ
      apply Finset.mem_filter.mpr
      refine ⟨hA a ha τ hτA (hτfix a (Finset.mem_insert_self _ _)) y, ?_⟩
      intro b hb
      change Equiv.swap y (f a) (τ b) = f b
      rw [hτfix b (Finset.mem_insert_of_mem hb)]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        exact (Finset.mem_sdiff.mp hy).2
          (Finset.mem_image.mpr ⟨b, hb, h⟩)
      · intro h
        exact haS ((hf (hSD hb) ha h) ▸ hb)
    have hginj : Set.InjOn g (↑(R ×ˢ B) : Set _) := by
      rintro ⟨y, τ⟩ hz ⟨z, υ⟩ hw heq
      have hτ := (hB τ (Finset.mem_product.mp hz).2).2 a (Finset.mem_insert_self _ _)
      have hυ := (hB υ (Finset.mem_product.mp hw).2).2 a (Finset.mem_insert_self _ _)
      have hyz : y = z := by
        have h := congrArg (fun σ : Equiv.Perm α => σ a) heq
        simpa [g, Equiv.Perm.mul_apply, hτ, hυ] using h
      subst z
      have hτυ : τ = υ := by
        apply Equiv.ext
        intro b
        have h := congrArg (fun σ : Equiv.Perm α => Equiv.swap y (f a) (σ b)) heq
        simpa [g, Equiv.Perm.mul_apply] using h
      exact Prod.ext rfl hτυ
    have hcard := Finset.card_le_card_of_injOn g hmap hginj
    have hR : R.card = Fintype.card α - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Finset.card_image_of_injOn]
      exact Set.InjOn.mono hSD hf
    simpa only [Finset.card_product, hR] using hcard
  have main : ∀ S ⊆ D,
      (Fintype.card α).descFactorial S.card *
        (A.filter (fun τ => ∀ a ∈ S, τ a = f a)).card ≤ A.card := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | @insert a S haS ih =>
      intro hsub
      have hSD : S ⊆ D := (Finset.subset_insert _ _).trans hsub
      have haD := hsub (Finset.mem_insert_self _ _)
      have hs := Nat.mul_le_mul_left ((Fintype.card α).descFactorial S.card)
        (step S hSD a haD haS)
      rw [Finset.card_insert_of_notMem haS, Nat.descFactorial_succ]
      nlinarith [ih hSD]
  exact main D (fun _ h => h)
