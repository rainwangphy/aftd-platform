import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.Supp
import AFTD.Kb.Tcs.V

/-!
# card_full_support_le_of_injective

Topic: quantum   Node: da755e794b6b

Provenance: helper lemma. arXiv:2610.04621 Lemma 5

If the coordinate projection v ↦ (v.1|_S, v.2|_S) onto a subset S of physical pairs is injective on a translate a + L, then the number of full-support vectors in a + L (vectors with supp v = univ) is at most 3^|S|.
-/

open scoped Pointwise in
/-- An injective projection onto S physical pairs limits the number of full-support vectors on any translate to at most 3^|S|. -/
lemma card_full_support_le_of_injective {k : ℕ}
    (L : Submodule (F 2) (V k 2)) (S : Finset (Fin k)) (a : V k 2)
    (hinj : Set.InjOn (fun v : V k 2 => ((fun (s : S) => v.1 s.1), (fun (s : S) => v.2 s.1))) (a +ᵥ (L : Set (V k 2)))) :
    Nat.card {v ∈ a +ᵥ (L : Set (V k 2)) | supp v = Finset.univ} ≤ 3 ^ S.card := by
  let β := { p : F 2 × F 2 // p.1 ≠ 0 ∨ p.2 ≠ 0 }
  have hβ : Nat.card β = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let A := {v ∈ a +ᵥ (L : Set (V k 2)) | supp v = Finset.univ}
  let f : A → (S → β) := fun ⟨v, hv⟩ s => ⟨(v.1 s.1, v.2 s.1), by
    have hsupp : supp v = Finset.univ := hv.2
    have hs : s.1 ∈ supp v := by rw [hsupp]; exact Finset.mem_univ s.1
    dsimp [supp] at hs
    rw [Set.mem_toFinset] at hs
    exact hs⟩
  have hf_inj : Function.Injective f := by
    intro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
    apply Subtype.ext
    apply hinj hv1.1 hv2.1
    ext : 1
    · ext s
      have := congr_fun heq s
      exact congr_arg (fun (p : β) => p.1.1) this
    · ext s
      have := congr_fun heq s
      exact congr_arg (fun (p : β) => p.1.2) this
  have hle := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_fun, hβ, Nat.card_eq_finsetCard] at hle
  exact hle
