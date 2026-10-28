import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsIElement

/-!
# bmi_is_left_unit_b

Topic: proof_theory   Node: 4489abadc574

Provenance: formalization of a published result. Source: arXiv:2610.37108 Proposition 3.1 -- Finite BM-algebras and fixed-point combinators

Let $(A, \cdot)$ be a finite magma equipped with a $B$-element $B$ and an $I$-element $I$. Then $B$ is a left unit: $Bx = x$ for all $x \in A$.
-/

/-- In any finite magma with a B-element and an I-element, B is a left unit. -/
theorem bmi_is_left_unit_b {A : Type*} [Mul A] [Fintype A]
    (B I : A) (hB : bmi_is_b_element B) (hI : bmi_is_i_element I) :
    ∀ x : A, B * x = x := by
  let L : A → (A → A) := fun a x => a * x
  let S := Set.range L
  let phi : S → S := fun ⟨f, _⟩ => ⟨L (f I), ⟨f I, rfl⟩⟩
  have h_surj : Function.Surjective phi := by
    rintro ⟨g, ⟨a, rfl⟩⟩
    refine ⟨⟨L (B * a), ⟨B * a, rfl⟩⟩, ?_⟩
    ext x
    dsimp [phi, L]
    rw [hB a I x, hI x]
  have h_inj : Function.Injective phi := Finite.injective_iff_surjective.mpr h_surj
  have h_inj2 : Function.Injective (phi ∘ phi) := h_inj.comp h_inj
  let vB : S := ⟨L B, ⟨B, rfl⟩⟩
  let vI : S := ⟨L I, ⟨I, rfl⟩⟩
  have h_eq : (phi ∘ phi) vB = (phi ∘ phi) vI := by
    ext x
    change (phi (phi vB)).1 x = (phi (phi vI)).1 x
    dsimp [phi, L, vB, vI]
    rw [hB I I x]
    repeat rw [hI]
  have hv : vB = vI := h_inj2 h_eq
  intro x
  have hL : L B x = L I x := congr_fun (congr_arg Subtype.val hv) x
  dsimp [L] at hL
  rw [hL, hI x]
