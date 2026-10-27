import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerClassPaletteOfCount
import AFTD.Kb.Tcs.CyclePowerClassLabelPeriodOfEndpointOverlap

/-!
# cycle_power_class_label_period_of_bounded_endpoint_overlap

Topic: combinatorics   Node: 7f195fa0b950

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

For bounded Boolean classes with complete distinct palettes, endpoint overlap forces the root labels to repeat after the class radius.
-/

open Finset

theorem cycle_power_class_label_period_of_bounded_endpoint_overlap
    (D t : ℕ) (x : ℤ → ℕ → Bool) (ell : ℤ → Fin t)
    (hcount : ∀ v : ℤ, (range D).sum
      (fun a => (x (v-(a : ℤ)) a).toNat) = t)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < D → b < D → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ)))
    (hoverlap : ∀ (p : ℤ) (q : ℕ), 1 ≤ q → q < D →
      x (p+(q : ℤ)) (D-1-q) = true →
      ∃ a : ℕ, a < q ∧ x (p+(q : ℤ)) (D-q+a) = true ∧
        x (p+(D : ℤ)) a = true) :
    Function.Periodic ell (D : ℤ) := by
  let S : ℤ → ℤ → Prop := fun p v =>
    ∃ a : ℕ, a < D ∧ v = p+(a : ℤ) ∧ x p a = true
  apply cycle_power_class_label_period_of_endpoint_overlap (D : ℤ) S ell
  · intro v s
    obtain ⟨a, ha, hx, hs⟩ := cycle_power_class_palette_of_count D t x ell hcount hsep v s
    exact ⟨v-(a : ℤ), ⟨a, ha, by omega, hx⟩, hs⟩
  · intro p q v hp hq he
    obtain ⟨a, ha, hva, hxa⟩ := hp
    obtain ⟨b, hb, hvb, hxb⟩ := hq
    have hpa : p = v-(a : ℤ) := by omega
    have hqb : q = v-(b : ℤ) := by omega
    by_cases hab : a=b
    · subst b; omega
    subst p q
    exact False.elim (hsep v a b ha hb hab hxa hxb he)
  · intro p
    rintro ⟨a, ha, he, hx⟩
    omega
  · intro p q hne hq
    obtain ⟨b, hb, hvb, hxb⟩ := hq
    let r := D-1-b
    have hD : 0 < D := by omega
    have hr0 : 1 ≤ r := by dsimp [r]; omega
    have hrD : r < D := by dsimp [r]; omega
    have hqr : q=p+(r : ℤ) := by dsimp [r]; omega
    have hage : D-1-r=b := by dsimp [r]; omega
    have hx : x (p+(r : ℤ)) (D-1-r) = true := by rw [← hqr, hage]; exact hxb
    obtain ⟨a, ha, hxa, hxnew⟩ := hoverlap p r hr0 hrD hx
    refine ⟨p+(D : ℤ)+(a : ℤ), ?_, ?_⟩
    · refine ⟨D-r+a, by omega, ?_, ?_⟩
      · dsimp [r] at *; omega
      · simpa only [hqr] using hxa
    · exact ⟨a, by omega, by omega, hxnew⟩
