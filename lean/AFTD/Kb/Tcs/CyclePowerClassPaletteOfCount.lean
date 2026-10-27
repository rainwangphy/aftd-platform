import AFTD.Prelude

/-!
# cycle_power_class_palette_of_count

Topic: combinatorics   Node: 8c212fc270d3

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

Exactly t active classes with distinct labels in Fin t use every label at each vertex.
-/

open Finset

theorem cycle_power_class_palette_of_count
    (D t : ℕ) (x : ℤ → ℕ → Bool) (ell : ℤ → Fin t)
    (hcount : ∀ v : ℤ, (range D).sum
      (fun a => (x (v-(a : ℤ)) a).toNat) = t)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < D → b < D → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ))) :
    ∀ (v : ℤ) (s : Fin t), ∃ a : ℕ, a < D ∧
      x (v-(a : ℤ)) a = true ∧ ell (v-(a : ℤ)) = s := by
  classical
  intro v s
  let A := (range D).filter (fun (a : ℕ) => x (v-(a : ℤ)) a = true)
  have hc : A.card = t := by
    rw [← hcount v]
    dsimp [A]
    rw [card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro a ha
    cases hx : x (v-(a : ℤ)) a <;> simp [hx]
  have hinj : Set.InjOn (fun a : ℕ => ell (v-(a : ℤ))) (A : Set ℕ) := by
    intro a ha b hb hab
    change a ∈ A at ha
    change b ∈ A at hb
    have ha' : a < D ∧ x (v-(a : ℤ)) a = true := by
      simpa only [A, mem_filter, mem_range] using ha
    have hb' : b < D ∧ x (v-(b : ℤ)) b = true := by
      simpa only [A, mem_filter, mem_range] using hb
    by_contra hne
    exact hsep v a b ha'.1 hb'.1 hne ha'.2 hb'.2 hab
  have hi : (A.image (fun a : ℕ => ell (v-(a : ℤ)))).card = t := by
    rw [card_image_of_injOn hinj, hc]
  have hu : A.image (fun a : ℕ => ell (v-(a : ℤ))) = univ :=
    eq_univ_of_card _ (by simpa using hi)
  have hs : s ∈ A.image (fun a : ℕ => ell (v-(a : ℤ))) := by rw [hu]; simp
  obtain ⟨a, ha, he⟩ := mem_image.mp hs
  have ha' : a < D ∧ x (v-(a : ℤ)) a = true := by
    simpa only [A, mem_filter, mem_range] using ha
  exact ⟨a, ha'.1, ha'.2, he⟩
