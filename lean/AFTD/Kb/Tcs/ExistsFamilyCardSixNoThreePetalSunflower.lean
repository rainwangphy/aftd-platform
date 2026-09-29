import AFTD.Prelude
import AFTD.Kb.Tcs.IsSunflower

/-!
# exists_family_card_six_no_three_petal_sunflower

Topic: combinatorics   Node: ee435aab4bf0

There is a finite family F of six 2-element subsets of a 6-element ground set (namely the six edges of two disjoint triangles) such that no 3-element subfamily of F is a sunflower with any kernel: for every G ⊆ F with |G| = 3 and every set C, G is not a sunflower with kernel C. Since |F| = 6 > 2!·2 = 4, this shows that the folklore threshold k!·s is not a valid bound in the sunflower lemma; the threshold must grow as k!·s^k.
-/

/-- Two disjoint triangles give six 2-element sets with no 3-petal sunflower, refuting the folklore threshold k!·s for the sunflower lemma. -/
theorem exists_family_card_six_no_three_petal_sunflower :
    ∃ F : Finset (Finset (Fin 6)), (∀ A ∈ F, A.card = 2) ∧ F.card = 6 ∧
      (∀ G ⊆ F, G.card = 3 → ∀ C, ¬ IsSunflower G C) := by
  refine ⟨{{0,1},{1,2},{0,2},{3,4},{4,5},{3,5}}, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro G hGF hG3 C hC
    have hpair : ∀ a ∈ ({{0,1},{1,2},{0,2},{3,4},{4,5},{3,5}} : Finset (Finset (Fin 6))),
        ∀ b ∈ ({{0,1},{1,2},{0,2},{3,4},{4,5},{3,5}} : Finset (Finset (Fin 6))),
        ∀ d ∈ ({{0,1},{1,2},{0,2},{3,4},{4,5},{3,5}} : Finset (Finset (Fin 6))),
        a ≠ b → a ≠ d → b ≠ d → ¬(a ∩ b = a ∩ d ∧ a ∩ b = b ∩ d) := by decide
    obtain ⟨a, b, d, hab, had, hbd, hGeq⟩ := Finset.card_eq_three.mp hG3
    have ha : a ∈ G := by rw [hGeq]; simp
    have hb : b ∈ G := by rw [hGeq]; simp
    have hd : d ∈ G := by rw [hGeq]; simp
    have h1 : a ∩ b = C := hC.2 a ha b hb hab
    have h2 : a ∩ d = C := hC.2 a ha d hd had
    have h3 : b ∩ d = C := hC.2 b hb d hd hbd
    exact hpair a (hGF ha) b (hGF hb) d (hGF hd) hab had hbd ⟨by rw [h1, h2], by rw [h1, h3]⟩
