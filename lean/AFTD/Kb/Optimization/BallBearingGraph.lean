import AFTD.Prelude

/-!
# ballBearingGraph

Topic: integer_programming   Node: af9f752d2a75

Provenance: formalization of a published result. Source: arXiv:2611.17386 Section 2

For any natural number k, the Ball Bearing graph ballBearingGraph k has vertex set Fin k × Fin 5. Two distinct vertices (j₁, v₁) and (j₂, v₂) are adjacent if and only if: (1) j₁ = j₂ and the unordered pair {v₁, v₂} is one of {0, 1}, {1, 2}, {1, 3}, {2, 3}, or {3, 4}; or (2) (j₁.val + 1) % k = j₂.val and (v₁, v₂) is (0, 0), (1, 0), or (4, 2); or (3) (j₂.val + 1) % k = j₁.val and (v₂, v₁) is (0, 0), (1, 0), or (4, 2).
-/

/-- The Ball Bearing graph BB(k) on 5k vertices Fin k × Fin 5 arranged in k five-vertex gadgets in a ring. -/
def ballBearingGraph (k : ℕ) : SimpleGraph (Fin k × Fin 5) := {
  Adj := fun x y => x ≠ y ∧
    ((x.1 = y.1 ∧
      ((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0) ∨
       (x.2 = 1 ∧ y.2 = 2) ∨ (x.2 = 2 ∧ y.2 = 1) ∨
       (x.2 = 1 ∧ y.2 = 3) ∨ (x.2 = 3 ∧ y.2 = 1) ∨
       (x.2 = 2 ∧ y.2 = 3) ∨ (x.2 = 3 ∧ y.2 = 2) ∨
       (x.2 = 3 ∧ y.2 = 4) ∨ (x.2 = 4 ∧ y.2 = 3))) ∨
     ((x.1.val + 1) % k = y.1.val ∧
      ((x.2 = 0 ∧ y.2 = 0) ∨ (x.2 = 1 ∧ y.2 = 0) ∨ (x.2 = 4 ∧ y.2 = 2))) ∨
     ((y.1.val + 1) % k = x.1.val ∧
      ((y.2 = 0 ∧ x.2 = 0) ∨ (y.2 = 1 ∧ x.2 = 0) ∨ (y.2 = 4 ∧ x.2 = 2)))),
  symm := ⟨fun {x y} h => by
    obtain ⟨hne, h⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, by tauto⟩
    · right; right; exact ⟨h1, h2⟩
    · right; left; exact ⟨h1, h2⟩⟩,
  loopless := ⟨fun {x} h => h.1 rfl⟩ }
