import AFTD.Prelude

/-!
# integer_quadratic_coloring_divisor

Topic: combinatorics   Node: c812e5ee802a

Provenance: helper lemma. Divisibility reduction for the rational quadratic route to OP-1482.

If an integer coloring avoids the false length-3 and true length-17 quadratic patterns with curvature q m, then another integer coloring avoids the same patterns with curvature q.
-/

theorem integer_quadratic_coloring_divisor (q m : ℕ) (f : ℤ → Bool) (h3 : ∀ a b : ℤ, ¬ ∀ k : Fin 3, f (((q * m : ℕ) : ℤ) * (k.val : ℤ)^2 + a*k.val+b) = false) (h17 : ∀ a b : ℤ, ¬ ∀ k : Fin 17, f (((q * m : ℕ) : ℤ) * (k.val : ℤ)^2 + a*k.val+b) = true) : ∃ g : ℤ → Bool, (∀ a b : ℤ, ¬ ∀ k : Fin 3, g ((q : ℤ) * (k.val : ℤ)^2 + a*k.val+b) = false) ∧ (∀ a b : ℤ, ¬ ∀ k : Fin 17, g ((q : ℤ) * (k.val : ℤ)^2 + a*k.val+b) = true) := by
  have algebra (k : ℕ) (a b : ℤ) :
      (m : ℤ)*((q : ℤ)*(k : ℤ)^2 + a*k+b) =
        ((q*m:ℕ):ℤ)*(k : ℤ)^2 + ((m : ℤ)*a)*k + (m : ℤ)*b := by
    push_cast
    ring
  refine ⟨fun z => f ((m : ℤ)*z), ?_, ?_⟩
  · intro a b hh
    apply h3 ((m : ℤ)*a) ((m : ℤ)*b)
    intro k
    have hk := hh k
    change f ((m : ℤ)*((q : ℤ)*(k.val : ℤ)^2+a*k.val+b)) = false at hk
    rw [algebra k.val a b] at hk
    exact hk
  · intro a b hh
    apply h17 ((m : ℤ)*a) ((m : ℤ)*b)
    intro k
    have hk := hh k
    change f ((m : ℤ)*((q : ℤ)*(k.val : ℤ)^2+a*k.val+b)) = true at hk
    rw [algebra k.val a b] at hk
    exact hk
