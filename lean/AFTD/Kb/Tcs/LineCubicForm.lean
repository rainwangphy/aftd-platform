import AFTD.Prelude

/-!
# line_cubic_form

Topic: quantum   Node: cca2271643ad

The line cubic form f_n on (ZMod 2)^n is the sum over i from 0 to n-3 of the product of adjacent triples x_i * x_{i+1} * x_{i+2}.
-/

/-- The line cubic form f_n(x) = ∑ x_i x_{i+1} x_{i+2} on (ZMod 2)^n. -/
def line_cubic_form (n : ℕ) (x : Fin n → ZMod 2) : ZMod 2 := ∑ i : Fin (n - 2),
    have h0 : i.val < n := by omega
    have h1 : i.val + 1 < n := by omega
    have h2 : i.val + 2 < n := by omega
    x ⟨i.val, h0⟩ * x ⟨i.val + 1, h1⟩ * x ⟨i.val + 2, h2⟩
