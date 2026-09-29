import AFTD.Prelude

/-!
# KarpReducible

Topic: np_completeness   Node: a2b63fab8a66

A language L over an alphabet Γ Karp-reduces (polynomial-time many-one reduces) to a language L' over an alphabet Γ' if there is a function f from words over Γ to words over Γ' that is computed by a multi-tape Turing machine in polynomial time in the length of the input word, and such that for every word w over Γ, w ∈ L if and only if f w ∈ L'.
-/

/-- Karp (polynomial-time many-one) reduction between two languages, via a polynomial-time computable map of words. -/
def KarpReducible (Γ Γ' : Type) (L : Language Γ) (L' : Language Γ') : Prop := ∃ f : List Γ → List Γ',
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ → List Γ) (id : List Γ' → List Γ') f) ∧
      ∀ w : List Γ, w ∈ L ↔ f w ∈ L'
