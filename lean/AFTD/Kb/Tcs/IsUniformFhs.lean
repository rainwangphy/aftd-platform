import AFTD.Prelude

/-!
# is_uniform_fhs

Topic: information   Node: 6edaa383ba58

Provenance: formalization of a published result. Source: arXiv:2611.11747, Section 1

A frequency hopping sequence X : Fin (k * s) → Fin s is uniform if each symbol f ∈ Fin s occurs exactly k times in X.
-/

/-- A frequency hopping sequence of period k * s is uniform if each symbol appears k times -/
def is_uniform_fhs (k s : ℕ) (X : Fin (k * s) → Fin s) : Prop := ∀ f : Fin s, (Finset.univ.filter (fun j => X j = f)).card = k
