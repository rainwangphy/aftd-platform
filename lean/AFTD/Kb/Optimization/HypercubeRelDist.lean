import AFTD.Prelude

/-!
# hypercube_rel_dist

Topic: submodular   Node: 1b7a80f70e81

Provenance: formalization of a published result. Source: arXiv:2611.02374 Def. 2.4

The relative Hamming distance between two functions f and g from the hypercube Fin n → Bool into Fin (k + 1) is the number of inputs where f and g differ divided by 2^n.
-/

/-- Relative Hamming distance between two functions from Fin n → Bool to Fin (k + 1). -/
noncomputable def hypercube_rel_dist {n k : ℕ} (f g : (Fin n → Bool) → Fin (k + 1)) : ℝ :=
  ((Finset.univ.filter (fun x => f x ≠ g x)).card : ℝ) / (2 ^ n : ℝ)
