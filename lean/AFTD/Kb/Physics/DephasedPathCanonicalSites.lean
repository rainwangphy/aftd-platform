import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathRainbowSite

/-!
# dephased_path_canonical_sites

Topic: quantum_mechanics   Node: 16ab9e50077e

Provenance: helper lemma. Explicit selection derived from the 812-state reduced-path certificate (22652), checked on all ordinary paths through ten vertices (22664) and sampled arbitrary endpoint leaves through fifteen vertices (22663).

Split a color word at equal-color edges and choose the first odd-offset rainbow site in each odd-length segment, when one exists.
-/

noncomputable def dephased_path_canonical_sites (n : ℕ) (color : Fin n → Fin 4) : Finset (Fin n) := open scoped Classical in Finset.univ.filter fun j => ∃ a b : Fin n, a.val ≤ j.val ∧ j.val ≤ b.val ∧ (∀ x : Fin n, x.val + 1 = a.val → color x = color a) ∧ (∀ x : Fin n, b.val + 1 = x.val → color b = color x) ∧ (∀ x y : Fin n, x.val + 1 = y.val → a.val ≤ x.val → y.val ≤ b.val → color x ≠ color y) ∧ (b.val - a.val + 1) % 2 = 1 ∧ (j.val - a.val) % 2 = 1 ∧ dephased_path_rainbow_site n color j ∧ ∀ k : Fin n, a.val ≤ k.val → k.val < j.val → (k.val - a.val) % 2 = 1 → ¬ dephased_path_rainbow_site n color k
