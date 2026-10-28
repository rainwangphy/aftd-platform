import AFTD.Prelude

/-!
# bool_sum_eq_card_filter

Topic: combinatorics   Node: 0a05cbb9b7bf

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

A Boolean profile summed through toNat over a natural range counts exactly its true offsets in that range.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem bool_sum_eq_card_filter (N : ℕ) (b : ℕ → Bool) :
    (range N).sum (fun a => (b a).toNat) = ((range N).filter (fun a => b a = true)).card := by
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro a ha
  cases b a <;> rfl
