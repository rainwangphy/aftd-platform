import AFTD.Prelude
import AFTD.Kb.Tcs.ShellsortHPass

/-!
# shellsort_h_pass_example

Topic: algorithms   Node: ecb9382c6642

Provenance: helper lemma. arXiv:2611.27671, Section 2 (definition of the h-pass); a computed instance.

Sanity check of the h-pass: the 2-pass of the array 5, 4, 3, 2, 1, 0 sorts the even positions (values 5, 3, 1) and the odd positions (4, 2, 0) separately, giving 1, 0, 3, 2, 5, 4.
-/

theorem shellsort_h_pass_example :
    (List.ofFn (shellsort_h_pass 2 (![5, 4, 3, 2, 1, 0] : Fin 6 → ℕ))) = [1, 0, 3, 2, 5, 4] := by
  decide
