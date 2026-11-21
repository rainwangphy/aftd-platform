import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.MaxVertexDiscrepancy

/-!
# op_2130_terminal_discrepancy_le_prefix_max

Topic: online_algorithms   Node: b70eb1279779

Provenance: helper lemma. OP-2130: convert a final discrepancy witness into a prefix maximum witness

For equally long request and orientation lists, the maximum absolute discrepancy in the final state is no greater than the maximum over all prefix states.
-/

private lemma op2130_fold_member_scan {α β : Type} (f : α → β → α) (xs : List β) (a : α) :
    xs.foldl f a ∈ xs.scanl f a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.scanl_cons]
    exact List.mem_cons_of_mem _ (ih (f a x))

lemma op2130_max_fold_ge (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simpa only [List.foldl_cons] using le_trans (le_max_left a x) (ih (max a x))

lemma op2130_max_fold_member (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldl_cons]
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) (op2130_max_fold_ge ys (max a x))
    · exact ih (max a y) hx

theorem op_2130_terminal_discrepancy_le_prefix_max (n : ℕ) (edges : List (Fin n × Fin n)) (signs : List Bool) (hlen : edges.length = signs.length) : max_vertex_discrepancy n ((edges.zip signs).foldl (fun d (e, b) => carpool_step n d e b) (fun _ => 0)) ≤ carpool_max_discrepancy n edges signs := by
  unfold carpool_max_discrepancy carpool_discrepancies
  apply op2130_max_fold_member
  apply List.mem_map.mpr
  refine ⟨_, op2130_fold_member_scan _ _ _, rfl⟩
