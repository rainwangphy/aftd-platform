import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiSubintervalFixedPoint
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tarski_box_query_le_small

Topic: algorithms   Node: f21d30854af9

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Brute force on small boxes: if every box in dimension k has at most M points, then every box query is answerable within M queries — and in particular tarski_box_query_le n k M holds, so the new definition is inhabited (non-vacuous).
-/

def tarski_box_query_le_small_tree {n k : ℕ} (x₀ : Fin k → Fin n) :
    List (Fin k → Fin n) → TarskiQueryTree n k
  | [] => .output x₀
  | x :: xs => .query x (fun fx => if fx = x then .output x else tarski_box_query_le_small_tree x₀ xs)

theorem tarski_box_query_le_small_cost_le {n k : ℕ} (x₀ : Fin k → Fin n) (L : List (Fin k → Fin n))
    (f : (Fin k → Fin n) → Fin k → Fin n) :
    TarskiQueryTree.cost f (tarski_box_query_le_small_tree x₀ L) ≤ L.length := by
  induction L with
  | nil =>
    simp [tarski_box_query_le_small_tree, TarskiQueryTree.cost]
  | cons x xs ih =>
    simp only [tarski_box_query_le_small_tree, TarskiQueryTree.cost, List.length_cons]
    split_ifs with h
    · simp [TarskiQueryTree.cost]
    · omega

theorem tarski_box_query_le_small_run_mem_and_fixed {n k : ℕ} (x₀ : Fin k → Fin n) (L : List (Fin k → Fin n))
    (f : (Fin k → Fin n) → Fin k → Fin n) (h : ∃ z ∈ L, f z = z) :
    TarskiQueryTree.run f (tarski_box_query_le_small_tree x₀ L) ∈ L ∧
    f (TarskiQueryTree.run f (tarski_box_query_le_small_tree x₀ L)) =
      TarskiQueryTree.run f (tarski_box_query_le_small_tree x₀ L) := by
  induction L with
  | nil =>
    rcases h with ⟨z, hz, -⟩
    cases hz
  | cons x xs ih =>
    simp only [tarski_box_query_le_small_tree, TarskiQueryTree.run]
    split_ifs with hfx
    · simp [TarskiQueryTree.run, hfx]
    · rcases h with ⟨z, hz, hfz⟩
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact False.elim (hfx hfz)
      · have ⟨h1, h2⟩ := ih ⟨z, hz, hfz⟩
        exact ⟨List.mem_cons_of_mem x h1, h2⟩

/-- Boxes small enough to enumerate are solved by querying all their points. -/
theorem tarski_box_query_le_small (n k M : ℕ) [NeZero n]
    (hM : ∀ a b : Fin k → Fin n, a ≤ b → (∏ j : Fin k, ((b j : ℕ) - (a j : ℕ) + 1)) ≤ M) :
    tarski_box_query_le n k M := by
  intro a b hab
  use tarski_box_query_le_small_tree a (Finset.Icc a b).toList
  intro f hf ha hb
  have h_fp := tarski_subinterval_fixed_point n k f hf a b hab ha hb
  rcases h_fp with ⟨x, hax, hxb, hfx⟩
  have hx_mem : x ∈ (Finset.Icc a b).toList := by
    rw [Finset.mem_toList, Finset.mem_Icc]
    exact ⟨hax, hxb⟩
  have h_run := tarski_box_query_le_small_run_mem_and_fixed a (Finset.Icc a b).toList f ⟨x, hx_mem, hfx⟩
  have h_mem_box : TarskiQueryTree.run f (tarski_box_query_le_small_tree a (Finset.Icc a b).toList) ∈ Finset.Icc a b := by
    rw [← Finset.mem_toList]
    exact h_run.1
  rw [Finset.mem_Icc] at h_mem_box
  refine ⟨h_mem_box.1, h_mem_box.2, h_run.2, ?_⟩
  have h_cost := tarski_box_query_le_small_cost_le a (Finset.Icc a b).toList f
  rw [Finset.length_toList] at h_cost
  have h_card_le : (Finset.Icc a b).card ≤ M := by
    rw [Pi.card_Icc]
    have h1 : ∀ j, (Finset.Icc (a j) (b j)).card = (b j : ℕ) - (a j : ℕ) + 1 := by
      intro j
      rw [Fin.card_Icc]
      have : a j ≤ b j := hab j
      omega
    simp_rw [h1]
    exact hM a b hab
  exact le_trans h_cost h_card_le
