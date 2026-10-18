import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryComplexityLe
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeRun

/-!
# tarski_query_complexity_dim_le_succ

Topic: algorithms   Node: 3adcd8c43638

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Dimension reduction: any query algorithm finding a fixed point in dimension k + 1 in at most q queries can be simulated in dimension k with at most q queries.
-/

def tarski_query_complexity_dim_le_succ_embed_tree {n k : ℕ} :
    TarskiQueryTree n (k + 1) → TarskiQueryTree n k
  | .output z => .output (fun i => z (Fin.castSucc i))
  | .query z next =>
    .query (fun i => z (Fin.castSucc i))
      (fun y => tarski_query_complexity_dim_le_succ_embed_tree (next (Fin.snoc y (z (Fin.last k)))))

def tarski_query_complexity_dim_le_succ_lift_map {n k : ℕ} (f : (Fin k → Fin n) → (Fin k → Fin n)) :
    (Fin (k + 1) → Fin n) → (Fin (k + 1) → Fin n) :=
  fun z => Fin.snoc (f (fun i => z (Fin.castSucc i))) (z (Fin.last k))

theorem tarski_query_complexity_dim_le_succ_lift_map_mono {n k : ℕ}
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f) :
    Monotone (tarski_query_complexity_dim_le_succ_lift_map f) := by
  intro x y hxy i
  induction i using Fin.lastCases with
  | last =>
    simp only [tarski_query_complexity_dim_le_succ_lift_map, Fin.snoc_last]
    exact hxy (Fin.last k)
  | cast i =>
    simp only [tarski_query_complexity_dim_le_succ_lift_map, Fin.snoc_castSucc]
    exact hf (fun j => hxy (Fin.castSucc j)) i

theorem tarski_query_complexity_dim_le_succ_embed_tree_run {n k : ℕ}
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (t : TarskiQueryTree n (k + 1)) :
    (tarski_query_complexity_dim_le_succ_embed_tree t).run f =
      fun i => (t.run (tarski_query_complexity_dim_le_succ_lift_map f)) (Fin.castSucc i) := by
  induction t with
  | output z =>
    rfl
  | query z next ih =>
    simp only [tarski_query_complexity_dim_le_succ_embed_tree, TarskiQueryTree.run]
    have hlift : Fin.snoc (f (fun i => z (Fin.castSucc i))) (z (Fin.last k)) =
        tarski_query_complexity_dim_le_succ_lift_map f z := rfl
    rw [hlift]
    exact ih (tarski_query_complexity_dim_le_succ_lift_map f z)

theorem tarski_query_complexity_dim_le_succ_embed_tree_cost {n k : ℕ}
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (t : TarskiQueryTree n (k + 1)) :
    (tarski_query_complexity_dim_le_succ_embed_tree t).cost f =
      t.cost (tarski_query_complexity_dim_le_succ_lift_map f) := by
  induction t with
  | output z =>
    rfl
  | query z next ih =>
    simp only [tarski_query_complexity_dim_le_succ_embed_tree, TarskiQueryTree.cost]
    have hlift : Fin.snoc (f (fun i => z (Fin.castSucc i))) (z (Fin.last k)) =
        tarski_query_complexity_dim_le_succ_lift_map f z := rfl
    rw [hlift]
    rw [ih (tarski_query_complexity_dim_le_succ_lift_map f z)]

theorem tarski_query_complexity_dim_le_succ_embed_tree_fixed {n k : ℕ}
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (t : TarskiQueryTree n (k + 1))
    (hfix : tarski_query_complexity_dim_le_succ_lift_map f
        (t.run (tarski_query_complexity_dim_le_succ_lift_map f)) =
      t.run (tarski_query_complexity_dim_le_succ_lift_map f)) :
    f ((tarski_query_complexity_dim_le_succ_embed_tree t).run f) =
      (tarski_query_complexity_dim_le_succ_embed_tree t).run f := by
  have hrun := tarski_query_complexity_dim_le_succ_embed_tree_run f t
  rw [hrun]
  apply funext
  intro i
  have h := congr_fun hfix (Fin.castSucc i)
  dsimp [tarski_query_complexity_dim_le_succ_lift_map] at h
  rw [Fin.snoc_castSucc] at h
  exact h

/-- Dimension reduction: any query algorithm finding a fixed point in dimension k + 1 in at most q queries can be simulated in dimension k with at most q queries. -/
theorem tarski_query_complexity_dim_le_succ (n k q : ℕ)
    (h : tarski_query_complexity_le n (k + 1) q) :
    tarski_query_complexity_le n k q := by
  obtain ⟨t, ht⟩ := h
  refine ⟨tarski_query_complexity_dim_le_succ_embed_tree t, fun f hf => ?_⟩
  have hmono := tarski_query_complexity_dim_le_succ_lift_map_mono f hf
  obtain ⟨hfix, hcost⟩ := ht (tarski_query_complexity_dim_le_succ_lift_map f) hmono
  refine ⟨tarski_query_complexity_dim_le_succ_embed_tree_fixed f t hfix, ?_⟩
  rw [tarski_query_complexity_dim_le_succ_embed_tree_cost]
  exact hcost
