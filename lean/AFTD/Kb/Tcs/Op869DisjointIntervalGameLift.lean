import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GoalGameStrategySimulation
import AFTD.Kb.Tcs.Op869SplicedColorsUpdate
import AFTD.Kb.Tcs.Op869DisjointSpliceBipartition
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_disjoint_interval_game_lift

Topic: online_algorithms   Node: b3d5523b0564

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemmas 2.3 and 2.4

A local k-colorable online strategy can be played on a fresh disconnected interval after any k-colorable earlier graph, without changing its responses or local goal.
-/

def op869_interval_related {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (s₁ : Op869SequentialState n) (s₂ : Op869SequentialState m) : Prop :=
  s₂.i = offset+s₁.i ∧ ∃ ext : Fin n → Finset (Fin m),
    (∀ a x, x ∈ ext a → x.val < offset) ∧
    s₂.P = op869_splice_preds offset h baseP ext s₁.P ∧
    s₂.C = op869_splice_colors offset h baseC s₁.C

theorem op869_interval_game_strategy_lift {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (k₁ k₂ D₁ D₂ t : ℕ)
    (g₁ : Op869SequentialState n → Prop) (g₂ : Op869SequentialState m → Prop)
    (hgoal : ∀ s₁ s₂, op869_interval_related offset h baseP baseC s₁ s₂ → g₁ s₁ → g₂ s₂)
    (hlegal : ∀ s₁ s₂, op869_interval_related offset h baseP baseC s₁ s₂ →
      ∀ S, op869_sequential_legal k₁ D₁ s₁ S →
        ∃ T : Finset (Fin m), (∀ x ∈ T, x.val < offset) ∧
          op869_sequential_legal k₂ D₂ s₂ (T ∪ S.map (op869_offset_emb offset h)))
    (fuel : ℕ) (s₁ : Op869SequentialState n) (s₂ : Op869SequentialState m)
    (hrel : op869_interval_related offset h baseP baseC s₁ s₂)
    (hgame : op869_sequential_goal_game g₁ (op869_sequential_legal k₁ D₁)
      (op869_sequential_valid t) op869_sequential_next fuel s₁) :
    op869_sequential_goal_game g₂ (op869_sequential_legal k₂ D₂)
      (op869_sequential_valid t) op869_sequential_next fuel s₂ := by
  classical
  apply op869_goal_game_strategy_simulation g₁ g₂ (op869_sequential_legal k₁ D₁)
    (op869_sequential_legal k₂ D₂) (op869_sequential_valid t) (op869_sequential_valid t)
    op869_sequential_next op869_sequential_next (op869_interval_related offset h baseP baseC) hgoal
  · intro s₁ s₂ hrel S hlocal
    obtain ⟨T, hT, hglobal⟩ := hlegal s₁ s₂ hrel S hlocal
    refine ⟨T ∪ S.map (op869_offset_emb offset h), hglobal, ?_⟩
    intro colors hvalid
    rcases hrel with ⟨hindex, ext, hext, hP, hC⟩
    have hvalidlocal : op869_sequential_valid t s₁ S colors := by
      constructor
      · exact hvalid.1
      · apply op869_spliced_valid_response offset h baseC s₁.C S T colors
        simpa [← hC] using hvalid.2
    refine ⟨colors, hvalidlocal, ?_⟩
    have hi₁ : s₁.i < n := by rcases hlocal with ⟨hi, _⟩; exact hi
    have hi₂ : s₂.i < m := by omega
    let i : Fin n := ⟨s₁.i, hi₁⟩
    have hemb : op869_offset_emb offset h i = (⟨s₂.i, hi₂⟩ : Fin m) := by
      apply Fin.ext
      change offset+s₁.i = s₂.i
      omega
    unfold op869_interval_related
    constructor
    · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.i]
      omega
    · refine ⟨Function.update ext i T, ?_, ?_, ?_⟩
      · intro a x hx
        by_cases hai : a = i
        · subst a
          exact hT x (by simpa using hx)
        · apply hext a x
          simpa [Function.update_of_ne hai] using hx
      · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.P]
        rw [hP, ← hemb]
        exact (op869_spliced_predecessors_update offset h baseP ext s₁.P i T S).symm
      · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.C]
        rw [hC, ← hemb]
        exact (op869_spliced_colors_update offset h baseC s₁.C i colors).symm
  · exact hrel
  · exact hgame


def op869_disjoint_interval_related {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (s₁ : Op869SequentialState n) (s₂ : Op869SequentialState m) : Prop :=
  s₂.i = offset+s₁.i ∧
    s₂.P = op869_splice_preds offset h baseP (fun _ => ∅) s₁.P ∧
    s₂.C = op869_splice_colors offset h baseC s₁.C



theorem op869_disjoint_interval_start {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (hclear : ∀ x, offset ≤ x.val → baseP x = ∅ ∧ baseC x = ∅) :
    op869_disjoint_interval_related offset h baseP baseC
      ⟨0, (fun _ => ∅), (fun _ => ∅)⟩ ⟨offset, baseP, baseC⟩ := by
  classical
  constructor
  · simp
  · constructor
    · funext x
      by_cases hx : offset ≤ x.val ∧ x.val < offset+n
      · have hc := (hclear x hx.1).1
        simp [op869_splice_preds, hx, hc]
      · simp [op869_splice_preds, hx]
    · funext x
      by_cases hx : offset ≤ x.val ∧ x.val < offset+n
      · have hc := (hclear x hx.1).2
        simp [op869_splice_colors, hx, hc]
      · simp [op869_splice_colors, hx]

/-- Disconnected-copy strategy transport for the bipartite gadget. -/
theorem op869_disjoint_interval_game_lift {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (k D t : ℕ)
    (hclear : ∀ x, offset ≤ x.val → baseP x = ∅)
    (hbase : (op869_graph_from_predecessors baseP).Colorable k)
    (g₁ : Op869SequentialState n → Prop) (g₂ : Op869SequentialState m → Prop)
    (hgoal : ∀ s₁ s₂, op869_disjoint_interval_related offset h baseP baseC s₁ s₂ → g₁ s₁ → g₂ s₂)
    (fuel : ℕ) (s₁ : Op869SequentialState n) (s₂ : Op869SequentialState m)
    (hrel : op869_disjoint_interval_related offset h baseP baseC s₁ s₂)
    (hgame : op869_sequential_goal_game g₁ (op869_sequential_legal k D)
      (op869_sequential_valid t) op869_sequential_next fuel s₁) :
    op869_sequential_goal_game g₂ (op869_sequential_legal k m)
      (op869_sequential_valid t) op869_sequential_next fuel s₂ := by
  classical
  apply op869_goal_game_strategy_simulation g₁ g₂ (op869_sequential_legal k D)
    (op869_sequential_legal k m) (op869_sequential_valid t) (op869_sequential_valid t)
    op869_sequential_next op869_sequential_next
    (op869_disjoint_interval_related offset h baseP baseC) hgoal
  · intro s₁ s₂ hrel S hlocal
    rcases hrel with ⟨hindex,hP,hC⟩
    obtain ⟨hi₁,hS,hcolor,hdegree⟩ := hlocal
    have hi₂ : s₂.i < m := by omega
    let i : Fin n := ⟨s₁.i,hi₁⟩
    have hemb : op869_offset_emb offset h i = (⟨s₂.i,hi₂⟩ : Fin m) := by
      apply Fin.ext
      change offset+s₁.i = s₂.i
      omega
    have hext0 : Function.update (fun _ : Fin n => (∅ : Finset (Fin m))) i ∅ =
        (fun _ : Fin n => (∅ : Finset (Fin m))) := by
      funext a
      by_cases ha : a = i <;> simp [ha]
    have huP := op869_spliced_predecessors_update offset h baseP (fun _ => ∅) s₁.P i ∅ S
    rw [hext0] at huP
    simp only [Finset.empty_union] at huP
    refine ⟨S.map (op869_offset_emb offset h), ?_, ?_⟩
    · refine ⟨hi₂, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
        have ha' := hS a ha
        change offset+a.val < s₂.i
        omega
      · rw [hP, ← hemb, ← huP]
        exact op869_disjoint_splice_colorable offset h baseP _ k hclear hbase hcolor
      · rw [hP, ← hemb, ← huP]
        intro x
        unfold op869_predecessor_postdegree
        simpa using Finset.card_le_univ (Finset.univ.filter (fun y : Fin m =>
          x < y ∧ x ∈ op869_splice_preds offset h baseP (fun _ => ∅)
            (Function.update s₁.P i S) y))
    · intro colors hvalid
      have hvalidlocal : op869_sequential_valid t s₁ S colors := by
        constructor
        · exact hvalid.1
        · apply op869_spliced_valid_response offset h baseC s₁.C S ∅ colors
          simpa [← hC] using hvalid.2
      refine ⟨colors,hvalidlocal,?_⟩
      unfold op869_disjoint_interval_related
      constructor
      · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.i]
        omega
      · constructor
        · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.P]
          rw [hP, ← hemb]
          exact huP.symm
        · simp only [op869_sequential_next, dif_pos hi₁, dif_pos hi₂, Op869SequentialState.C]
          rw [hC, ← hemb]
          exact (op869_spliced_colors_update offset h baseC s₁.C i colors).symm
  · exact hrel
  · exact hgame
