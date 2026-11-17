import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_game_maintains_prefix

Topic: online_algorithms   Node: c2a17b3e58fc

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemma 2.3

A bounded online-coloring strategy preserves graph colorability, the board-size bound, and empty predecessor and color sets at all future positions.
-/

theorem op869_game_preserves_invariant {S M R : Type} (goal invariant : S → Prop)
    (legal : S → M → Prop) (valid : S → M → R → Prop) (next : S → M → R → S)
    (hstep : ∀ s a r, invariant s → legal s a → valid s a r → invariant (next s a r))
    (fuel : ℕ) (s : S) (hinv : invariant s)
    (hgame : op869_sequential_goal_game goal legal valid next fuel s) :
    op869_sequential_goal_game (fun s => invariant s ∧ goal s) legal valid next fuel s := by
  induction fuel generalizing s with
  | zero => simp [op869_sequential_goal_game] at hgame
  | succ fuel ih =>
    simp only [op869_sequential_goal_game] at hgame ⊢
    obtain ⟨a, ha, hnext⟩ := hgame
    refine ⟨a, ha, ?_⟩
    intro r hr
    have hi := hstep s a r hinv ha hr
    rcases hnext r hr with hgoal | hrest
    · exact Or.inl ⟨hi,hgoal⟩
    · exact Or.inr (ih _ hi hrest)

def op869_prefix_invariant {n : ℕ} (k : ℕ) (s : Op869SequentialState n) : Prop :=
  s.i ≤ n ∧ (op869_graph_from_predecessors s.P).Colorable k ∧
    ∀ a, s.i ≤ a.val → s.P a = ∅ ∧ s.C a = ∅

theorem op869_legal_step_preserves_prefix {n : ℕ} (k D t : ℕ)
    (s : Op869SequentialState n) (S : Finset (Fin n)) (colors : Finset ℕ)
    (hinv : op869_prefix_invariant k s)
    (hlegal : op869_sequential_legal k D s S)
    (hvalid : op869_sequential_valid t s S colors) :
    op869_prefix_invariant k (op869_sequential_next s S colors) := by
  classical
  obtain ⟨hi,hS,hcolor,hdegree⟩ := hlegal
  simp only [op869_sequential_next, dif_pos hi, op869_prefix_invariant,
    Op869SequentialState.i, Op869SequentialState.P, Op869SequentialState.C]
  constructor
  · omega
  · constructor
    · exact hcolor
    · intro a ha
      have hai : a ≠ (⟨s.i,hi⟩ : Fin n) := by
        intro heq
        have hv := congrArg Fin.val heq
        change a.val = s.i at hv
        omega
      have hbefore := hinv.2.2 a (by omega)
      constructor
      · simpa [Function.update_of_ne hai] using hbefore.1
      · simpa [Function.update_of_ne hai] using hbefore.2



theorem op869_empty_prefix_invariant (n k : ℕ) (hk : 1 ≤ k) :
    op869_prefix_invariant k (⟨0, (fun _ : Fin n => ∅), (fun _ : Fin n => ∅)⟩ : Op869SequentialState n) := by
  refine ⟨by change 0 ≤ n; omega, ?_, ?_⟩
  · refine ⟨SimpleGraph.Coloring.mk (fun _ : Fin n => (⟨0, by omega⟩ : Fin k)) ?_⟩
    intro a b hadj
    change (a < b ∧ a ∈ (∅ : Finset (Fin n))) ∨ (b < a ∧ b ∈ (∅ : Finset (Fin n))) at hadj
    simp at hadj
  · simp

/-- Fresh-prefix invariant for sequential online games. -/
theorem op869_game_maintains_prefix {n : ℕ} (k D t : ℕ) (goal : Op869SequentialState n → Prop)
    (fuel : ℕ) (s : Op869SequentialState n) (hinv : op869_prefix_invariant k s)
    (hgame : op869_sequential_goal_game goal (op869_sequential_legal k D)
      (op869_sequential_valid t) op869_sequential_next fuel s) :
    op869_sequential_goal_game (fun s => op869_prefix_invariant k s ∧ goal s)
      (op869_sequential_legal k D) (op869_sequential_valid t) op869_sequential_next fuel s := by
  apply op869_game_preserves_invariant goal (op869_prefix_invariant k)
    (op869_sequential_legal k D) (op869_sequential_valid t) op869_sequential_next
    (op869_legal_step_preserves_prefix k D t) fuel s hinv hgame
