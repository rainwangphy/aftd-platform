import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_game_sequential_compose

Topic: online_algorithms   Node: ec776d6f364e

Provenance: helper lemma. Sequential composition for the finite adversary game of arXiv:2610.41516 Section 2.

If an adversary can force a chosen intermediate state property within fuel₁ moves, and can then force K colors within fuel₂ further moves from every such state, it can force K colors within fuel₁+fuel₂ moves.
-/

def op869_sequential_goal_game {S M R : Type} (goal : S → Prop) (legal : S → M → Prop)
    (valid : S → M → R → Prop) (next : S → M → R → S) : ℕ → S → Prop
  | 0, _ => False
  | fuel+1, state =>
      ∃ move, legal state move ∧ ∀ response, valid state move response →
        goal (next state move response) ∨ op869_sequential_goal_game goal legal valid next fuel (next state move response)

lemma op869_sequential_fuel_mono_internal {S M R : Type} (goal : S → Prop) (legal : S → M → Prop)
    (valid : S → M → R → Prop) (next : S → M → R → S) (n n' : ℕ) (s : S)
    (hn : n ≤ n') (h : op869_sequential_goal_game goal legal valid next n s) :
    op869_sequential_goal_game goal legal valid next n' s := by
  induction n generalizing n' s with
  | zero => simp [op869_sequential_goal_game] at h
  | succ n ih =>
    cases n' with
    | zero => omega
    | succ n' =>
      simp only [op869_sequential_goal_game] at h ⊢
      obtain ⟨move, hm, hnext⟩ := h
      refine ⟨move, hm, ?_⟩
      intro r hr
      rcases hnext r hr with hgoal | hgame
      · exact Or.inl hgoal
      · exact Or.inr (ih n' _ (by omega) hgame)

theorem op869_sequential_compose_internal {S M R : Type} (g₁ g₂ : S → Prop) (legal : S → M → Prop)
    (valid : S → M → R → Prop) (next : S → M → R → S) (n m : ℕ) (s : S)
    (hfirst : op869_sequential_goal_game g₁ legal valid next n s)
    (hsecond : ∀ s, g₁ s → op869_sequential_goal_game g₂ legal valid next m s) :
    op869_sequential_goal_game g₂ legal valid next (n+m) s := by
  induction n generalizing s with
  | zero => simp [op869_sequential_goal_game] at hfirst
  | succ n ih =>
    simp only [op869_sequential_goal_game] at hfirst
    simp only [Nat.succ_add, op869_sequential_goal_game]
    obtain ⟨move, hm, hnext⟩ := hfirst
    refine ⟨move, hm, ?_⟩
    intro r hr
    rcases hnext r hr with hgoal | hgame
    · right
      exact op869_sequential_fuel_mono_internal g₂ legal valid next m (n+m) _ (by omega) (hsecond _ hgoal)
    · right
      exact ih _ hgame

structure Op869SequentialState (n : ℕ) where
  i : ℕ
  P : Fin n → Finset (Fin n)
  C : Fin n → Finset ℕ

def op869_sequential_goal_internal {n : ℕ} (K : ℕ) (s : Op869SequentialState n) : Prop :=
  K ≤ ((Finset.univ.filter (fun a : Fin n => a.val < s.i)).biUnion s.C).card

def op869_sequential_legal {n : ℕ} (k D : ℕ) (s : Op869SequentialState n) (S : Finset (Fin n)) : Prop :=
  ∃ hi : s.i < n, (∀ a ∈ S, a.val < s.i) ∧
    let P' := Function.update s.P (⟨s.i, hi⟩ : Fin n) S
    (op869_graph_from_predecessors P').Colorable k ∧
      ∀ a, op869_predecessor_postdegree P' a ≤ D

def op869_sequential_valid {n : ℕ} (t : ℕ) (s : Op869SequentialState n)
    (S : Finset (Fin n)) (c : Finset ℕ) : Prop :=
  c.card = t ∧ ∀ a ∈ S, Disjoint (s.C a) c

def op869_sequential_next {n : ℕ} (s : Op869SequentialState n) (S : Finset (Fin n))
    (c : Finset ℕ) : Op869SequentialState n :=
  if hi : s.i < n then ⟨s.i+1, Function.update s.P (⟨s.i,hi⟩ : Fin n) S,
    Function.update s.C (⟨s.i,hi⟩ : Fin n) c⟩ else s

theorem op869_bounded_sequential_equiv_internal {n : ℕ} (k t K D fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ) :
    op869_sequential_goal_game (op869_sequential_goal_internal K) (op869_sequential_legal k D)
      (op869_sequential_valid t) op869_sequential_next fuel ⟨i,P,C⟩ ↔
    op869_bounded_adversary_forces k t K D fuel i P C := by
  classical
  induction fuel generalizing i P C with
  | zero => simp [op869_sequential_goal_game, op869_bounded_adversary_forces]
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_sequential_goal_game, op869_bounded_adversary_forces, dif_pos hi]
      simp only [op869_sequential_legal, op869_sequential_valid, op869_sequential_next, op869_sequential_goal_internal,
        dif_pos hi, Nat.lt_succ_iff, Op869SequentialState.i, Op869SequentialState.P, Op869SequentialState.C]
      simp only [ih]
      aesop
    · simp [op869_sequential_goal_game, op869_bounded_adversary_forces, op869_sequential_legal, hi]

/-- Sequential composition for the bounded online-coloring adversary game. -/
theorem op869_bounded_game_sequential_compose {n : ℕ} (k t K D : ℕ) (goal : Op869SequentialState n → Prop)
    (fuel₁ fuel₂ i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (hfirst : op869_sequential_goal_game goal (op869_sequential_legal k D) (op869_sequential_valid t)
      op869_sequential_next fuel₁ ⟨i,P,C⟩)
    (hsecond : ∀ s : Op869SequentialState n, goal s →
      op869_bounded_adversary_forces k t K D fuel₂ s.i s.P s.C) :
    op869_bounded_adversary_forces k t K D (fuel₁+fuel₂) i P C := by
  apply (op869_bounded_sequential_equiv_internal k t K D (fuel₁+fuel₂) i P C).mp
  apply op869_sequential_compose_internal goal (op869_sequential_goal_internal K) (op869_sequential_legal k D)
    (op869_sequential_valid t) op869_sequential_next fuel₁ fuel₂ ⟨i,P,C⟩ hfirst
  intro s hs
  exact (op869_bounded_sequential_equiv_internal k t K D fuel₂ s.i s.P s.C).mpr (hsecond s hs)
