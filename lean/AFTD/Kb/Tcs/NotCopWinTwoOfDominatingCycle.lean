import AFTD.Prelude
import AFTD.Kb.Tcs.HasCopWinStrategy
import AFTD.Kb.Tcs.CopsCanWinFrom
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.G

/-!
# not_cop_win_two_of_dominating_cycle

Topic: graphs   Node: 8fb13203497d

Provenance: original. Related work: refutes `cop_win_two_of_dominating_cycle`

The statement `cop_win_two_of_dominating_cycle` is false: The theorem is FALSE. A concrete counterexample is the Petersen graph P on 10 vertices:
1. P contains an induced 5-cycle C = (v₀, v₁, v₂, v₃, v₄) with m = 5 ≥ 3.
2. C dominates P: the outer vertices are on C, and every inner vertex u_i is adjacent to v_i ∈ C.
3. However, the cop number of the Petersen graph is 3 (Aigner and Fromme, 1984, Theorem 3: the Petersen graph is the unique smallest graph with cop number 3). Thus 2 cops do not have a winning strategy on P: `¬ HasCopWinStrategy P 2`.

The statement in attempt #5490 was adapted from Gupta–Pradhan–Swain (arXiv:2610.20129) where the graphs were assumed to be claw-free. The author omitted `IsClawFree G` (and hole length restrictions), believing any dominating cycle allows 2 cops to win. But the Petersen graph has claws (e.g. {v₀, v₁, v₄, u₀} is an induced claw K_{1,3}), which allows the robber to evade 2 cops indefinitely.
-/

set_option maxHeartbeats 4000000

/-- Adjacency of the Petersen graph on `Fin 5 × Bool`. -/
def not_cop_win_two_of_dominating_cycle_petersen_adj (a b : Fin 5 × Bool) : Prop :=
  (a.2 = false ∧ b.2 = false ∧ (b.1 = a.1 + 1 ∨ a.1 = b.1 + 1)) ∨
  (a.2 = true ∧ b.2 = true ∧ (b.1 = a.1 + 2 ∨ a.1 = b.1 + 2)) ∨
  (a.1 = b.1 ∧ a.2 ≠ b.2)

instance not_cop_win_two_of_dominating_cycle_petersen_adj_decidable :
    DecidableRel not_cop_win_two_of_dominating_cycle_petersen_adj := fun a b => by
  unfold not_cop_win_two_of_dominating_cycle_petersen_adj
  infer_instance

theorem not_cop_win_two_of_dominating_cycle_petersen_adj_symm :
    Std.Symm not_cop_win_two_of_dominating_cycle_petersen_adj := ⟨by decide⟩

theorem not_cop_win_two_of_dominating_cycle_petersen_adj_irrefl :
    Std.Irrefl not_cop_win_two_of_dominating_cycle_petersen_adj := ⟨by decide⟩

/-- The Petersen graph on `Fin 5 × Bool`: `(i, false)` on the outer 5-cycle,
`(i, true)` on the inner pentagram, and a spoke joining `(i, false)` to `(i, true)`. -/
def not_cop_win_two_of_dominating_cycle_petersen : SimpleGraph (Fin 5 × Bool) :=
  ⟨not_cop_win_two_of_dominating_cycle_petersen_adj,
   not_cop_win_two_of_dominating_cycle_petersen_adj_symm,
   not_cop_win_two_of_dominating_cycle_petersen_adj_irrefl⟩

instance not_cop_win_two_of_dominating_cycle_petersen_decidable_adj :
    DecidableRel not_cop_win_two_of_dominating_cycle_petersen.Adj :=
  not_cop_win_two_of_dominating_cycle_petersen_adj_decidable

/-- A cop/robber position is safe when the robber is neither on nor adjacent to any cop. -/
def not_cop_win_two_of_dominating_cycle_robber_safe
    (C : Fin 2 → Fin 5 × Bool) (R : Fin 5 × Bool) : Prop :=
  ∀ i, C i ≠ R ∧ ¬ not_cop_win_two_of_dominating_cycle_petersen.Adj (C i) R

instance not_cop_win_two_of_dominating_cycle_robber_safe_decidable
    (C : Fin 2 → Fin 5 × Bool) (R : Fin 5 × Bool) :
    Decidable (not_cop_win_two_of_dominating_cycle_robber_safe C R) := by
  unfold not_cop_win_two_of_dominating_cycle_robber_safe
  infer_instance

/-- Every two-cop position on the Petersen graph leaves a safe robber position. -/
theorem not_cop_win_two_of_dominating_cycle_exists_robber_safe :
    ∀ C : Fin 2 → Fin 5 × Bool,
      ∃ R, not_cop_win_two_of_dominating_cycle_robber_safe C R := by
  decide

/-- Safety is preserved: after any cop move there is a robber move restoring safety. -/
theorem not_cop_win_two_of_dominating_cycle_robber_safe_step :
    ∀ (C : Fin 2 → Fin 5 × Bool) (R : Fin 5 × Bool),
      not_cop_win_two_of_dominating_cycle_robber_safe C R →
      ∀ (C' : Fin 2 → Fin 5 × Bool),
        (∀ i, C' i = C i ∨ not_cop_win_two_of_dominating_cycle_petersen.Adj (C i) (C' i)) →
        ∃ R', (R' = R ∨ not_cop_win_two_of_dominating_cycle_petersen.Adj R R') ∧
          not_cop_win_two_of_dominating_cycle_robber_safe C' R' := by
  decide

/-- From a safe position the two cops never force a capture. -/
theorem not_cop_win_two_of_dominating_cycle_not_cops_win_from_safe :
    ∀ (C : Fin 2 → Fin 5 × Bool) (R : Fin 5 × Bool),
      not_cop_win_two_of_dominating_cycle_robber_safe C R →
      ¬ CopsCanWinFrom not_cop_win_two_of_dominating_cycle_petersen 2 C R := by
  intro C R hS hwin
  revert hS
  induction hwin with
  | capture C R hcap =>
      intro hS
      obtain ⟨i, hi⟩ := hcap
      exact (hS i).1 hi
  | step_capture C R C' hC hcap =>
      intro hS
      obtain ⟨i, hi⟩ := hcap
      rcases hC i with h | h
      · exact (hS i).1 (h.symm.trans hi)
      · exact (hS i).2 (hi ▸ h)
  | step C R C' hC hR ih =>
      intro hS
      obtain ⟨R', hR', hS'⟩ :=
        not_cop_win_two_of_dominating_cycle_robber_safe_step C R hS C' hC
      exact ih R' hR' hS'

/-- Two cops do not have a winning strategy on the Petersen graph. -/
theorem not_cop_win_two_of_dominating_cycle_petersen_not_has_cop_win_two :
    ¬ HasCopWinStrategy not_cop_win_two_of_dominating_cycle_petersen 2 := by
  rintro ⟨C₀, h⟩
  obtain ⟨R₀, hS⟩ := not_cop_win_two_of_dominating_cycle_exists_robber_safe C₀
  exact not_cop_win_two_of_dominating_cycle_not_cops_win_from_safe C₀ R₀ hS (h R₀)

/-- The outer 5-cycle of the Petersen graph, as a vertex map. -/
def not_cop_win_two_of_dominating_cycle_outer_vertex (i : Fin 5) : Fin 5 × Bool := (i, false)

theorem not_cop_win_two_of_dominating_cycle_outer_vertex_injective :
    Function.Injective not_cop_win_two_of_dominating_cycle_outer_vertex := by
  intro a b h
  simpa [not_cop_win_two_of_dominating_cycle_outer_vertex] using h

theorem not_cop_win_two_of_dominating_cycle_outer_vertex_adj_iff (a b : Fin 5) :
    not_cop_win_two_of_dominating_cycle_petersen.Adj
        (not_cop_win_two_of_dominating_cycle_outer_vertex a)
        (not_cop_win_two_of_dominating_cycle_outer_vertex b) ↔
      (SimpleGraph.cycleGraph 5).Adj a b := by
  unfold not_cop_win_two_of_dominating_cycle_outer_vertex
  fin_cases a <;> fin_cases b <;> decide

/-- The outer 5-cycle of the Petersen graph is an embedded copy of `cycleGraph 5`. -/
def not_cop_win_two_of_dominating_cycle_outer_cycle_embedding :
    SimpleGraph.cycleGraph 5 ↪g not_cop_win_two_of_dominating_cycle_petersen :=
  RelEmbedding.mk
    ⟨not_cop_win_two_of_dominating_cycle_outer_vertex,
     not_cop_win_two_of_dominating_cycle_outer_vertex_injective⟩
    (by intro a b; exact not_cop_win_two_of_dominating_cycle_outer_vertex_adj_iff a b)

/-- The outer 5-cycle dominates the Petersen graph. -/
theorem not_cop_win_two_of_dominating_cycle_outer_cycle_dominates :
    simple_graph_is_dominating not_cop_win_two_of_dominating_cycle_petersen
      (Set.range not_cop_win_two_of_dominating_cycle_outer_cycle_embedding) := by
  intro v
  obtain ⟨a, b⟩ := v
  cases b
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨(a, false), ⟨a, rfl⟩, Or.inr (Or.inr ⟨rfl, Bool.false_ne_true⟩)⟩

/-- The cop game is invariant under an equivalence of graphs: positions transport along `e`. -/
theorem not_cop_win_two_of_dominating_cycle_cops_win_from_equiv
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (e : V ≃ W) (hadj : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b) :
    ∀ (c : ℕ) (C : Fin c → V) (R : V),
      CopsCanWinFrom G c C R → CopsCanWinFrom G' c (fun i => e (C i)) (e R) := by
  intro c C R h
  induction h with
  | capture C R hcap =>
      obtain ⟨i, hi⟩ := hcap
      exact CopsCanWinFrom.capture _ _ ⟨i, by rw [hi]⟩
  | step_capture C R C' hC hcap =>
      obtain ⟨i, hi⟩ := hcap
      refine CopsCanWinFrom.step_capture _ _ (fun i => e (C' i)) ?_ ⟨i, by rw [hi]⟩
      intro i
      rcases hC i with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr ((hadj (C i) (C' i)).mpr h)
  | step C R C' hC hR ih =>
      refine CopsCanWinFrom.step _ _ (fun i => e (C' i)) ?_ ?_
      · intro i
        rcases hC i with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr ((hadj (C i) (C' i)).mpr h)
      · intro R' hR'
        rcases hR' with h | h
        · rw [h]
          exact ih R (Or.inl rfl)
        · have h' : G'.Adj (e R) (e (e.symm R')) := by rw [Equiv.apply_symm_apply]; exact h
          simpa using ih (e.symm R') (Or.inr ((hadj R (e.symm R')).mp h'))

/-- The Petersen graph lifted to an arbitrary universe. -/
def not_cop_win_two_of_dominating_cycle_ulift_petersen :
    SimpleGraph (ULift (Fin 5 × Bool)) where
  Adj a b := not_cop_win_two_of_dominating_cycle_petersen.Adj a.down b.down
  symm := ⟨fun a b h =>
    (SimpleGraph.symm not_cop_win_two_of_dominating_cycle_petersen).symm a.down b.down h⟩
  loopless := ⟨fun a h =>
    (SimpleGraph.loopless not_cop_win_two_of_dominating_cycle_petersen).irrefl a.down h⟩

/-- Two cops do not win on the universe-lifted Petersen graph either. -/
theorem not_cop_win_two_of_dominating_cycle_ulift_not_has_cop_win_two :
    ¬ HasCopWinStrategy not_cop_win_two_of_dominating_cycle_ulift_petersen 2 := by
  rintro ⟨C₀, hC⟩
  refine not_cop_win_two_of_dominating_cycle_petersen_not_has_cop_win_two
    ⟨fun i => (C₀ i).down, ?_⟩
  intro R
  exact not_cop_win_two_of_dominating_cycle_cops_win_from_equiv
    (G := not_cop_win_two_of_dominating_cycle_ulift_petersen)
    (G' := not_cop_win_two_of_dominating_cycle_petersen)
    (e := Equiv.ulift) (fun a b => Iff.rfl) 2 C₀ (ULift.up R) (hC (ULift.up R))

/-- The universe-lifted outer 5-cycle vertex map. -/
def not_cop_win_two_of_dominating_cycle_ulift_outer_vertex :
    Fin 5 → ULift (Fin 5 × Bool) :=
  fun i => ULift.up (not_cop_win_two_of_dominating_cycle_outer_vertex i)

theorem not_cop_win_two_of_dominating_cycle_ulift_outer_vertex_injective :
    Function.Injective not_cop_win_two_of_dominating_cycle_ulift_outer_vertex := by
  intro a b h
  have h2 : (a, false) = (b, false) := ULift.up_inj.mp h
  simpa using h2

theorem not_cop_win_two_of_dominating_cycle_ulift_outer_vertex_adj_iff (a b : Fin 5) :
    not_cop_win_two_of_dominating_cycle_ulift_petersen.Adj
        (not_cop_win_two_of_dominating_cycle_ulift_outer_vertex a)
        (not_cop_win_two_of_dominating_cycle_ulift_outer_vertex b) ↔
      (SimpleGraph.cycleGraph 5).Adj a b := by
  show not_cop_win_two_of_dominating_cycle_petersen_adj (a, false) (b, false) ↔
    (SimpleGraph.cycleGraph 5).Adj a b
  fin_cases a <;> fin_cases b <;> decide

/-- The outer 5-cycle inside the universe-lifted Petersen graph. -/
def not_cop_win_two_of_dominating_cycle_ulift_outer_cycle_embedding :
    SimpleGraph.cycleGraph 5 ↪g not_cop_win_two_of_dominating_cycle_ulift_petersen :=
  RelEmbedding.mk
    ⟨not_cop_win_two_of_dominating_cycle_ulift_outer_vertex,
     not_cop_win_two_of_dominating_cycle_ulift_outer_vertex_injective⟩
    (by intro a b; exact not_cop_win_two_of_dominating_cycle_ulift_outer_vertex_adj_iff a b)

/-- The outer 5-cycle dominates the universe-lifted Petersen graph. -/
theorem not_cop_win_two_of_dominating_cycle_ulift_outer_cycle_dominates :
    simple_graph_is_dominating not_cop_win_two_of_dominating_cycle_ulift_petersen
      (Set.range not_cop_win_two_of_dominating_cycle_ulift_outer_cycle_embedding) := by
  intro v
  cases v with
  | up x =>
    obtain ⟨a, b⟩ := x
    cases b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨ULift.up (a, false), ⟨a, rfl⟩, Or.inr (Or.inr ⟨rfl, Bool.false_ne_true⟩)⟩

theorem not_cop_win_two_of_dominating_cycle : ¬ (∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m : ℕ) (hm : 3 ≤ m) (f : SimpleGraph.cycleGraph m ↪g G)
    (hdom : simple_graph_is_dominating G (Set.range f)), HasCopWinStrategy G 2) := by
  intro h
  exact not_cop_win_two_of_dominating_cycle_ulift_not_has_cop_win_two
    (h (V := ULift (Fin 5 × Bool))
      (G := not_cop_win_two_of_dominating_cycle_ulift_petersen) (m := 5) (hm := by norm_num)
      (f := not_cop_win_two_of_dominating_cycle_ulift_outer_cycle_embedding)
      (hdom := not_cop_win_two_of_dominating_cycle_ulift_outer_cycle_dominates))
