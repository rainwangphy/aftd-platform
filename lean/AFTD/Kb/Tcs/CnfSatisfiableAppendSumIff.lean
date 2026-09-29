import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfSatisfiableOfAppend
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_satisfiable_append_sum_iff

Topic: np_completeness   Node: 54cb405c624e

Let f be a CNF formula over a variable type V and g a CNF formula over a variable type W. Replace every literal of f by the literal of the same sign whose variable is Sum.inl of the old variable, and every literal of g by the literal of the same sign whose variable is Sum.inr of the old variable, and concatenate the clause lists. The resulting formula over the disjoint union V ⊕ W is satisfiable if and only if f is satisfiable over V and g is satisfiable over W.
-/

def cnf_satisfiable_append_sum_iff_lift_inl {V W : Type*} (l : CnfLit V) : CnfLit (V ⊕ W) :=
  match l with
  | CnfLit.pos v => CnfLit.pos (Sum.inl v)
  | CnfLit.neg v => CnfLit.neg (Sum.inl v)

def cnf_satisfiable_append_sum_iff_lift_inr {V W : Type*} (l : CnfLit W) : CnfLit (V ⊕ W) :=
  match l with
  | CnfLit.pos v => CnfLit.pos (Sum.inr v)
  | CnfLit.neg v => CnfLit.neg (Sum.inr v)

/-- Standardizing apart: clauses over disjoint variable sets are satisfiable jointly iff each is satisfiable separately. -/
theorem cnf_satisfiable_append_sum_iff {V W : Type*} (f : List (List (CnfLit V)))
    (g : List (List (CnfLit W))) :
    CnfSatisfiable (f.map (List.map (fun l : CnfLit V =>
        match l with | CnfLit.pos v => CnfLit.pos (Sum.inl v) | CnfLit.neg v => CnfLit.neg (Sum.inl v)))
      ++ g.map (List.map (fun l : CnfLit W =>
        match l with | CnfLit.pos v => CnfLit.pos (Sum.inr v) | CnfLit.neg v => CnfLit.neg (Sum.inr v))))
      ↔ CnfSatisfiable f ∧ CnfSatisfiable g := by
  change CnfSatisfiable (f.map (List.map (cnf_satisfiable_append_sum_iff_lift_inl (W := W)))
      ++ g.map (List.map (cnf_satisfiable_append_sum_iff_lift_inr (V := V))))
      ↔ CnfSatisfiable f ∧ CnfSatisfiable g
  constructor
  · intro h
    have hsplit := cnf_satisfiable_of_append h
    constructor
    · obtain ⟨ρ, hρ⟩ := hsplit.1
      refine ⟨fun v => ρ (Sum.inl v), ?_⟩
      intro c hc
      obtain ⟨l, hl, he⟩ := hρ (c.map (cnf_satisfiable_append_sum_iff_lift_inl (W := W))) (List.mem_map_of_mem hc)
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      cases l' with
      | pos v => exact ⟨CnfLit.pos v, hl', he⟩
      | neg v => exact ⟨CnfLit.neg v, hl', he⟩
    · obtain ⟨ρ, hρ⟩ := hsplit.2
      refine ⟨fun w => ρ (Sum.inr w), ?_⟩
      intro c hc
      obtain ⟨l, hl, he⟩ := hρ (c.map (cnf_satisfiable_append_sum_iff_lift_inr (V := V))) (List.mem_map_of_mem hc)
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      cases l' with
      | pos v => exact ⟨CnfLit.pos v, hl', he⟩
      | neg v => exact ⟨CnfLit.neg v, hl', he⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨Sum.elim σ τ, ?_⟩
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨l', hl', he⟩ := hσ c' hc'
      cases l' with
      | pos v => exact ⟨CnfLit.pos (Sum.inl v), List.mem_map_of_mem hl', he⟩
      | neg v => exact ⟨CnfLit.neg (Sum.inl v), List.mem_map_of_mem hl', he⟩
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨l', hl', he⟩ := hτ c' hc'
      cases l' with
      | pos v => exact ⟨CnfLit.pos (Sum.inr v), List.mem_map_of_mem hl', he⟩
      | neg v => exact ⟨CnfLit.neg (Sum.inr v), List.mem_map_of_mem hl', he⟩
