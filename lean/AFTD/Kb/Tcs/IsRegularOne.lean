import AFTD.Prelude

/-!
# is_regular_one

Topic: automata   Node: 08c36b51abc6

Provenance: formalization of a published result. Source: standard textbook result (automata theory): {ε} is regular

The language {[]} containing only the empty word is regular.
-/

/-- The language containing only the empty word (the unit language 1) is regular. -/
theorem is_regular_one {α : Type*} : (1 : Language α).IsRegular := by
  have hfold : ∀ (y : List α) (s : Bool),
      List.foldl (fun (_ : Bool) (_ : α) => false) s y = if y = [] then s else false := by
    intro y
    induction y with
    | nil => intro s; simp
    | cons b y ih =>
      intro s
      simp only [List.foldl_cons, ih, reduceCtorEq, if_false]
      split_ifs <;> rfl
  refine ⟨Bool, inferInstance, ⟨fun _ _ => false, true, {true}⟩, ?_⟩
  ext x
  rw [DFA.mem_accepts, Language.mem_one]
  show List.foldl (fun (_ : Bool) (_ : α) => false) true x ∈ ({true} : Set Bool) ↔ x = []
  rw [hfold]
  split_ifs with h <;> simp [h]
