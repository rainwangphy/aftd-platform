import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree

/-!
# is_claw_free_triple_neighbors

Topic: graphs   Node: 730835a11f3c

Provenance: helper lemma. step towards op_292_cop_number_p7_claw_free

In any claw-free graph, among any three distinct neighbors of a vertex, at least two are adjacent.
-/

/-- In any claw-free graph, among any three distinct neighbors of a vertex, at least two are adjacent. -/
theorem is_claw_free_triple_neighbors {V : Type*} (G : SimpleGraph V) (hclaw : IsClawFree G)
    (v : V) (a b c : V) (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  by_contra h
  push Not at h
  obtain ⟨hab', hac', hbc'⟩ := h
  have hab'' : ¬ G.Adj b a := fun hh => hab' hh.symm
  have hac'' : ¬ G.Adj c a := fun hh => hac' hh.symm
  have hbc'' : ¬ G.Adj c b := fun hh => hbc' hh.symm
  apply hclaw
  let f : Fin 1 ⊕ Fin 3 → V := Sum.elim (fun _ => v) ![a,b,c]
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · simp only [f, Sum.elim_inl] at hxy
      exact congrArg Sum.inl (Subsingleton.elim i j)
    · fin_cases i
      fin_cases j <;> simp only [f, Sum.elim_inr] at hxy
      · exact absurd hxy ha.ne
      · exact absurd hxy hb.ne
      · exact absurd hxy hc.ne
    · fin_cases i <;> fin_cases j <;> simp only [f, Sum.elim_inr] at hxy
      · exact absurd hxy.symm ha.ne
      · exact absurd hxy.symm hb.ne
      · exact absurd hxy.symm hc.ne
    · fin_cases i <;> fin_cases j <;> simp only [f, Sum.elim_inr] at hxy ⊢
      all_goals first
        | rfl
        | exact absurd hxy hab
        | exact absurd hxy hab.symm
        | exact absurd hxy hac
        | exact absurd hxy hac.symm
        | exact absurd hxy hbc
        | exact absurd hxy hbc.symm
  refine ⟨{ toFun := f, inj' := hf_inj, map_rel_iff' := ?_ }⟩
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [f, completeBipartiteGraph, ha, hb, hc, ha.symm, hb.symm, hc.symm,
      hab', hac', hbc', hab'', hac'', hbc'']
