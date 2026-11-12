import AFTD.Prelude
import AFTD.Kb.Optimization.WolfeMajorCycle
import AFTD.Kb.Optimization.IsWolfeCorral
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.Optimization.BasePolytopeExtremeBases

/-!
# linopt_major_cycle_discards_corral_atom

Topic: optimization   Node: ec1dc42c1e38

Provenance: helper lemma. Counterexample to the stated transition relation, compared with the algorithm in arXiv:2611.12680 Section 2.2.

The formal major-cycle relation can discard the previous atom even though the enlarged two-atom support is already a corral, for the base polytope of a normalized submodular function.
-/

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private lemma in772_counterexampleproof_single (p : Fin 2 → ℝ) : is_wolfe_corral {p} p := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro x hx
    have : x=p := by simpa using hx
    subst x
    simp
  · refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp

private lemma in772_counterexampleproof_counterexample :
    ∃ (p q r : Fin 2 → ℝ),
      p = ![3,0] ∧ q = ![1,2] ∧
      wolfe_major_cycle ({p, q} : Set (Fin 2 → ℝ)) {p} {q} p q ∧
      is_wolfe_corral ({p,q} : Finset (Fin 2 → ℝ)) r ∧ p ≠ q := by
  classical
  let p : Fin 2 → ℝ := ![3,0]
  let q : Fin 2 → ℝ := ![1,2]
  let r : Fin 2 → ℝ := ![(3:ℝ)/2,3/2]
  have hpq : p ≠ q := by
    intro h
    have hh := congrFun h 0
    norm_num [p,q] at hh
  have hqp : q ≠ p := Ne.symm hpq
  refine ⟨p,q,r,rfl,rfl,?_,?_,hpq⟩
  · refine ⟨in772_counterexampleproof_single p,in772_counterexampleproof_single q,?_,?_,q,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp
    · simp
    · norm_num [p,q,Fin.sum_univ_two]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> norm_num [p,q,Fin.sum_univ_two]
    · simp
    · simp
    · norm_num [p,q,Fin.sum_univ_two]
  · refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [p,q,r,Fin.sum_univ_two]
    · let c : (Fin 2 → ℝ) → ℝ := fun x => if x=p then 1/4 else 3/4
      refine ⟨c, ?_, ?_, ?_⟩
      · simp [c,hpq,hqp]; norm_num
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [c,hpq,hqp] <;> norm_num
      · ext i
        fin_cases i <;> simp [c,hpq,hqp,p,q,r] <;> norm_num


private def in772_counterexampleproof_f (S : Finset (Fin 2)) : ℝ :=
  if (0 : Fin 2) ∈ S then 3 else if (1 : Fin 2) ∈ S then 2 else 0

private lemma in772_counterexampleproof_f_submodular : in772_counterexampleproof_f ∅ = 0 ∧ is_submodular in772_counterexampleproof_f := by
  constructor
  · norm_num [in772_counterexampleproof_f]
  · classical
    intro S T j hST hj
    fin_cases S <;> fin_cases T <;> fin_cases j <;>
      norm_num [in772_counterexampleproof_f,Finset.subset_iff] at *

private lemma in772_counterexampleproof_atoms : base_polytope_extreme_bases in772_counterexampleproof_f =
    ({(![3,0] : Fin 2 → ℝ), ![1,2]} : Set (Fin 2 → ℝ)) := by
  ext a
  simp only [base_polytope_extreme_bases, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨pi,rfl⟩
    have hpi : pi.symm 0 = 0 ∨ pi.symm 0 = 1 := by
      have hh := (pi.symm 0).isLt
      omega
    have hn : pi.symm 1 ≠ pi.symm 0 := by
      intro h
      have hbad := pi.symm.injective h
      norm_num at hbad
    rcases hpi with h0 | h0
    · have h1 : pi.symm 1 = 1 := by
        have hh := (pi.symm 1).isLt
        omega
      left
      funext i
      fin_cases i <;> norm_num [in772_counterexampleproof_f,h0,h1]
    · have h1 : pi.symm 1 = 0 := by
        have hh := (pi.symm 1).isLt
        omega
      right
      funext i
      fin_cases i <;> norm_num [in772_counterexampleproof_f,h0,h1]
  · rintro (rfl | rfl)
    · refine ⟨Equiv.refl _, ?_⟩
      funext i
      fin_cases i <;> norm_num [in772_counterexampleproof_f]
    · refine ⟨Equiv.swap 0 1, ?_⟩
      funext i
      fin_cases i <;> norm_num [in772_counterexampleproof_f,Equiv.swap_apply_def]


private lemma in772_counterexampleproof_submodular_false_transition :
    ∃ (f : Finset (Fin 2) → ℝ) (p q r : Fin 2 → ℝ),
      f ∅ = 0 ∧ is_submodular f ∧
      base_polytope_extreme_bases f = ({p,q} : Set (Fin 2 → ℝ)) ∧
      wolfe_major_cycle (base_polytope_extreme_bases f) {p} {q} p q ∧
      is_wolfe_corral ({p,q} : Finset (Fin 2 → ℝ)) r ∧ p ≠ q := by
  obtain ⟨p,q,r,hp,hq,hstep,hcorral,hne⟩ := in772_counterexampleproof_counterexample
  refine ⟨in772_counterexampleproof_f,p,q,r,in772_counterexampleproof_f_submodular.1,in772_counterexampleproof_f_submodular.2,?_,?_,hcorral,hne⟩
  · simpa [hp,hq] using in772_counterexampleproof_atoms
  · simpa [in772_counterexampleproof_atoms,hp,hq] using hstep

theorem linopt_major_cycle_discards_corral_atom :
    ∃ (f : Finset (Fin 2) → ℝ) (p q r : Fin 2 → ℝ),
      f ∅ = 0 ∧ is_submodular f ∧
      base_polytope_extreme_bases f = ({p,q} : Set (Fin 2 → ℝ)) ∧
      wolfe_major_cycle (base_polytope_extreme_bases f) {p} {q} p q ∧
      is_wolfe_corral ({p,q} : Finset (Fin 2 → ℝ)) r ∧ p ≠ q := by
  exact in772_counterexampleproof_submodular_false_transition
