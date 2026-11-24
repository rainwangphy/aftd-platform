import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# op874_two_four_forest_fixed_external_no_completion

Topic: graphs   Node: f5184bf85d94

Provenance: helper lemma. OP-874: two-versus-four forest and pair-degree obstruction, experiments 38473 and 38476.

For the displayed 16-vertex two-versus-four external coloring, no hidden local states define a strong six-coloring of the truncation. The accompanying finite data node certifies the graph, eligible matching cut, forest missing graphs and local pair bound.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def op874f16L : Fin 24 → Fin 16 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,6,7,8,9,10,11,11,12,13,14]
private def op874f16R : Fin 24 → Fin 16 := ![1,5,14,2,9,3,12,4,13,5,15,7,7,8,10,8,9,10,11,12,15,13,14,15]
private def op874f16Missing : Fin 16 → Finset (Fin 6) := ![{0,3,5},{1,3,5},{0,3,5},{1,2,3},{0,2,4},{1,4,5},{0,4,5},{1,3,4},{0,2,3},{1,2,3},{1,2,4},{1,2,3},{0,3,4},{1,4,5},{0,2,4},{0,2,3}]
private def op874f16Shared (e : Fin 24) (z : Fin 6) : Prop :=
  z ∈ op874f16Missing (op874f16L e) ∧ z ∈ op874f16Missing (op874f16R e)
private instance (e : Fin 24) (z : Fin 6) : Decidable (op874f16Shared e z) := by
  unfold op874f16Shared
  infer_instance

private theorem op874f16_no_binary_owners :
    ¬ ∃ q : Fin 24 → Fin 6 → Fin 16,
      (∀ e z, op874f16Shared e z → q e z = op874f16L e ∨ q e z = op874f16R e) ∧
      (∀ e f a b, op874f16Shared e a → op874f16Shared f b → q e a = q f b → (e=f ↔ a=b)) := by
  rintro ⟨q,hends,hcollision⟩
  have step (e f : Fin 24) (a b : Fin 6) (v w : Fin 16)
      (hv : q e a = v) (he : op874f16Shared e a) (hf : op874f16Shared f b)
      (hend : (op874f16L f=v ∧ op874f16R f=w) ∨
        (op874f16L f=w ∧ op874f16R f=v))
      (hconf : (e=f ∧ a≠b) ∨ (e≠f ∧ a=b)) : q f b = w := by
    have hbad : q f b ≠ v := by
      intro hv'
      have h := hcollision e f a b he hf (hv.trans hv'.symm)
      rcases hconf with ⟨hef,hab⟩ | ⟨hef,hab⟩
      · exact hab (h.mp hef)
      · exact hef (h.mpr hab)
    rcases hend with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rcases hends f b hf with hleft | hright
      · exact (hbad (hleft.trans hl)).elim
      · exact hright.trans hr
    · rcases hends f b hf with hleft | hright
      · exact hleft.trans hl
      · exact (hbad (hright.trans hr)).elim
  have hor := hends 0 3 (by decide)
  rcases hor with h0 | h0
  ·
    have h1 : q 0 5 = 1 := step 0 0 3 5 0 1 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 3 5 = 2 := step 0 3 5 5 1 2 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 3 3 = 1 := step 3 3 5 3 2 1 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 4 3 = 9 := step 3 4 3 3 1 9 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 16 3 = 8 := step 4 16 3 3 9 8 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 16 2 = 9 := step 16 16 3 2 8 9 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 17 2 = 10 := step 16 17 2 2 9 10 h6 (by decide) (by decide) (by decide) (by decide)
    have h8 : q 18 2 = 11 := step 17 18 2 2 10 11 h7 (by decide) (by decide) (by decide) (by decide)
    have h9 : q 20 2 = 15 := step 18 20 2 2 11 15 h8 (by decide) (by decide) (by decide) (by decide)
    have h10 : q 23 2 = 14 := step 20 23 2 2 15 14 h9 (by decide) (by decide) (by decide) (by decide)
    have h11 : q 23 0 = 15 := step 23 23 2 0 14 15 h10 (by decide) (by decide) (by decide) (by decide)
    have h12 : q 10 0 = 4 := step 23 10 0 0 15 4 h11 (by decide) (by decide) (by decide) (by decide)
    have h13 : q 10 2 = 15 := step 10 10 0 2 4 15 h12 (by decide) (by decide) (by decide) (by decide)
    have h14 : q 20 2 = 11 := step 10 20 2 2 15 11 h13 (by decide) (by decide) (by decide) (by decide)
    have h15 : q 18 2 = 10 := step 20 18 2 2 11 10 h14 (by decide) (by decide) (by decide) (by decide)
    have h16 : q 17 2 = 9 := step 18 17 2 2 10 9 h15 (by decide) (by decide) (by decide) (by decide)
    have h17 : q 16 2 = 8 := step 17 16 2 2 9 8 h16 (by decide) (by decide) (by decide) (by decide)
    have h18 : q 16 3 = 9 := step 16 16 2 3 8 9 h17 (by decide) (by decide) (by decide) (by decide)
    have h19 : q 4 3 = 1 := step 16 4 3 3 9 1 h18 (by decide) (by decide) (by decide) (by decide)
    have h20 : q 3 3 = 2 := step 4 3 3 3 1 2 h19 (by decide) (by decide) (by decide) (by decide)
    have h21 : q 3 5 = 1 := step 3 3 3 5 2 1 h20 (by decide) (by decide) (by decide) (by decide)
    have h22 : q 0 5 = 0 := step 3 0 5 5 1 0 h21 (by decide) (by decide) (by decide) (by decide)
    have h23 : q 0 3 = 1 := step 0 0 5 3 0 1 h22 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (0 : Fin 16) ≠ 1) (h0.symm.trans h23)
  ·
    have h1 : q 3 3 = 2 := step 0 3 3 3 1 2 h0 (by decide) (by decide) (by decide) (by decide)
    have h2 : q 6 3 = 12 := step 3 6 3 3 2 12 h1 (by decide) (by decide) (by decide) (by decide)
    have h3 : q 19 3 = 11 := step 6 19 3 3 12 11 h2 (by decide) (by decide) (by decide) (by decide)
    have h4 : q 20 3 = 15 := step 19 20 3 3 11 15 h3 (by decide) (by decide) (by decide) (by decide)
    have h5 : q 20 2 = 11 := step 20 20 3 2 15 11 h4 (by decide) (by decide) (by decide) (by decide)
    have h6 : q 18 2 = 10 := step 20 18 2 2 11 10 h5 (by decide) (by decide) (by decide) (by decide)
    have h7 : q 17 2 = 9 := step 18 17 2 2 10 9 h6 (by decide) (by decide) (by decide) (by decide)
    have h8 : q 16 2 = 8 := step 17 16 2 2 9 8 h7 (by decide) (by decide) (by decide) (by decide)
    have h9 : q 16 3 = 9 := step 16 16 2 3 8 9 h8 (by decide) (by decide) (by decide) (by decide)
    have h10 : q 4 3 = 1 := step 16 4 3 3 9 1 h9 (by decide) (by decide) (by decide) (by decide)
    have h11 : q 0 3 = 0 := step 4 0 3 3 1 0 h10 (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (1 : Fin 16) ≠ 0) (h0.symm.trans h11)

private def op874f16Ends (e : Fin 24) : Sym2 (Fin 16) := s(op874f16L e,op874f16R e)
private def op874f16Colors : Fin 24 → Fin 6 :=
  ![4,2,1,2,0,4,1,5,0,3,1,0,2,1,3,5,4,5,0,5,4,2,3,5]
private lemma op874f16Loopless : ∀ e, ¬ (op874f16Ends e).IsDiag := by decide
private lemma op874f16Cubic : ∀ v : Fin 16,
    Set.ncard {e : Fin 24 | v ∈ op874f16Ends e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide
private lemma op874f16Proper : ∀ v e f, v ∈ op874f16Ends e → v ∈ op874f16Ends f →
    op874f16Colors e = op874f16Colors f → e=f := by decide
private lemma op874f16MissingIff : ∀ v z, z ∈ op874f16Missing v ↔
    ∀ e, v ∈ op874f16Ends e → op874f16Colors e ≠ z := by decide

theorem op874_two_four_forest_fixed_external_no_completion :
    let L : Fin 24 → Fin 16 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,6,7,8,9,10,11,11,12,13,14]
    let R : Fin 24 → Fin 16 := ![1,5,14,2,9,3,12,4,13,5,15,7,7,8,10,8,9,10,11,12,15,13,14,15]
    let ends : Fin 24 → Sym2 (Fin 16) := fun e => s(L e,R e)
    let color : Fin 24 → Fin 6 := ![4,2,1,2,0,4,1,5,0,3,1,0,2,1,3,5,4,5,0,5,4,2,3,5]
    ¬ ∃ h : Fin 16 → Fin 24 → Fin 6,
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ color f) ∧
      truncation_local_states_define_strong_coloring ends (fun _ e => color e) h := by
  change ¬ ∃ h : Fin 16 → Fin 24 → Fin 6,
      (∀ v e f, v ∈ op874f16Ends e → v ∈ op874f16Ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874f16Ends e → v ∈ op874f16Ends f → h v e ≠ op874f16Colors f) ∧
      truncation_local_states_define_strong_coloring op874f16Ends (fun _ e => op874f16Colors e) h
  classical
  rintro ⟨h,hh,hch,hs⟩
  let c : Fin 16 → Fin 24 → Fin 6 := fun _ e => op874f16Colors e
  have hc : ∀ v e f, v ∈ op874f16Ends e → v ∈ op874f16Ends f → c v e = c v f → e=f :=
    op874f16Proper
  have compat := (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874f16Ends op874f16Loopless op874f16Cubic
    c h hc hh hch).1 hs
  have cover (e : Fin 24) (z : Fin 6) (hz : op874f16Shared e z) :
      h (op874f16L e) e = z ∨ h (op874f16R e) e = z := by
    by_contra hn
    push_neg at hn
    have huP : z ∈ truncation_exposed_pair op874f16Ends c h (op874f16L e) e :=
      ⟨(op874f16MissingIff _ _).1 hz.1, fun heq => hn.1 heq.symm⟩
    have hvP : z ∈ truncation_exposed_pair op874f16Ends c h (op874f16R e) e :=
      ⟨(op874f16MissingIff _ _).1 hz.2, fun heq => hn.2 heq.symm⟩
    exact Set.disjoint_left.mp (compat e (op874f16L e) (op874f16R e) rfl).2 huP hvP
  let q (e : Fin 24) (z : Fin 6) : Fin 16 :=
    if h (op874f16L e) e = z then op874f16L e else op874f16R e
  have qgood (e : Fin 24) (z : Fin 6) (hz : op874f16Shared e z) :
      q e z ∈ op874f16Ends e ∧ h (q e z) e = z := by
    by_cases hl : h (op874f16L e) e = z
    · simp [q,hl,op874f16Ends]
    · have hr := (cover e z hz).resolve_left hl
      simp [q,hl,hr,op874f16Ends]
  apply op874f16_no_binary_owners
  refine ⟨q,?_,?_⟩
  · intro e z hz
    dsimp [q]
    split_ifs <;> simp
  · intro e f a b he hf heq
    have he' := qgood e a he
    have hf' := qgood f b hf
    rw [← heq] at hf'
    constructor
    · intro hef
      subst f
      exact he'.2.symm.trans hf'.2
    · intro hab
      apply hh (q e a) e f he'.1 hf'.1
      exact he'.2.trans (hab.trans hf'.2.symm)
