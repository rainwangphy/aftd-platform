import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# op874_forest_fixed_external_exact_owner_strictness

Topic: graphs   Node: 12f7181e75f0

Provenance: helper lemma. OP-874: forest exact-owner obstruction, experiments 38549–38554.

The displayed 12-vertex fixed external coloring has ordinary strong local states, but every such state hides color 1 at both ends of indexed edge 10, so exact ownership fails even on that one matching edge.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 2048

private def op874foL : Fin 18 → Fin 12 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,7,8,9,10]
private def op874foR : Fin 18 → Fin 12 := ![1,5,6,2,7,3,8,4,11,5,10,9,7,11,8,9,10,11]
private def op874foEnds (e : Fin 18) : Sym2 (Fin 12) := s(op874foL e,op874foR e)
private def op874foColors : Fin 18 → Fin 6 := ![3,2,0,5,1,4,0,2,1,4,0,1,4,5,2,3,5,3]

private lemma op874foLoopless : ∀ e, ¬ (op874foEnds e).IsDiag := by decide
private lemma op874foCubic : ∀ v : Fin 12,
    Set.ncard {e : Fin 18 | v ∈ op874foEnds e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide
private lemma op874foProper : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f →
    op874foColors e = op874foColors f → e=f := by decide

private lemma op874fo_shared_pair_forces
    (h : Fin 12 → Fin 18 → Fin 6)
    (hh : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e = h v f → e=f)
    (hch : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e ≠ op874foColors f)
    (hs : truncation_local_states_define_strong_coloring op874foEnds (fun _ e => op874foColors e) h)
    (u v : Fin 12) (e : Fin 18) (he : op874foEnds e=s(u,v)) (a b : Fin 6) (hab : a ≠ b)
    (hua : ∀ f, u ∈ op874foEnds f → op874foColors f ≠ a)
    (hub : ∀ f, u ∈ op874foEnds f → op874foColors f ≠ b)
    (hva : ∀ f, v ∈ op874foEnds f → op874foColors f ≠ a)
    (hvb : ∀ f, v ∈ op874foEnds f → op874foColors f ≠ b) :
    h u e=a ∨ h u e=b := by
  classical
  let c : Fin 12 → Fin 18 → Fin 6 := fun _ e => op874foColors e
  have hc : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → c v e = c v f → e=f :=
    op874foProper
  have compat := (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874foEnds op874foLoopless op874foCubic
    c h hc hh hch).1 hs
  have cover (z : Fin 6) (huz : ∀ f, u ∈ op874foEnds f → op874foColors f ≠ z)
      (hvz : ∀ f, v ∈ op874foEnds f → op874foColors f ≠ z) :
      h u e=z ∨ h v e=z := by
    by_contra hn
    push_neg at hn
    have huP : z ∈ truncation_exposed_pair op874foEnds c h u e :=
      ⟨huz, fun heq => hn.1 heq.symm⟩
    have hvP : z ∈ truncation_exposed_pair op874foEnds c h v e :=
      ⟨hvz, fun heq => hn.2 heq.symm⟩
    exact Set.disjoint_left.mp (compat e u v he).2 huP hvP
  rcases cover a hua hva with hu | hv
  · exact Or.inl hu
  · rcases cover b hub hvb with hu | hv'
    · exact Or.inr hu
    · exact False.elim (hab (hv.symm.trans hv'))

private theorem op874fo_forced_both
    (h : Fin 12 → Fin 18 → Fin 6)
    (hh : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e = h v f → e=f)
    (hch : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e ≠ op874foColors f)
    (hs : truncation_local_states_define_strong_coloring op874foEnds (fun _ e => op874foColors e) h) :
    h 4 10=1 ∧ h 10 10=1 := by
  have h47 := op874fo_shared_pair_forces h hh hch hs 4 3 7 (by decide) 3 5 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h49 := op874fo_shared_pair_forces h hh hch hs 4 5 9 (by decide) 3 5 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h1016 := op874fo_shared_pair_forces h hh hch hs 10 9 16 (by decide) 2 4 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h1017 := op874fo_shared_pair_forces h hh hch hs 10 11 17 (by decide) 2 4 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have vals4 : ∀ x : Fin 6, x ≠ 0 → x ≠ 2 → x ≠ 4 → x=1 ∨ x=3 ∨ x=5 := by decide
  have vals10 : ∀ x : Fin 6, x ≠ 0 → x ≠ 3 → x ≠ 5 → x=1 ∨ x=2 ∨ x=4 := by decide
  have hm4 := vals4 (h 4 10)
    (by simpa [op874foColors] using hch 4 10 10 (by decide) (by decide))
    (by simpa [op874foColors] using hch 4 10 7 (by decide) (by decide))
    (by simpa [op874foColors] using hch 4 10 9 (by decide) (by decide))
  have hm10 := vals10 (h 10 10)
    (by simpa [op874foColors] using hch 10 10 10 (by decide) (by decide))
    (by simpa [op874foColors] using hch 10 10 17 (by decide) (by decide))
    (by simpa [op874foColors] using hch 10 10 16 (by decide) (by decide))
  have hn47 : h 4 10 ≠ h 4 7 := fun he =>
    (by decide : (10 : Fin 18) ≠ 7) (hh 4 10 7 (by decide) (by decide) he)
  have hn49 : h 4 10 ≠ h 4 9 := fun he =>
    (by decide : (10 : Fin 18) ≠ 9) (hh 4 10 9 (by decide) (by decide) he)
  have hn1016 : h 10 10 ≠ h 10 16 := fun he =>
    (by decide : (10 : Fin 18) ≠ 16) (hh 10 10 16 (by decide) (by decide) he)
  have hn1017 : h 10 10 ≠ h 10 17 := fun he =>
    (by decide : (10 : Fin 18) ≠ 17) (hh 10 10 17 (by decide) (by decide) he)
  have hn479 : h 4 7 ≠ h 4 9 := fun he =>
    (by decide : (7 : Fin 18) ≠ 9) (hh 4 7 9 (by decide) (by decide) he)
  have hn1617 : h 10 16 ≠ h 10 17 := fun he =>
    (by decide : (16 : Fin 18) ≠ 17) (hh 10 16 17 (by decide) (by decide) he)
  constructor
  · rcases h47 with h47 | h47 <;> rcases h49 with h49 | h49 <;>
      rcases hm4 with hm4 | hm4 | hm4 <;> simp_all
  · rcases h1016 with h1016 | h1016 <;> rcases h1017 with h1017 | h1017 <;>
      rcases hm10 with hm10 | hm10 | hm10 <;> simp_all


private def op874foWitness : Fin 12 → Fin 18 → Fin 6 := ![![4,5,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![2,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,2,0,1,3,0,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,3,0,5,0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,3,0,5,1,0,0,0,0,0,0,0],![0,5,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0],![0,0,3,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0],![0,0,0,0,5,0,0,0,0,0,0,0,3,0,0,0,0,0],![0,0,0,0,0,0,1,0,0,0,0,0,0,0,5,4,0,0],![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,4,0],![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2,4],![0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,2]]

private theorem op874fo_ordinary_completion :
    ∃ h : Fin 12 → Fin 18 → Fin 6,
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e ≠ op874foColors f) ∧
      truncation_local_states_define_strong_coloring op874foEnds (fun _ e => op874foColors e) h := by
  refine ⟨op874foWitness, by decide, by decide, ?_⟩
  have hc : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f →
      op874foColors e = op874foColors f → e=f := op874foProper
  have hh : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f →
      op874foWitness v e = op874foWitness v f → e=f := by decide
  have hch : ∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f →
      op874foWitness v e ≠ op874foColors f := by decide
  apply (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874foEnds op874foLoopless op874foCubic
    (fun _ e => op874foColors e) op874foWitness hc hh hch).2
  have hdata : ∀ (e : Fin 18) (u v : Fin 12) (z : Fin 6), op874foEnds e = s(u,v) →
      (∀ f, u ∈ op874foEnds f → op874foColors f ≠ z) → z ≠ op874foWitness u e →
      (∀ f, v ∈ op874foEnds f → op874foColors f ≠ z) → z ≠ op874foWitness v e → False := by
    intro e
    fin_cases e <;> decide
  intro e u v he
  refine ⟨rfl,?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨hu,hu'⟩ ⟨hv,hv'⟩
  exact hdata e u v z he hu hu' hv hv'

theorem op874_forest_fixed_external_exact_owner_strictness :
    let L : Fin 18 → Fin 12 := ![0,0,0,1,1,2,2,3,3,4,4,5,6,6,7,8,9,10]
    let R : Fin 18 → Fin 12 := ![1,5,6,2,7,3,8,4,11,5,10,9,7,11,8,9,10,11]
    let ends : Fin 18 → Sym2 (Fin 12) := fun e => s(L e,R e)
    let color : Fin 18 → Fin 6 := ![3,2,0,5,1,4,0,2,1,4,0,1,4,5,2,3,5,3]
    (∃ h : Fin 12 → Fin 18 → Fin 6,
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ color f) ∧
      truncation_local_states_define_strong_coloring ends (fun _ e => color e) h) ∧
    ¬ ∃ h : Fin 12 → Fin 18 → Fin 6,
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ color f) ∧
      truncation_local_states_define_strong_coloring ends (fun _ e => color e) h ∧
      ¬ (h 4 10 = 1 ∧ h 10 10 = 1) := by
  change (∃ h : Fin 12 → Fin 18 → Fin 6,
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e ≠ op874foColors f) ∧
      truncation_local_states_define_strong_coloring op874foEnds (fun _ e => op874foColors e) h) ∧
    ¬ ∃ h : Fin 12 → Fin 18 → Fin 6,
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874foEnds e → v ∈ op874foEnds f → h v e ≠ op874foColors f) ∧
      truncation_local_states_define_strong_coloring op874foEnds (fun _ e => op874foColors e) h ∧
      ¬ (h 4 10 = 1 ∧ h 10 10 = 1)
  refine ⟨op874fo_ordinary_completion, ?_⟩
  rintro ⟨h,hh,hch,hs,hn⟩
  exact hn (op874fo_forced_both h hh hch hs)
