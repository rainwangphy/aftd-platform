import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# op874_fixed_external_exact_owner_strictness

Topic: graphs   Node: 9467c47ee6f2

Provenance: helper lemma. OP-874: fixed-color exact-owner obstruction, experiments 38521 and 38525.

For the displayed proper two-versus-four external coloring of an eight-vertex two-square graph, ordinary strong local states exist but none satisfy exact low-port ownership on all four matching edges.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 2048

private def op874xoL : Fin 12 → Fin 8 := ![0,0,0,1,1,2,2,3,4,4,5,6]
private def op874xoR : Fin 12 → Fin 8 := ![1,3,4,2,6,3,5,7,5,7,6,7]
private def op874xoEnds (e : Fin 12) : Sym2 (Fin 8) := s(op874xoL e,op874xoR e)
private def op874xoColors : Fin 12 → Fin 6 := ![5,2,0,2,1,4,0,1,3,4,5,3]
private def op874xoPorts : Fin 8 → Fin 3 → Fin 12 := ![![0,1,2],![0,3,4],![3,5,6],![1,5,7],![2,8,9],![6,8,10],![4,10,11],![7,9,11]]
private def op874xoMissing : Fin 8 → Finset (Fin 6) := ![{1,3,4},{0,3,4},{1,3,5},{0,3,5},{1,2,5},{1,2,4},{0,2,4},{0,2,5}]
private def op874xoState : Fin 8 → Fin 6 → Fin 3 → Fin 6 := ![![![1,3,4],![1,4,3],![3,1,4],![3,4,1],![4,1,3],![4,3,1]],![![0,3,4],![0,4,3],![3,0,4],![3,4,0],![4,0,3],![4,3,0]],![![1,3,5],![1,5,3],![3,1,5],![3,5,1],![5,1,3],![5,3,1]],![![0,3,5],![0,5,3],![3,0,5],![3,5,0],![5,0,3],![5,3,0]],![![1,2,5],![1,5,2],![2,1,5],![2,5,1],![5,1,2],![5,2,1]],![![1,2,4],![1,4,2],![2,1,4],![2,4,1],![4,1,2],![4,2,1]],![![0,2,4],![0,4,2],![2,0,4],![2,4,0],![4,0,2],![4,2,0]],![![0,2,5],![0,5,2],![2,0,5],![2,5,0],![5,0,2],![5,2,0]]]
private def op874xoIndex (v : Fin 8) (e : Fin 12) : Fin 3 :=
  if op874xoPorts v 0 = e then 0 else if op874xoPorts v 1 = e then 1 else 2
private def op874xoHidden (v : Fin 8) (s : Fin 6) (e : Fin 12) : Fin 6 :=
  op874xoState v s (op874xoIndex v e)
private def op874xoExposed (v : Fin 8) (s : Fin 6) (e : Fin 12) : Finset (Fin 6) :=
  (op874xoMissing v).erase (op874xoHidden v s e)
private def op874xoAllow (e : Fin 12) (a b : Fin 6) : Bool :=
  decide (Disjoint (op874xoExposed (op874xoL e) a e) (op874xoExposed (op874xoR e) b e) ∧
    ((e = 2 ∨ e = 6) → ¬ (op874xoHidden (op874xoL e) a e = 1 ∧
       op874xoHidden (op874xoR e) b e = 1)))

private theorem op874xo_csp_impossible :
    ∀ x0 : Fin 6, ∀ x1 : Fin 6, op874xoAllow 0 x0 x1 = true →
    ∀ x2 : Fin 6, op874xoAllow 3 x1 x2 = true →
    ∀ x3 : Fin 6, op874xoAllow 1 x0 x3 = true → op874xoAllow 5 x2 x3 = true →
    ∀ x4 : Fin 6, op874xoAllow 2 x0 x4 = true →
    ∀ x5 : Fin 6, op874xoAllow 6 x2 x5 = true → op874xoAllow 8 x4 x5 = true →
    ∀ x6 : Fin 6, op874xoAllow 4 x1 x6 = true → op874xoAllow 10 x5 x6 = true →
    ∀ x7 : Fin 6, op874xoAllow 7 x3 x7 = true → op874xoAllow 9 x4 x7 = true →
      op874xoAllow 11 x6 x7 = true → False := by decide


private lemma op874xoLoopless : ∀ e, ¬ (op874xoEnds e).IsDiag := by decide
private lemma op874xoCubic : ∀ v : Fin 8,
    Set.ncard {e : Fin 12 | v ∈ op874xoEnds e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide
private lemma op874xoProper : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f →
    op874xoColors e = op874xoColors f → e=f := by decide
private lemma op874xoPortMem : ∀ v k, v ∈ op874xoEnds (op874xoPorts v k) := by decide
private lemma op874xoPortInj : ∀ v k l, op874xoPorts v k = op874xoPorts v l → k=l := by decide
private lemma op874xoPortInverse : ∀ v e, v ∈ op874xoEnds e →
    op874xoPorts v (op874xoIndex v e) = e := by decide
private lemma op874xoMissingIff : ∀ v z, z ∈ op874xoMissing v ↔
    ∀ e, v ∈ op874xoEnds e → op874xoColors e ≠ z := by decide
private lemma op874xoStateComplete : ∀ (v : Fin 8) (a b d : Fin 6),
    a ≠ b → a ≠ d → b ≠ d →
    (∀ k : Fin 3, a ≠ op874xoColors (op874xoPorts v k)) →
    (∀ k : Fin 3, b ≠ op874xoColors (op874xoPorts v k)) →
    (∀ k : Fin 3, d ≠ op874xoColors (op874xoPorts v k)) →
    ∃ i : Fin 6, op874xoState v i 0 = a ∧ op874xoState v i 1 = b ∧
      op874xoState v i 2 = d := by decide

private theorem op874xo_two_edges_impossible
    (h : Fin 8 → Fin 12 → Fin 6)
    (hh : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e = h v f → e=f)
    (hch : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e ≠ op874xoColors f)
    (hs : truncation_local_states_define_strong_coloring op874xoEnds (fun _ e => op874xoColors e) h)
    (hx2 : ¬ (h 0 2 = 1 ∧ h 4 2 = 1))
    (hx6 : ¬ (h 2 6 = 1 ∧ h 5 6 = 1)) : False := by
  classical
  let c : Fin 8 → Fin 12 → Fin 6 := fun _ e => op874xoColors e
  have hc : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → c v e = c v f → e=f :=
    op874xoProper
  have compat := (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874xoEnds op874xoLoopless op874xoCubic
    c h hc hh hch).1 hs
  have hstate (v : Fin 8) : ∃ i : Fin 6, ∀ k : Fin 3,
      h v (op874xoPorts v k) = op874xoState v i k := by
    have hdiff (k l : Fin 3) (hkl : k ≠ l) :
        h v (op874xoPorts v k) ≠ h v (op874xoPorts v l) := by
      intro heq
      apply hkl
      exact op874xoPortInj v k l (hh v _ _ (op874xoPortMem v k) (op874xoPortMem v l) heq)
    obtain ⟨i,h0,h1,h2⟩ := op874xoStateComplete v
      (h v (op874xoPorts v 0)) (h v (op874xoPorts v 1)) (h v (op874xoPorts v 2))
      (hdiff 0 1 (by decide)) (hdiff 0 2 (by decide)) (hdiff 1 2 (by decide))
      (fun k => hch v _ _ (op874xoPortMem v 0) (op874xoPortMem v k))
      (fun k => hch v _ _ (op874xoPortMem v 1) (op874xoPortMem v k))
      (fun k => hch v _ _ (op874xoPortMem v 2) (op874xoPortMem v k))
    refine ⟨i,?_⟩
    intro k
    fin_cases k <;> symm <;> assumption
  let X (v : Fin 8) : Fin 6 := Classical.choose (hstate v)
  have hX (v : Fin 8) (k : Fin 3) : h v (op874xoPorts v k) = op874xoState v (X v) k :=
    Classical.choose_spec (hstate v) k
  have hval (v : Fin 8) (e : Fin 12) (hv : v ∈ op874xoEnds e) :
      h v e = op874xoHidden v (X v) e := by
    have hp := hX v (op874xoIndex v e)
    rw [op874xoPortInverse v e hv] at hp
    exact hp
  have hEx (v : Fin 8) (e : Fin 12) (hv : v ∈ op874xoEnds e) (z : Fin 6) :
      z ∈ op874xoExposed v (X v) e ↔ z ∈ truncation_exposed_pair op874xoEnds c h v e := by
    have heq := hval v e hv
    constructor
    · intro hz
      have hz' := Finset.mem_erase.mp hz
      exact ⟨(op874xoMissingIff v z).1 hz'.2, fun h' => hz'.1 (h'.trans heq)⟩
    · intro hz
      apply Finset.mem_erase.mpr
      exact ⟨fun h' => hz.2 (h'.trans heq.symm), (op874xoMissingIff v z).2 hz.1⟩
  have hAllow (e : Fin 12) : op874xoAllow e (X (op874xoL e)) (X (op874xoR e)) = true := by
    have hL : op874xoL e ∈ op874xoEnds e := by simp [op874xoEnds]
    have hR : op874xoR e ∈ op874xoEnds e := by simp [op874xoEnds]
    have hdisj : Disjoint (op874xoExposed (op874xoL e) (X (op874xoL e)) e)
        (op874xoExposed (op874xoR e) (X (op874xoR e)) e) := by
      rw [Finset.disjoint_left]
      intro z hu hv
      exact Set.disjoint_left.mp (compat e (op874xoL e) (op874xoR e) rfl).2
        ((hEx _ _ hL _).1 hu) ((hEx _ _ hR _).1 hv)
    have hmatch : (e=2 ∨ e=6) → ¬
        (op874xoHidden (op874xoL e) (X (op874xoL e)) e = 1 ∧
         op874xoHidden (op874xoR e) (X (op874xoR e)) e = 1) := by
      rintro (rfl | rfl) ⟨hu,hv⟩
      · apply hx2
        constructor
        · exact (hval 0 2 (by decide)).trans (by simpa [op874xoL] using hu)
        · exact (hval 4 2 (by decide)).trans (by simpa [op874xoR] using hv)
      · apply hx6
        constructor
        · exact (hval 2 6 (by decide)).trans (by simpa [op874xoL] using hu)
        · exact (hval 5 6 (by decide)).trans (by simpa [op874xoR] using hv)
    simp only [op874xoAllow, decide_eq_true_eq]
    exact ⟨hdisj,hmatch⟩
  exact op874xo_csp_impossible (X 0) (X 1) (hAllow 0)
    (X 2) (hAllow 3) (X 3) (hAllow 1) (hAllow 5) (X 4) (hAllow 2)
    (X 5) (hAllow 6) (hAllow 8) (X 6) (hAllow 4) (hAllow 10)
    (X 7) (hAllow 7) (hAllow 9) (hAllow 11)


private def op874xoWitness : Fin 8 → Fin 12 → Fin 6 := ![![4,3,1,0,0,0,0,0,0,0,0,0],![3,0,0,0,4,0,0,0,0,0,0,0],![0,0,0,3,0,5,1,0,0,0,0,0],![0,5,0,0,0,3,0,0,0,0,0,0],![0,0,1,0,0,0,0,0,2,5,0,0],![0,0,0,0,0,0,4,0,1,0,2,0],![0,0,0,0,0,0,0,0,0,0,4,2],![0,0,0,0,0,0,0,5,0,2,0,0]]

private theorem op874xo_ordinary_completion :
    ∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e ≠ op874xoColors f) ∧
      truncation_local_states_define_strong_coloring op874xoEnds (fun _ e => op874xoColors e) h := by
  refine ⟨op874xoWitness, by decide, by decide, ?_⟩
  have hc : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f →
      op874xoColors e = op874xoColors f → e=f := op874xoProper
  have hh : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f →
      op874xoWitness v e = op874xoWitness v f → e=f := by decide
  have hch : ∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f →
      op874xoWitness v e ≠ op874xoColors f := by decide
  apply (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874xoEnds op874xoLoopless op874xoCubic
    (fun _ e => op874xoColors e) op874xoWitness hc hh hch).2
  have hdata : ∀ (e : Fin 12) (u v : Fin 8) (z : Fin 6), op874xoEnds e = s(u,v) →
      (∀ f, u ∈ op874xoEnds f → op874xoColors f ≠ z) → z ≠ op874xoWitness u e →
      (∀ f, v ∈ op874xoEnds f → op874xoColors f ≠ z) → z ≠ op874xoWitness v e → False := by
    intro e
    fin_cases e <;> decide
  intro e u v he
  refine ⟨rfl,?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨hu,hu'⟩ ⟨hv,hv'⟩
  exact hdata e u v z he hu hu' hv hv'

private def op874xoBits : Fin 8 → Bool := ![false,true,false,true,false,false,true,true]
private def op874xoMatch : Finset (Fin 12) := {2,4,6,7}

theorem op874_fixed_external_exact_owner_strictness :
    let L : Fin 12 → Fin 8 := ![0,0,0,1,1,2,2,3,4,4,5,6]
    let R : Fin 12 → Fin 8 := ![1,3,4,2,6,3,5,7,5,7,6,7]
    let ends : Fin 12 → Sym2 (Fin 8) := fun e => s(L e,R e)
    let color : Fin 12 → Fin 6 := ![5,2,0,2,1,4,0,1,3,4,5,3]
    let bits : Fin 8 → Bool := ![false,true,false,true,false,false,true,true]
    let matching : Finset (Fin 12) := {2,4,6,7}
    (∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ color f) ∧
      truncation_local_states_define_strong_coloring ends (fun _ e => color e) h) ∧
    ¬ ∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ color f) ∧
      truncation_local_states_define_strong_coloring ends (fun _ e => color e) h ∧
      (∀ e ∈ matching, ¬ (h (L e) e = (if bits (L e) then 0 else 1) ∧
        h (R e) e = (if bits (R e) then 0 else 1))) := by
  change (∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e ≠ op874xoColors f) ∧
      truncation_local_states_define_strong_coloring op874xoEnds (fun _ e => op874xoColors e) h) ∧
    ¬ ∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874xoEnds e → v ∈ op874xoEnds f → h v e ≠ op874xoColors f) ∧
      truncation_local_states_define_strong_coloring op874xoEnds (fun _ e => op874xoColors e) h ∧
      (∀ e ∈ op874xoMatch, ¬ (h (op874xoL e) e = (if op874xoBits (op874xoL e) then 0 else 1) ∧
        h (op874xoR e) e = (if op874xoBits (op874xoR e) then 0 else 1)))
  refine ⟨op874xo_ordinary_completion, ?_⟩
  rintro ⟨h,hh,hch,hs,hexact⟩
  apply op874xo_two_edges_impossible h hh hch hs
  · have h2 := hexact 2 (by decide)
    simpa [op874xoBits,op874xoL,op874xoR] using h2
  · have h6 := hexact 6 (by decide)
    simpa [op874xoBits,op874xoL,op874xoR] using h6
