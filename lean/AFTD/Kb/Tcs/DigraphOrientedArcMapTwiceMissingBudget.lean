import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorOverlapIncidenceIdentity
import AFTD.Kb.Tcs.FiniteEndomapMissingImageEqNonrepresentatives
import AFTD.Kb.Tcs.FiniteFunctionCollisionHeadPairInjective
import AFTD.Kb.Tcs.FiniteEndomapCollisionChargeIdentity
import AFTD.Kb.Tcs.DigraphOrientedTwoParentCollisionLimit
import AFTD.Kb.Tcs.DigraphTwoCommonParentsEdgeMultiplicity
import AFTD.Kb.Tcs.DigraphArcChoiceCollisionRepeatedPair
import AFTD.Kb.Tcs.DigraphTwoParentCollisionChargeCardLeOne
import AFTD.Kb.Tcs.FiniteParentCollisionBudgetWithCover
import AFTD.Kb.Tcs.OrientedOverlapMultiplicityBudget

/-!
# digraph_oriented_arc_map_twice_missing_budget

Topic: graphs   Node: 8999422eab35

Provenance: helper lemma. Collision accounting for the four-cycle campaign; experiment 13230.

In a finite loopless oriented digraph with a chosen common predecessor for every arc, twice the number of arcs missing from the resulting predecessor arc map is at most three times the total repeated common-predecessor incidence count.
-/

private instance in516_graph_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_oriented_arc_map_twice_missing_budget
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (choose : α → α → α)
    (hloop : ∀ u, ¬ D.Adj u u)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hchoice : ∀ u v, D.Adj u v → D.Adj (choose u v) u ∧ D.Adj (choose u v) v) :
    let Arc := {e : α × α // D.Adj e.1 e.2}
    let f : Arc → Arc := fun e =>
      ⟨(choose e.val.1 e.val.2, e.val.1), (hchoice e.val.1 e.val.2 e.property).1⟩
    2 * ((Finset.univ : Finset Arc) \ Finset.univ.image f).card ≤
      3 * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
        (digraph_common_predecessor_graph D).edgeFinset.card) := by
  classical
  let Arc := {e : α × α // D.Adj e.1 e.2}
  let f : Arc → Arc := fun e =>
    ⟨(choose e.val.1 e.val.2, e.val.1), (hchoice e.val.1 e.val.2 e.property).1⟩
  let r : Arc → Arc := fun y => if h : ∃ x, f x = y then Classical.choose h else y
  have hr : ∀ x, f (r (f x)) = f x := by
    intro x
    dsimp [r]
    split
    · rename_i h
      exact Classical.choose_spec h
    · rename_i h
      exact (h ⟨x,rfl⟩).elim
  let tail : Arc → α := fun x => x.val.1
  let head : Arc → α := fun x => x.val.2
  have htail : ∀ x y, f x = f y → tail x = tail y := by
    intro x y h
    exact congrArg (fun z : Arc => z.val.2) h
  have hkey : Function.Injective (fun x => (tail x, head x)) := by
    intro x y h
    exact Subtype.ext h
  let parent : Sym2 α → Finset α := fun e =>
    Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x
  let edges := (digraph_common_predecessor_graph D).edgeFinset
  let repeated := edges.filter fun e => 2 ≤ (parent e).card
  let dirty : Finset α := Finset.univ.filter fun u =>
    ∃ a b p, a ≠ b ∧ p ≠ u ∧ D.Adj u a ∧ D.Adj u b ∧ D.Adj p a ∧ D.Adj p b
  let missing : Finset Arc := Finset.univ \ Finset.univ.image f
  let nonrep : Finset Arc := Finset.univ.filter fun x => r (f x) ≠ x
  let edge : Arc → Sym2 α := fun x => s(head x, head (r (f x)))
  let charge : Sym2 α → Finset α := fun e => (nonrep.filter fun x => edge x = e).image tail
  have hdata (x : Arc) : tail (r (f x)) = tail x ∧
      choose (tail x) (head (r (f x))) = choose (tail x) (head x) := by
    have h := hr x
    have ht : tail (r (f x)) = tail x := htail _ _ h
    have hc : choose (tail (r (f x))) (head (r (f x))) =
        choose (tail x) (head x) := congrArg (fun z : Arc => z.val.1) h
    rw [ht] at hc
    exact ⟨ht,hc⟩
  have hheads (x : Arc) (hx : r (f x) ≠ x) : head x ≠ head (r (f x)) := by
    intro h
    apply hx
    apply Subtype.ext
    exact Prod.ext (hdata x).1 h.symm
  have hcharged (x : Arc) (hx : r (f x) ≠ x) : edge x ∈ repeated := by
    have hd := hdata x
    have ha : D.Adj (tail x) (head x) := x.property
    have hb : D.Adj (tail x) (head (r (f x))) := by
      have hp : D.Adj (tail (r (f x))) (head (r (f x))) := (r (f x)).property
      rw [hd.1] at hp
      exact hp
    have hh := digraph_arc_choice_collision_repeated_pair α D choose hloop hchoice
      (tail x) (head x) (head (r (f x))) (hheads x hx) ha hb hd.2.symm
    exact Finset.mem_filter.mpr hh
  have hcharge : missing.card ≤ ∑ e ∈ repeated, (charge e).card := by
    have h := finite_endomap_collision_charge_identity Arc α α f r tail head repeated
      hr htail hkey hcharged
    change missing.card = ∑ e ∈ repeated, (charge e).card at h
    exact h.le
  have hdirty : dirty ⊆ repeated.biUnion parent := by
    intro u hu
    obtain ⟨_,a,b,p,hab,hpu,hua,hub,hpa,hpb⟩ := Finset.mem_filter.mp hu
    have hh := digraph_two_common_parents_edge_multiplicity α D a b u p
      hab hpu.symm hua hub hpa hpb
    apply Finset.mem_biUnion.mpr
    refine ⟨s(a,b), Finset.mem_filter.mpr hh, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hua
    · exact hub
  have hsubset : ∀ e ∈ repeated, charge e ⊆ parent e := by
    intro e he u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have hxe : edge x = e := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro z hz
    rw [← hxe] at hz
    change z ∈ s(head x, head (r (f x))) at hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact x.property
    · have hp : D.Adj (tail (r (f x))) (head (r (f x))) := (r (f x)).property
      rw [(hdata x).1] at hp
      exact hp
  have hm : ∀ e ∈ repeated, 2 ≤ (parent e).card := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have htwo : ∀ e ∈ repeated, (parent e).card = 2 → (charge e).card ≤ 1 := by
    intro e he hm2
    induction e using Sym2.ind with
    | h a b =>
      have hparentEq : parent s(a,b) =
          Finset.univ.filter (fun p => D.Adj p a ∧ D.Adj p b) := by
        ext p
        simp only [parent, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact ⟨h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
        · rintro ⟨ha,hb⟩ x hx
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact ha
          · exact hb
      rw [hparentEq] at hm2
      have hlim := digraph_two_parent_collision_charge_card_le_one α D choose hloop hori hchoice a b hm2
      have hsub : charge s(a,b) ⊆
          Finset.univ.filter (fun p => D.Adj p a ∧ D.Adj p b ∧ choose p a = choose p b) := by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        have heq : s(head x, head (r (f x))) = s(a,b) := (Finset.mem_filter.mp hx).2
        have hd := hdata x
        have ha : D.Adj (tail x) (head x) := x.property
        have hb : D.Adj (tail x) (head (r (f x))) := by
          have hp : D.Adj (tail (r (f x))) (head (r (f x))) := (r (f x)).property
          rw [hd.1] at hp
          exact hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases Sym2.eq_iff.mp heq with ⟨hxa,hxb⟩ | ⟨hxa,hxb⟩
        · exact ⟨by simpa [hxa] using ha, by simpa [hxb] using hb,
            by simpa [hxa,hxb] using hd.2.symm⟩
        · exact ⟨by simpa [hxb] using hb, by simpa [hxa] using ha,
            by simpa [hxa,hxb] using hd.2⟩
      have hh := Finset.card_le_card hsub
      exact hh.trans hlim
  have hparentPos : ∀ e ∈ edges, 1 ≤ (parent e).card := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨_,p,hpa,hpb⟩ := he
      apply Finset.card_pos.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hpa
      · exact hpb
  have hsum : (∑ e ∈ repeated, ((parent e).card - 1)) =
      (∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) - edges.card := by
    have hall := digraph_common_predecessor_overlap_incidence_identity α D
    have hs : (∑ e ∈ repeated, ((parent e).card - 1)) =
        ∑ e ∈ edges, ((parent e).card - 1) := by
      dsimp [repeated]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : 2 ≤ (parent e).card
      · simp [h]
      · have hp := hparentPos e he
        have hc : (parent e).card = 1 := by omega
        simp [h,hc]
    rw [hs]
    exact hall
  have hc : ∀ e ∈ repeated, (charge e).card ≤ (parent e).card := by
    intro e he
    exact Finset.card_le_card (hsubset e he)
  have hbudget := oriented_overlap_multiplicity_budget (Sym2 α) repeated
    (fun e => (parent e).card) (fun e => (charge e).card) hm hc htwo
  have hcomp : (∑ e ∈ repeated, (charge e).card) ≤ ∑ e ∈ repeated, (parent e).card := by
    exact Finset.sum_le_sum (fun e he => hc e he)
  change 2 * missing.card ≤ _
  rw [← hsum]
  omega
