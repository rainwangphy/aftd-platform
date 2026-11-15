import AFTD.Prelude

/-!
# good_slopes_fiber55_uncolored_gap_counterexample

Topic: elementary_number_theory   Node: 06de1dc4c8f7

Provenance: helper lemma. Counterexample identified in computation 27607 for the OP-1027 fiber investigation.

There are 55 points over Z/55 with at least 33 good unit directions and a collision in direction 1. This refutes the proposed bound of at most 32 good unit directions without the three-color assumption.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 15000

theorem good_slopes_fiber55_uncolored_gap_counterexample :
    ∃ S : Finset (ZMod 55 × ZMod 55), S.card = 55 ∧
      33 ≤ ((Finset.univ : Finset (ZMod 55)).filter fun a => IsUnit a ∧
        Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + a*p.1) S).card ∧
      ¬ Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + p.1) S := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let S : Finset (ZMod 55 × ZMod 55) := {
    (0,0),
    (0,11),
    (0,22),
    (0,33),
    (0,44),
    (1,10),
    (1,21),
    (1,32),
    (1,43),
    (1,54),
    (2,9),
    (2,20),
    (2,31),
    (2,42),
    (2,53),
    (3,8),
    (3,19),
    (3,30),
    (3,41),
    (3,52),
    (4,7),
    (4,18),
    (4,29),
    (4,40),
    (4,51),
    (5,6),
    (5,17),
    (5,28),
    (5,39),
    (5,50),
    (6,5),
    (6,16),
    (6,27),
    (6,38),
    (6,49),
    (7,4),
    (7,15),
    (7,26),
    (7,37),
    (7,48),
    (8,3),
    (8,14),
    (8,25),
    (8,36),
    (8,47),
    (9,2),
    (9,13),
    (9,24),
    (9,35),
    (9,46),
    (10,1),
    (10,12),
    (10,23),
    (10,34),
    (10,45)
  }
  let c : ZMod 55 →+* ZMod 11 := ZMod.castHom (by decide : 11 ∣ 55) (ZMod 11)
  let X : Finset (ZMod 55) := {0,1,2,3,4,5,6,7,8,9,10}
  let allowed55 : Finset (ZMod 55) := (Finset.univ : Finset (ZMod 55)).filter (fun a => IsUnit a ∧ c a ≠ 1)
  have hS : S.card = 55 := by decide
  have hX : (X.image c).card = X.card := by decide
  have hxin : Set.InjOn c X := Finset.card_image_iff.mp hX
  have hxset : S.image Prod.fst ⊆ X := by decide
  have hyset : S ⊆ (Finset.univ : Finset (ZMod 55 × ZMod 55)).filter (fun p => c p.2 + c p.1 = 0) := by decide
  have hallowed : allowed55.card = 36 := by decide
  have hgood : ∀ a ∈ allowed55, Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + a*p.1) S := by
    intro a ha p hp q hq h
    have ha1 : c a ≠ 1 := (Finset.mem_filter.mp ha).2.2
    have hy1 : c p.2 + c p.1 = 0 := (Finset.mem_filter.mp (hyset hp)).2
    have hy2 : c q.2 + c q.1 = 0 := (Finset.mem_filter.mp (hyset hq)).2
    have hmod := congrArg c h
    simp only [map_add, map_mul] at hmod
    have hmul : (c a - 1) * (c p.1 - c q.1) = 0 := by linear_combination hmod - hy1 + hy2
    have hnz : c a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hxeqmod : c p.1 = c q.1 := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hnz)
    have hxeq : p.1 = q.1 := hxin (hxset (Finset.mem_image.mpr ⟨p,hp,rfl⟩)) (hxset (Finset.mem_image.mpr ⟨q,hq,rfl⟩)) hxeqmod
    apply Prod.ext hxeq
    linear_combination h - a*hxeq
  refine ⟨S, hS, ?_, ?_⟩
  · have hsub : allowed55 ⊆ (Finset.univ : Finset (ZMod 55)).filter (fun a => IsUnit a ∧
        Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + a*p.1) S) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(Finset.mem_filter.mp ha).2.1, hgood a ha⟩
    have h := Finset.card_le_card hsub
    omega
  · intro hinj
    have hp : (0,0) ∈ S := by decide
    have hq : (1,54) ∈ S := by decide
    have heq : (0 : ZMod 55) + 0 = 54 + 1 := by decide
    exact (by decide : ((0,0) : ZMod 55 × ZMod 55) ≠ (1,54)) (hinj hp hq heq)
