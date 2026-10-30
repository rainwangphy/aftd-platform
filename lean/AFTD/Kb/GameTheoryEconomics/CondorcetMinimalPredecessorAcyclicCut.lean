import AFTD.Prelude

/-!
# condorcet_minimal_predecessor_acyclic_cut

Topic: social_choice   Node: 17993716ca02

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

For k positive, a finite relation globally minimal under induced restriction among relations with the outside common predecessor property for sets of at most k vertices has an undominated set of exactly k+1 vertices crossing every nonempty induced acyclic subset.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimal_predecessor_acyclic_cut
    (m k : ℕ) (hk : 0 < k) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (A : Finset (Fin m)) (hAne : A.Nonempty)
    (hA : WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val)) :
    ∃ T : Finset (Fin m), T.card = k+1 ∧
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) ∧
      (∃ a ∈ T, a ∈ A) ∧ (∃ b ∈ T, b ∉ A) := by
  classical
  obtain ⟨a,ha⟩ := hAne
  obtain ⟨c,_,hc⟩ := hA.has_min Set.univ ⟨⟨a,ha⟩,Set.mem_univ _⟩
  have hsource : ∀ b ∈ A, ¬ R b c.val :=
    fun b hb hbc => hc ⟨b,hb⟩ (Set.mem_univ _) hbc
  let C := univ \ A
  have hproper : C ≠ univ := by
    intro heq
    have hm : c.val ∈ C := by rw [heq]; exact mem_univ _
    exact (mem_sdiff.mp hm).2 c.property
  have hnot : ¬(∀ J : Finset (Fin m), J ⊆ C → J.card ≤ k →
      ∃ a ∈ C, a ∉ J ∧ ∀ b ∈ J, R a b) :=
    fun h => hproper (hminimal C h)
  push_neg at hnot
  obtain ⟨J,hJC,hJcard,hJbad⟩ := hnot
  have hcJ : c.val ∉ J := fun h => (mem_sdiff.mp (hJC h)).2 c.property
  let T := insert c.val J
  have hTle : T.card ≤ k+1 := (card_insert_le _ _).trans (Nat.add_le_add_right hJcard 1)
  have hTbad : ¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b := by
    rintro ⟨d,hd,hdR⟩
    by_cases hdA : d ∈ A
    · exact hsource d hdA (hdR c.val (mem_insert_self _ _))
    · have hdC : d ∈ C := mem_sdiff.mpr ⟨mem_univ _,hdA⟩
      have hdJ : d ∉ J := fun h => hd (mem_insert_of_mem h)
      obtain ⟨b,hb,hnb⟩ := hJbad d hdC hdJ
      exact hnb (hdR b (mem_insert_of_mem hb))
  have hTcard : T.card = k+1 := by
    have hnotle : ¬ T.card ≤ k := fun h => hTbad (hroot T h)
    omega
  have hJpos : 0 < J.card := by
    have hcount : T.card = J.card+1 := card_insert_of_notMem hcJ
    omega
  obtain ⟨b,hb⟩ := card_pos.mp hJpos
  exact ⟨T,hTcard,hTbad,⟨c.val,mem_insert_self _ _,c.property⟩,
    ⟨b,mem_insert_of_mem hb,(mem_sdiff.mp (hJC hb)).2⟩⟩
