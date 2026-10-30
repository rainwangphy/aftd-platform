import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicHalfCoverSignaturePairsGeSeven

/-!
# condorcet_acyclic_cover_realizes_critical_signatures

Topic: social_choice   Node: df30afac8f6a

Provenance: helper lemma. IN-383, OP-19 campaign session9, 2026-10-30. General source-selection argument underlying the bounded activity-signature searches. Supporting structural lemma only; no new election bound or research novelty is claimed.

Suppose n=k+q induced acyclic vertex sets cover each vertex at least q times, and every set of at most k vertices has an outside common predecessor. Then every q-element subset of the n set indices occurs as the EXACT activity signature of some vertex. The relation has arbitrary finite order. This forces all ten signatures in the S2 three-of-five auxiliary and all twenty signatures in a six-support balanced S3 half-cover, but gives no upper bound on cohort multiplicity.
-/

open Finset
set_option maxHeartbeats 4000000

theorem condorcet_acyclic_cover_realizes_critical_signatures
    (m n k q : ℕ) (hn : n=k+q) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a,a∉J ∧ ∀ b∈J,R a b)
    (hU : ∀ v,WellFounded (fun a b : {a : Fin m // a∈U v} => R a.val b.val))
    (hcover : ∀ a,q≤(univ.filter fun v => a∈U v).card) :
    ∀ S : Finset (Fin n), S.card=q →
      ∃ a : Fin m,∀ v,a∈U v ↔ v∈S := by
  classical
  obtain ⟨r,_,_⟩ := hroot ∅ (by simp)
  have hsources : ∀ v,∃ b,∀ a∈U v,¬R a b := by
    intro v
    by_cases hne : (U v).Nonempty
    · obtain ⟨a,ha⟩ := hne
      obtain ⟨b,_,hmin⟩ := (hU v).has_min Set.univ ⟨⟨a,ha⟩,Set.mem_univ _⟩
      exact ⟨b.val,fun a ha hab => hmin ⟨a,ha⟩ (Set.mem_univ _) hab⟩
    · exact ⟨r,fun a ha => False.elim (hne ⟨a,ha⟩)⟩
  choose b hb using hsources
  intro S hS
  let W := univ \ S
  have hW : W.card=k := by
    dsimp only [W]
    rw [card_sdiff,inter_univ,card_univ,Fintype.card_fin,hS,hn]
    omega
  obtain ⟨a,_,ha⟩ := hroot (W.image b) (card_image_le.trans (by omega))
  have hav : ∀ v∈W,a∉U v := by
    intro v hv hau
    exact hb v a hau (ha (b v) (mem_image.mpr ⟨v,hv,rfl⟩))
  let I := univ.filter fun v => a∈U v
  have hIS : I ⊆ S := by
    intro v hv
    by_contra hnS
    exact hav v (mem_sdiff.mpr ⟨mem_univ _,hnS⟩) (mem_filter.mp hv).2
  have heq : I=S := eq_of_subset_of_card_le hIS (by
    rw [hS]
    exact hcover a)
  refine ⟨a,?_⟩
  intro v
  change a∈U v ↔ v∈S
  rw [← heq]
  simp [I]
