import AFTD.Prelude
import AFTD.Kb.Tcs.FinForwardPairsCard

/-!
# biclique_exact_forward_pairs_sum

Topic: combinatorics   Node: 4101b60612de

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

If bicliques own every forward pair at distance d exactly once on Fin g, the sum of their numbers of such pairs is g-d.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem biclique_exact_forward_pairs_sum
    {R : Type*} [Fintype R] (g d : ℕ) (hd : d ≤ g)
    (A B : R → Finset (Fin g))
    (hunique : ∀ i j : Fin g, j.val+d = i.val → ∃! r, i ∈ A r ∧ j ∈ B r) :
    (∑ r, (((A r).product (B r)).filter
      (fun p : Fin g × Fin g => p.2.val+d = p.1.val)).card) = g-d := by
  classical
  let C : R → Finset (Fin g × Fin g) := fun r =>
    ((A r).product (B r)).filter (fun p => p.2.val+d = p.1.val)
  let S := ((univ : Finset (Fin g)).product univ).filter
    (fun p : Fin g × Fin g => p.2.val+d = p.1.val)
  have hdis : (↑(univ : Finset R) : Set R).PairwiseDisjoint C := by
    intro r hr s hs hrs
    apply disjoint_left.mpr
    intro p hpr hps
    have hrd := (mem_filter.mp hpr).2
    have hri := (mem_product.mp (mem_filter.mp hpr).1)
    have hsi := (mem_product.mp (mem_filter.mp hps).1)
    obtain ⟨t, ht, huniq⟩ := hunique p.1 p.2 hrd
    exact hrs ((huniq r hri).trans (huniq s hsi).symm)
  have hcover : univ.biUnion C = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨r, hr, hpr⟩ := mem_biUnion.mp hp
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, (mem_filter.mp hpr).2⟩
    · intro hp
      have hdist := (mem_filter.mp hp).2
      obtain ⟨r, hr, huniq⟩ := hunique p.1 p.2 hdist
      exact mem_biUnion.mpr ⟨r, mem_univ _, mem_filter.mpr ⟨mem_product.mpr hr, hdist⟩⟩
  change (∑ r, (C r).card) = g-d
  rw [← card_biUnion hdis, hcover]
  exact fin_forward_pairs_card g d hd
