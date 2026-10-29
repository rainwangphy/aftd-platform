import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.WildCompleteThirteenPartitionTemplate
import AFTD.Kb.Tcs.WildCompleteThirteenOneSwapRepairObstruction
import AFTD.Kb.Tcs.WildNumberCompleteGraphLargeEq
import AFTD.Kb.Tcs.WildNumberCompleteOddEqIffOptimalPartition
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_no_closed_union_of_blocks

Topic: graphs   Node: 8dee46498cce

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

If every used color crosses every nonempty proper cut of the block labels under p, then no nonempty proper vertex set that is a union of p-fibers is closed under a used color.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_no_closed_union_of_blocks {n k q : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (p : Fin n → Fin q)
    (hcut : ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin q)),
      S.Nonempty → S ≠ Finset.univ →
      ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (U : Finset (Fin n))
    (hU : U.Nonempty) (hproper : U ≠ Finset.univ)
    (hsat : ∀ u ∈ U, ∀ v, p v = p u → v ∈ U) : ¬w279_closed c (c e) U := by
  classical
  intro hcl
  let S : Finset (Fin q) := U.image p
  have hS : S.Nonempty := hU.image p
  have hSp : S ≠ Finset.univ := by
    intro hh
    apply hproper
    apply Finset.eq_univ_of_forall
    intro v
    have hv : p v ∈ S := hh ▸ Finset.mem_univ _
    obtain ⟨u,hu,hp⟩ := Finset.mem_image.1 hv
    exact hsat u hu v hp.symm
  obtain ⟨u,v,huv,hu,hv,hc⟩ := hcut e S hS hSp
  obtain ⟨x,hx,hpx⟩ := Finset.mem_image.1 hu
  have huU := hsat x hx u hpx.symm
  have hvU := hcl u huU v huv hc
  exact hv (Finset.mem_image_of_mem p hvU)
