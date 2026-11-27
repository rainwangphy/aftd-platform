import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Op1957ExtendibleIndependenceOfComplementMatching
import AFTD.Kb.Tcs.Op1957InducedComplementMinDegree
import AFTD.Kb.Tcs.Op1957MinDegreeForcesMatching

/-!
# large_extendible_high_degree_independence_number_bound

Topic: graphs   Node: 3cf57c4c0f3e

Provenance: formalization of a published result. Source: https://ajc.maths.uq.edu.au/pdf/12/ocr-ajc-v12-p59.pdf, Lemma 4, specialized to order 4k.

For k at least two, a connected k-extendible graph on 4k vertices with minimum degree at least 2k+1 has no independent vertex set larger than k.
-/

theorem large_extendible_high_degree_independence_number_bound
    (k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k) (hconn : G.Connected)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (U : Finset (Fin (4*k)))
    (hind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) : U.card ≤ k := by
  classical
  apply op1957_extendible_independence_of_complement_matching k G hext
  · intro I hI
    have hdegree' : ∀ v, k+I.card ≤ (G.neighborFinset v).card := by
      intro v
      have hh := hdegree v
      omega
    have hcard := Fintype.card_subtype_compl (fun v : Fin (4*k) => v ∈ I)
    simp only [Fintype.card_fin,Fintype.card_coe] at hcard
    have hsize : 2*k ≤ Fintype.card {v : Fin (4*k) // v ∉ I} := by
      rw [hcard]
      omega
    have hdeg := op1957_induced_complement_min_degree G I k hdegree'
    exact op1957_min_degree_forces_matching (G.induce {v | v ∉ I}) k hsize hdeg
  · exact hind
