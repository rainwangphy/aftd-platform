import AFTD.Prelude

/-!
# mdfrbf_compress

Topic: combinatorics   Node: cc3e65f227f1

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

The compression map: given a block W ⊆ Fin d, a colouring χ and an excluded colour c, send a set A of points outside W to its image together with W if A admits a nonempty subset whose image is c-coloured, and to its image alone otherwise. So T ∅ = ∅, and (T A) \ W always recovers the image of A.
-/

/-- Compression map T on subsets of the complement of W, used to remove the fan colour c. -/
noncomputable def mdfrbf_compress {d k : ℕ} (W : Finset (Fin d)) (χ : Finset (Fin d) → Fin k) (c : Fin k)
    (A : Finset ↥(Finset.univ \ W)) : Finset (Fin d) := by
  classical
  exact if A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧
      χ (B.map (Function.Embedding.subtype fun x => x ∈ Finset.univ \ W)) = c
    then A.map (Function.Embedding.subtype fun x => x ∈ Finset.univ \ W) ∪ W
    else A.map (Function.Embedding.subtype fun x => x ∈ Finset.univ \ W)
