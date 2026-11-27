import AFTD.Prelude
import AFTD.Kb.Tcs.ConceptClassRestrict

/-!
# concept_class_restrict_nonempty

Topic: learning   Node: 35d7668d7600

Provenance: helper lemma. Sanity check of concept_class_restrict; arXiv:2611.26721 (Littlestone dimension and its dual).

The restriction of a nonempty class of functions X → Bool to any subset Y of X is nonempty.
-/

theorem concept_class_restrict_nonempty {X : Type*} (H : Set (X → Bool)) (Y : Set X)
    (hH : H.Nonempty) : (concept_class_restrict H Y).Nonempty := hH.image _
