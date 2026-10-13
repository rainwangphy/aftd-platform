import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHypomorphic

/-!
# poset_hypomorphic_refl

Topic: combinatorics   Node: 959786fe0f24

Provenance: helper lemma. Sanity lemma for poset_hypomorphic (arXiv:2610.12690).

Every ordered set is hypomorphic to itself.
-/

theorem poset_hypomorphic_refl (P : Type*) [PartialOrder P] : poset_hypomorphic P P :=
  ⟨Equiv.refl P, fun _ => ⟨OrderIso.refl _⟩⟩
