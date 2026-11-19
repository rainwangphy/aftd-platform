import AFTD.Prelude

/-!
# truncation_periodic_auxiliary_port_certificate

Topic: graphs   Node: 92a40411bd66

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The specified exposed pairs on internal and consecutive auxiliary block links are disjoint for either matching bit.
-/

theorem truncation_periodic_auxiliary_port_certificate :
    ∀ b : Bool,
      let other : Fin 6 := if b then 0 else 1
      let nextOther : Fin 6 := if b then 1 else 0
      Disjoint ({2,5} : Finset (Fin 6)) {other,4} ∧
      Disjoint ({2,4} : Finset (Fin 6)) {other,3} ∧
      Disjoint ({4,3} : Finset (Fin 6)) {other,5} ∧
      Disjoint ({3,5} : Finset (Fin 6)) {2,other} ∧
      Disjoint ({3,other} : Finset (Fin 6)) {5,nextOther} := by
  decide
