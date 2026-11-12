import AFTD.Prelude

/-!
# PrioritizedBorelStateTrace

Topic: automata   Node: 67b698770e03

Provenance: helper lemma. arXiv:2611.10136, Sections 4.1 and 5.1; abstract state traces of tree arenas

A state trace starts at the initial state and extends by a transition; the recorded branch and state sequence are stored in reverse order.
-/

inductive PrioritizedBorelStateTrace {Q : Type} (init : Q)
    (R : List Bool → Q → Bool → Q → Prop) : List Bool → Q → List Q → Prop
  | root : PrioritizedBorelStateTrace init R [] init [init]
  | step {v q qs d q'} : PrioritizedBorelStateTrace init R v q qs → R v q d q' →
      PrioritizedBorelStateTrace init R (d :: v) q' (q' :: qs)
