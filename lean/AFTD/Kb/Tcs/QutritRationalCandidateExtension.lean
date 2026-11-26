import AFTD.Prelude
import AFTD.Kb.Tcs.QutritBosonicPairCode
import AFTD.Kb.Tcs.QutritRationalCandidateExtensionBlocks

/-!
# qutrit_rational_candidate_extension

Topic: quantum   Node: 119e090f44b6

Provenance: helper lemma. OP-2299; exact rational two-copy PPT bosonic extension, experiments 40204 and 40206.

The unnormalized-occupation representation of the explicit two-copy extension.
-/

noncomputable def qutrit_rational_candidate_extension :
    Matrix (Fin 3 × (Fin 2 → Fin 3)) (Fin 3 × (Fin 2 → Fin 3)) ℂ := Matrix.of fun p q => if p.1+p.2 0+p.2 1 = q.1+q.2 0+q.2 1 then qutrit_rational_candidate_extension_blocks (p.1+p.2 0+p.2 1) (qutrit_bosonic_pair_code (p.2 0) (p.2 1)) (qutrit_bosonic_pair_code (q.2 0) (q.2 1)) else 0
