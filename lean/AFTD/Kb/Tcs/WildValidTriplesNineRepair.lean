import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineSatCore
import AFTD.Kb.Tcs.WildValidTriplesNineEncodingPartA
import AFTD.Kb.Tcs.WildValidTriplesNineEncodingPartB
import AFTD.Kb.Tcs.WildValidTriplesNineEncodingPartC
import AFTD.Kb.Tcs.WildValidTriplesNineEncodingPartD

/-!
# wild_valid_triples_nine_repair

Topic: graphs   Node: c77a1ec92d89

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed. The former combined helper timed out in the180-second interactive gate. This is the SAME checked certificate and mathematical interpretation, split into a core and four soundness modules; no gate budget, axiom or mathematical statement is weakened.

For any normalized symmetric row-injective array on an arbitrary vertex/color type, take nine distinct vertices. If their first triple has the indicated invalidity witness and the other two triples are valid, a permutation rearranges the nine vertices into three valid triples. Array values may lie outside the nine vertices. This is a validity repair only; it does not eliminate larger seals.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem wild_valid_triples_nine_repair {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : (A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3))
    (hT2 : (A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6)) : ∃ σ : Equiv.Perm (Fin 9),∀ t : Fin 3,
      A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+1,by omega⟩))≠(v (σ ⟨3*t.val+2,by omega⟩)) ∧ A (v (σ ⟨3*t.val+0,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+1,by omega⟩)) ∧ A (v (σ ⟨3*t.val+1,by omega⟩)) (v (σ ⟨3*t.val+2,by omega⟩))≠(v (σ ⟨3*t.val+0,by omega⟩)) := by
  change in342_nine_goal A v
  by_contra hno
  have hF : (in342_nine_val A v).satisfies_fmla in342_nine_formula := (in342_nine_sat_and (in342_nine_sat_and (wild_valid_triples_nine_encoding_part_a A hdiag hsym hinj v hv hbad hT1 hT2 hno) (wild_valid_triples_nine_encoding_part_b A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (wild_valid_triples_nine_encoding_part_c A hdiag hsym hinj v hv hbad hT1 hT2 hno) (wild_valid_triples_nine_encoding_part_d A hdiag hsym hinj v hv hbad hT1 hT2 hno)))
  exact wild_valid_triples_nine_sat_core (in342_nine_val A v) hF
