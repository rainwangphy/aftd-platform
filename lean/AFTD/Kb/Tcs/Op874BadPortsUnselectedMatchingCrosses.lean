import AFTD.Prelude
import AFTD.Kb.Tcs.Op874UnselectedEdgeTwoBadNonownersImpossible
import AFTD.Kb.Tcs.Op874OneSidedPerfectMatchingCrosses

/-!
# op874_bad_ports_unselected_matching_crosses

Topic: graphs   Node: 59990c48d44e

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

Under the displayed local high-color palette and interface conditions, an involutive unselected-edge matching exchanges the two classes whenever the original matching does.
-/

theorem op874_bad_ports_unselected_matching_crosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate other : V → V)
    (t s x y : V → Fin 6)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (hother : ∀ v, other (other v) = v)
    (htsame : ∀ v, t (other v) = t v)
    (hlocal : ∀ v, flag v = false →
      2 ≤ (t v).val ∧ (t v).val ≤ 3 ∧ 4 ≤ (s v).val ∧ 4 ≤ (x v).val ∧
      2 ≤ (y v).val ∧ s v ≠ x v ∧ y v ≠ s v ∧ y v ≠ x v ∧ y v ≠ t v)
    (hcross : ∀ v, flag v = false → flag (other v) = false → y v ≠ y (other v)) :
    ∀ v, flag (other v) = !flag v := by
  apply op874_one_sided_perfect_matching_crosses flag mate other hmate hflip hother
  intro v hv
  cases ho : flag (other v) with
  | true => rfl
  | false =>
    obtain ⟨htl,hth,hs,hx,hy,hsx,hys,hyx,hyt⟩ := hlocal v hv
    obtain ⟨htl',hth',hs',hx',hy',hsx',hys',hyx',hyt'⟩ := hlocal (other v) ho
    have ht' : y (other v) ≠ t v := by simpa [htsame v] using hyt'
    exact False.elim (op874_unselected_edge_two_bad_nonowners_impossible
      (t v) (s v) (s (other v)) (x v) (x (other v)) (y v) (y (other v))
      htl hth hs hs' hx hx' hy hy' hsx hsx' hys hys' hyx hyx' hyt ht' (hcross v hv ho))
