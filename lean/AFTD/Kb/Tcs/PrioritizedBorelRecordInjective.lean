import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelRecordReplay

/-!
# prioritized_borel_record_injective

Topic: automata   Node: 190044579035

Provenance: helper lemma. Strategy reconstruction for arXiv:2611.10136, Conjecture 19.

Compatible finite histories with equal length and equal records of opponent branching choices are identical.
-/

theorem prioritized_borel_record_injective {A : Type} (own branch : List A → Bool)
    (policy forced : List A → A) (hist xs ys : List A)
    (hx : op1385Compatible own branch policy forced hist xs)
    (hy : op1385Compatible own branch policy forced hist ys)
    (hlen : xs.length = ys.length)
    (hrecord : op1385Record own branch hist xs = op1385Record own branch hist ys) : xs = ys := by
  have hx' := prioritized_borel_record_replay own branch policy forced hist xs hx
  have hy' := prioritized_borel_record_replay own branch policy forced hist ys hy
  rw [hlen, hrecord] at hx'
  have h := hx'.symm.trans hy'
  exact List.append_cancel_left (congrArg Prod.fst (Option.some.inj h))
