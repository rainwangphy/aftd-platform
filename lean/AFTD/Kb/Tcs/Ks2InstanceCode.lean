import AFTD.Prelude
import AFTD.Kb.Tcs.RatSelfDelimitingCode
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# ks2_instance_code

Topic: np_completeness   Node: 5bce7520a4ce

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1: binary encoding of an instance (alpha, d, v_1..v_m). Encoding choice (the paper fixes none): an input vector is given by a pair (t, w), t a rational and w a list of pairs of rationals, and stands for sqrt(t) times the vector with Gaussian-rational coordinates a_j + b_j i; this covers the paper's reduction, whose vectors are sqrt(alpha_r / q_v) times sign vectors.

With explicit arguments α : ℚ, d : ℕ and vs : List (ℚ × List (ℚ × ℚ)), in this order: the Bool word (List Bool) that is the concatenation of nat_self_delimiting_code d, then rat_self_delimiting_code α, then nat_self_delimiting_code of the length of vs, then, for each entry (t, w) of vs in order (List.flatMap): rat_self_delimiting_code t, nat_self_delimiting_code of the length of w, and for each pair (a, b) of w in order (List.flatMap) rat_self_delimiting_code a followed by rat_self_delimiting_code b.
-/

/-- The binary word encoding an instance `(α, d, vs)` of the algorithmic Kadison-Singer problem. -/
def ks2_instance_code (α : ℚ) (d : ℕ) (vs : List (ℚ × List (ℚ × ℚ))) : List Bool :=
  nat_self_delimiting_code d ++ rat_self_delimiting_code α ++
    nat_self_delimiting_code vs.length ++
    vs.flatMap (fun p => rat_self_delimiting_code p.1 ++ nat_self_delimiting_code p.2.length ++
      p.2.flatMap (fun z => rat_self_delimiting_code z.1 ++ rat_self_delimiting_code z.2))
