import AFTD.Prelude

/-!
# period_doubling_word

Topic: combinatorics   Node: bc8e347cda53

Provenance: formalization of a published result. Source: arXiv:2602.16152

The sequence of finite period-doubling words w_n over Bool, defined by w_0 = [false] and w_{n+1} obtained by simultaneously replacing false with [false, true] and true with [false, false].
-/

/-- The n-th finite period-doubling word w_n over Bool. -/
def period_doubling_word : ℕ → List Bool
| 0 => [false]
| n + 1 => (period_doubling_word n).flatMap (fun b => match b with | false => [false, true] | true => [false, false])
