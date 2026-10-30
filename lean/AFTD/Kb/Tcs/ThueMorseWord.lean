import AFTD.Prelude

/-!
# thue_morse_word

Topic: combinatorics   Node: 85627274f827

Provenance: formalization of a published result. Source: arXiv:2610.10950

The n-th Thue-Morse word t_n over the alphabet {false, true}, defined recursively by t_0 = [false] and t_{n+1} obtained by replacing each false with [false, true] and each true with [true, false].
-/

/-- The n-th Thue-Morse word of length 2^n over {false, true}. -/
def thue_morse_word : ℕ → List Bool
| 0 => [false]
| n + 1 => (thue_morse_word n).flatMap (fun b => match b with | true => [true, false] | false => [false, true])
