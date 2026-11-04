import AFTD.Prelude

/-!
# sternDiatomic

Topic: elementary_number_theory   Node: 0952c1f943b6

Provenance: formalization of a published result. Source: scout/2611-01243-halving-partitions-and-hyperbinary-expansions.md:368

Stern's diatomic sequence s(n) is defined by s(0) = 0, s(1) = 1, s(2m) = s(m), and s(2m+1) = s(m) + s(m+1) for m ≥ 1.
-/

/-- Stern's diatomic sequence s(n). -/
def sternDiatomic : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  if h : (n + 2) % 2 = 0 then
    have : (n + 2) / 2 < n + 2 := Nat.div_lt_self (Nat.succ_pos (n + 1)) (by decide)
    sternDiatomic ((n + 2) / 2)
  else
    have : (n + 2) / 2 < n + 2 := Nat.div_lt_self (Nat.succ_pos (n + 1)) (by decide)
    have : (n + 2) / 2 + 1 < n + 2 := by omega
    sternDiatomic ((n + 2) / 2) + sternDiatomic ((n + 2) / 2 + 1)
termination_by n => n
