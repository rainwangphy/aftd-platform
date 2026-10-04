import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket
import AFTD.Kb.GameTheoryEconomics.CyclicOffset

/-!
# hollow_shell_market

Topic: matching_markets   Node: f94f15366094

The cyclic Hollow-Shell marriage market C_n on n men and n women indexed by Z/nZ: man g ranks woman h at ((h - g) mod n) + 1 and woman h ranks man g at n - ((h - g) mod n), and each agent strictly prefers a partner with smaller rank.
-/

/-- The cyclic Hollow-Shell profile `C_n` (arXiv:2609.17418, eq. (1)): man `g` ranks woman `h` at `((h - g) mod n) + 1` and woman `h` ranks man `g` at `n - ((h - g) mod n)`; an agent prefers the partner it ranks lower. -/
def hollow_shell_market (n : ℕ) : MarriageMarket (Fin n) (Fin n) :=
  ⟨fun g h h' => cyclic_offset g h + 1 < cyclic_offset g h' + 1,
    fun h g g' => n - cyclic_offset g h < n - cyclic_offset g' h⟩
