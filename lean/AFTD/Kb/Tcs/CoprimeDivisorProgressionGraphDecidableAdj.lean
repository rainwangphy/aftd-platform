import AFTD.Prelude
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraph

/-!
# coprime_divisor_progression_graph_decidable_adj

Topic: graphs   Node: 29741e20c0e5

Provenance: original. Related work: folklore

Adjacency in the coprime divisor progression graph coprime_divisor_progression_graph n a b is decidable via Classical.decRel.
-/

/-- Classical decidability instance for adjacency in the coprime divisor progression graph. -/
noncomputable instance coprime_divisor_progression_graph_decidable_adj (n : ℕ) (a b : ℤ) :
    DecidableRel (coprime_divisor_progression_graph n a b).Adj := Classical.decRel _
