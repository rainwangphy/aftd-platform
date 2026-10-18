import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique

/-!
# op_258_forces

Topic: combinatorics   Node: 993742bb58bc

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

The decay profile a forces a monochromatic K_k if for all sufficiently large n, every a-bounded colouring of the edges of K_n has a monochromatic K_k.
-/

/-- Forcing predicate: `a` forces a monochromatic `K_k` if all sufficiently large complete graphs, under any `a`-bounded edge colouring, contain a monochromatic `K_k`. -/
def op_258_forces (a : ℕ+ → ℝ) (k : ℕ) : Prop := ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
    op_258_bounded a n c → op_258_has_mono_clique n c k
