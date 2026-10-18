import AFTD.Prelude
import AFTD.Kb.Tcs.HasCleanHandshakeSeq

/-!
# glove_number

Topic: combinatorics   Node: d2d8015696fb

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:222

The glove number $\mathrm{gl}(G)$ of a simple graph $G$ is the minimum number of gloves $k \in \mathbb{N}$ admitting a clean handshake sequence covering all edges of $G$, defined as the infimum of the set of such $k$.
-/

/-- The glove number of a simple graph. -/
noncomputable def glove_number {V : Type*} (G : SimpleGraph V) : ℕ := sInf {k : ℕ | has_clean_handshake_seq G k}
