import AFTD.Prelude

/-!
# digraph_quasikernel_outneighbors

Topic: graphs   Node: 3299a7fadbc0

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; standard finite digraph definitions and quasi-kernel exchange.

The first out-neighborhood of a finite set of vertices in a digraph.
-/

def digraph_quasikernel_outneighbors {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q : Finset α) : Finset α :=
  Finset.univ.filter fun v => ∃ q ∈ Q, D.Adj q v

-- In a source-free digraph the first out-neighborhood of any quasi-kernel
-- is itself two-step out-dominating, even when it is not independent.
