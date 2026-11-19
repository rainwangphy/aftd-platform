import AFTD.Prelude

/-!
# parity_game_attractor

Topic: automata   Node: f2a53767fe83

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 2 (attractor set, as stage |V| of the inductive definition)

A game on a finite vertex type V is given by own : V → Bool (own v = true means Even owns v, false means Odd owns v), E : V → V → Bool (E v w = true means there is an edge from v to w) and prio : V → ℕ (the priority of each vertex). A player is a Boolean: true is Even, false is Odd. parity_game_attractor own E pl U (arguments in this order: owner map, edge relation, player, target set) is the finite set of vertices obtained from U by applying |V| times (|V| = the number of vertices) the one-step operator X ↦ X ∪ {v : (own v = pl and some w with E v w = true lies in X) or (own v ≠ pl and every w with E v w = true lies in X)}. This is stage |V| of the inductive definition of the pl-attractor of U (stage 0 is U, stage k+1 adds the vertices of player pl with a successor in stage k and the vertices of the other player all of whose successors are in stage k); the stages increase and are stationary from stage |V| on, so it is their union.
-/

/-- The attractor of a vertex set `U` for player `pl` (`true` = Even, `false` = Odd) in the game with owner map `own` and edge relation `E`: the `|V|`-th stage of the usual inductive definition, at which the increasing stages have become stationary. -/
def parity_game_attractor {V : Type} [Fintype V] [DecidableEq V] (own : V → Bool)
    (E : V → V → Bool) (pl : Bool) (U : Finset V) : Finset V :=
  (fun X : Finset V => X ∪ Finset.univ.filter (fun v =>
      (own v = pl ∧ ∃ w, E v w = true ∧ w ∈ X) ∨ (own v ≠ pl ∧ ∀ w, E v w = true → w ∈ X)))^[Fintype.card V] U
