import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameAttractor

/-!
# parity_game_attractor_superset

Topic: automata   Node: ccaa068f7337

Provenance: helper lemma. arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time): sanity lemma for the attractor definition

The attractor of a set U of vertices, for either player, contains U.
-/

theorem parity_game_attractor_superset {V : Type} [Fintype V] [DecidableEq V] (own : V → Bool)
    (E : V → V → Bool) (pl : Bool) (U : Finset V) : U ⊆ parity_game_attractor own E pl U := by
  unfold parity_game_attractor
  generalize Fintype.card V = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans Finset.subset_union_left
