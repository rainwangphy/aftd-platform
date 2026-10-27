import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphIsHopInv
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop_inverse_two_word

Topic: graphs   Node: a3098439c1ee

Provenance: helper lemma. Routine word-metric/cycle-factor assembly for IN-262 / OP-543, using the verified baseline normalization. The remaining quadratic diameter theorem is conjectural; no diameter assumption is silently discharged and no research advance is claimed.

The inverse of a normalized allowed permutation also has a two-hop realization, although it need not itself be normalized allowed.
-/

theorem simple_graph_normalized_hop_inverse_two_word {V : Type*} (G : SimpleGraph V)
    (h₀ p : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀)
    (hp : simple_graph_normalized_hop G h₀ p) :
    ∃ w : List (Equiv.Perm V), (∀ h ∈ w, simple_graph_is_hop G h) ∧
      w.length = 2 ∧ w.prod = p⁻¹ := by
  refine ⟨[(h₀ * p)⁻¹, h₀], ?_, rfl, ?_⟩
  · intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact simple_graph_is_hop_inv G (h₀ * p) hp
    · exact hh₀
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    group
