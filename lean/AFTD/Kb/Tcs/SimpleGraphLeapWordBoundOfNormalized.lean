import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphLeapGroupNormalizedCosets
import AFTD.Kb.Tcs.SimpleGraphNormalizedWordToHopWord
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_leap_word_bound_of_normalized

Topic: graphs   Node: b3249627af21

Provenance: helper lemma. Routine word-metric/cycle-factor assembly for IN-262 / OP-543, using the verified baseline normalization. The remaining quadratic diameter theorem is conjectural; no diameter assumption is silently discharged and no research advance is claimed.

A signed normalized-word diameter bound D implies an actual hop-word diameter bound 2D+1. The normalized diameter bound remains an explicit hypothesis.
-/

theorem simple_graph_leap_word_bound_of_normalized {V : Type*} (G : SimpleGraph V)
    (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) (D : ℕ)
    (hD : ∀ k ∈ simple_graph_normalized_hop_group G h₀,
      ∃ w : List (Equiv.Perm V),
        (∀ p ∈ w, simple_graph_normalized_hop G h₀ p ∨
          simple_graph_normalized_hop G h₀ p⁻¹) ∧ w.length ≤ D ∧ w.prod = k) :
    ∀ g ∈ simple_graph_leap_group G,
      ∃ u : List (Equiv.Perm V), (∀ h ∈ u, simple_graph_is_hop G h) ∧
        u.length ≤ 2*D+1 ∧ u.prod = g := by
  intro g hg
  rcases simple_graph_leap_group_normalized_cosets G h₀ hh₀ g hg with h1 | h2
  · obtain ⟨w, hw, hlen, hprod⟩ := hD g h1
    obtain ⟨u, hu, hulen, huprod⟩ := simple_graph_normalized_word_to_hop_word G h₀ hh₀ w hw
    refine ⟨u, hu, ?_, by rw [huprod, hprod]⟩
    omega
  · obtain ⟨w, hw, hlen, hprod⟩ := hD (h₀⁻¹ * g) h2
    obtain ⟨u, hu, hulen, huprod⟩ := simple_graph_normalized_word_to_hop_word G h₀ hh₀ w hw
    refine ⟨h₀ :: u, ?_, ?_, ?_⟩
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact hh₀
      · exact hu h hh
    · simp only [List.length_cons]
      omega
    · simp only [List.prod_cons, huprod, hprod, mul_inv_cancel_left]
