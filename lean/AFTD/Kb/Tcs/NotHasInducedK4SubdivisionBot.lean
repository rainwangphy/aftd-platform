import AFTD.Prelude
import AFTD.Kb.Tcs.HasInducedK4Subdivision

/-!
# not_has_induced_k4_subdivision_bot

Topic: graphs   Node: deb2df6e201e

Provenance: helper lemma. Helper for arXiv:2610.32404 Proposition 11.2 (PR-412).

The empty graph on any vertex type contains no induced subdivision of K4.
-/

theorem not_has_induced_k4_subdivision_bot (V : Type*) :
    ¬ has_induced_k4_subdivision (⊥ : SimpleGraph V) := by
  rintro ⟨b, hb, P, _⟩
  have h : b 0 = b 1 := SimpleGraph.reachable_bot.mp ⟨P ⟨(0, 1), by decide⟩⟩
  have := hb h
  norm_num at this
