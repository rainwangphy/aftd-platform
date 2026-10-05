import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Close
import AFTD.Kb.GameTheoryEconomics.Poc8Step
import AFTD.Kb.GameTheoryEconomics.Poc8Graph

/-!
# poc8_close_sound

Topic: fair_division   Node: c3267f59b234

Every vertex reached by the BFS iteration from r inside S lies in S and is reachable from r in the subgraph induced by S.
-/

theorem poc8_close_sound (S : Fin 8 → Bool) (r : Fin 8) (hr : S r = true) :
    ∀ k v, poc8_close S (fun w => w == r) k v = true →
      ∃ hv : S v = true, (poc8_graph.induce {x | S x = true}).Reachable ⟨r, hr⟩ ⟨v, hv⟩ := by
  intro k
  induction k with
  | zero =>
    intro v hv
    simp only [poc8_close, beq_iff_eq] at hv
    subst hv
    exact ⟨hr, SimpleGraph.Reachable.refl _⟩
  | succ k ih =>
    intro v hv
    simp only [poc8_close, poc8_step, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      List.mem_finRange, true_and] at hv
    rcases hv with hv | ⟨hSv, w, hw, hadj⟩
    · exact ih v hv
    · obtain ⟨hSw, hreach⟩ := ih w hw
      have hA : (poc8_graph.induce {x | S x = true}).Adj ⟨w, hSw⟩ ⟨v, hSv⟩ := hadj
      exact ⟨hSv, hreach.trans hA.reachable⟩
