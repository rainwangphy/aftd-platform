import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUnsafePivotStableGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutUnsafePivotStableProfile
import AFTD.Kb.GameTheoryEconomics.IsMaxcutNeutralPivotSafe
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_neutral_pivot_safe_not_necessary

Topic: equilibria   Node: 249392029e1c

Provenance: helper lemma. Independent exhaustive finite checks in experiments 16728 and 16729.

A full graph and its vertex deletion may both be strongly stable, with exactly one restored-vertex conflict, while that conflict neighbor is not neutral-pivot safe. Thus the pivot-safety sufficient condition is not necessary for a particular extension.
-/

instance : DecidableRel maxcut_unsafe_pivot_stable_graph.Adj := by
  unfold maxcut_unsafe_pivot_stable_graph
  infer_instance

/-- Strong stability is equivalent to the absence of a strongly improving coalition move
that only records the destination colouring on the coalition itself. -/
theorem maxcut_neutral_pivot_safe_not_necessary_se_iff_restrict {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) :
    is_maxcut_strong_equilibrium G σ ↔
      ∀ S : Finset V, ¬ ∃ f : ↥S → Fin k, S.Nonempty ∧
        ∀ v : ↥S, maxcut_utility G σ (v : V) <
          maxcut_utility G (fun x => if h : x ∈ S then f ⟨x, h⟩ else σ x) (v : V) := by
  unfold is_maxcut_strong_equilibrium is_maxcut_strong_deviation
  constructor
  · rintro h S ⟨f, hne, himp⟩
    exact h S (fun x => if hx : x ∈ S then f ⟨x, hx⟩ else σ x)
      ⟨hne, fun x hx => by simp [hx], fun v hv => himp ⟨v, hv⟩⟩
  · rintro h S τ ⟨hne, hoff, himp⟩
    refine h S ⟨fun v => τ v.1, hne, fun v => ?_⟩
    have hext : (fun x => if hx : x ∈ S then (fun w : ↥S => τ w.1) ⟨x, hx⟩ else σ x) = τ := by
      funext x
      by_cases hx : x ∈ S
      · simp [hx]
      · simp [hx, hoff x hx]
    simp only [hext]
    exact himp v.1 v.2

theorem maxcut_neutral_pivot_safe_not_necessary :
    is_maxcut_strong_equilibrium maxcut_unsafe_pivot_stable_graph maxcut_unsafe_pivot_stable_profile ∧
    is_maxcut_strong_equilibrium (maxcut_unsafe_pivot_stable_graph.induce (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)))
      (fun x : (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)) => maxcut_unsafe_pivot_stable_profile x.1) ∧
    (Finset.univ.filter fun w => maxcut_unsafe_pivot_stable_graph.Adj (0 : Fin 6) w ∧ maxcut_unsafe_pivot_stable_profile w = maxcut_unsafe_pivot_stable_profile 0) = {3} ∧
    ∃ u : (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)), u.1 = 3 ∧ ¬ is_maxcut_neutral_pivot_safe (maxcut_unsafe_pivot_stable_graph.induce (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)))
      (fun x : (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)) => maxcut_unsafe_pivot_stable_profile x.1) u := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (maxcut_neutral_pivot_safe_not_necessary_se_iff_restrict _ _).2 ?_
    decide
  · refine (maxcut_neutral_pivot_safe_not_necessary_se_iff_restrict _ _).2 ?_
    decide
  · have h : ∀ w : Fin 6,
        (maxcut_unsafe_pivot_stable_graph.Adj (0 : Fin 6) w ∧
          maxcut_unsafe_pivot_stable_profile w = maxcut_unsafe_pivot_stable_profile 0) ↔ w = 3 := by
      decide
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact h w
  · refine ⟨⟨3, by decide⟩, rfl, ?_⟩
    intro hsafe
    let C : Finset (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)) := {⟨1, by decide⟩, ⟨3, by decide⟩}
    let τ : (↑(Finset.univ.erase (0 : Fin 6)) : Set (Fin 6)) → Fin 3 :=
      fun x => if x.1 = 3 then 1 else if x.1 = 1 then 0 else maxcut_unsafe_pivot_stable_profile x.1
    exact hsafe C τ (by decide) (by decide) (by decide) (by decide) (by decide)
