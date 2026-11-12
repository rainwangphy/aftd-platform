import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelFiniteHistoryShadow

/-!
# prioritized_borel_constrained_history_shadow

Topic: automata   Node: ac718d1a9759

Provenance: helper lemma.

A prefix-closed finite-alphabet history tree has an infinite branch meeting pointwise allowed-value constraints whenever arbitrarily long constrained histories exist.
-/

theorem prioritized_borel_constrained_history_shadow (A : Type) [Fintype A]
    (P : List A → Prop) (allowed : ℕ → A → Prop)
    (hprefix : ∀ xs ys, P (xs ++ ys) → P xs)
    (hdepth : ∀ n, ∃ xs : List A, xs.length = n ∧ P xs ∧
      ∀ (i : ℕ) (hi : i < xs.length), allowed i xs[i]) :
    ∃ f : ℕ → A, (∀ n, P (List.ofFn (fun i : Fin n => f i))) ∧
      ∀ i, allowed i (f i) := by
  classical
  let Q : List A → Prop := fun xs => P xs ∧
    ∀ (i : ℕ) (hi : i < xs.length), allowed i xs[i]
  have hQprefix : ∀ xs ys, Q (xs ++ ys) → Q xs := by
    intro xs ys h
    refine ⟨hprefix xs ys h.1, ?_⟩
    intro i hi
    have hh := h.2 i (by simp; omega)
    rw [List.getElem_append_left hi] at hh
    exact hh
  have hQdepth : ∀ n, ∃ xs : List A, xs.length = n ∧ Q xs := by
    intro n
    obtain ⟨xs, hlen, hp, ha⟩ := hdepth n
    exact ⟨xs, hlen, hp, ha⟩
  obtain ⟨f, hf⟩ := prioritized_borel_finite_history_shadow A Q hQprefix hQdepth
  refine ⟨f, fun n => (hf n).1, ?_⟩
  intro i
  have hh := (hf (i+1)).2 i (by simp)
  simpa only [List.getElem_ofFn] using hh
