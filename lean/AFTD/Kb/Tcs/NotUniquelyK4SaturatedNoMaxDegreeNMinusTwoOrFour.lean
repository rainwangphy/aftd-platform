import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated

/-!
# not_uniquely_k4_saturated_no_max_degree_n_minus_two_or_four

Topic: graphs   Node: 887112a42c71

Provenance: original. Related work: refutes `uniquely_k4_saturated_no_max_degree_n_minus_two_or_four`

The statement `uniquely_k4_saturated_no_max_degree_n_minus_two_or_four` is false: The theorem quantifies over ALL n : ℕ, including n = 0 and n = 1, and is false there.

Take n = 0 and G = ⊥ : SimpleGraph (Fin 0) (the unique graph on the empty vertex set). Then:
* `is_uniquely_clique_saturated G 4` holds VACUOUSLY: there is no Finset of the empty type with card 4 (so no 4-clique exists), and `Gᶜ.edgeSet = ∅` (there are no vertex pairs at all), so the `∀ e ∈ Gᶜ.edgeSet, ∃! ...` condition is vacuous.
* `G.maxDegree = 0` (maximum degree of the empty graph is 0).
* In ℕ, `0 - 2 = 0` and `0 - 4 = 0` (truncated subtraction).

Hence the conclusion `G.maxDegree ≠ n - 2 ∧ G.maxDegree ≠ n - 4` reduces to `0 ≠ 0 ∧ 0 ≠ 0`, which is false. So the claimed inequality `G.maxDegree ≠ n - 2` fails for n = 0.

The same happens for n = 1 with G = ⊤ : SimpleGraph (Fin 1) (equivalently ⊥, since a single-vertex graph has no edges): no 4-clique exists, and `⊤ᶜ = ⊥` so `edgeSet = ∅`, making the graph vacuously uniquely K₄-saturated; `maxDegree = 1 - 1 = 0 = 1 - 2 = n - 2`. So `G.maxDegree ≠ n - 2` fails here too, with a nonempty vertex set.

Both counterexamples are checked in Lean. The published theorem (arXiv:2611.13656, Thm 3.1) surely assumes a lower bound on n (the interesting range n ≥ 5 or so); the formal statement as given dropped that hypothesis, making it false at the degenerate values n = 0, 1.
-/

open scoped Classical in
theorem not_uniquely_k4_saturated_no_max_degree_n_minus_two_or_four : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : is_uniquely_clique_saturated G 4), G.maxDegree ≠ n - 2 ∧ G.maxDegree ≠ n - 4) := by
  intro h
  have hG0 : is_uniquely_clique_saturated (⊥ : SimpleGraph (Fin 0)) 4 := by
    unfold is_uniquely_clique_saturated
    refine ⟨?_, ?_⟩
    · intro s hs
      have hc := hs.card_eq
      have : s = ∅ := Finset.eq_empty_of_isEmpty s
      rw [this] at hc
      simp at hc
    · intro e he
      exact isEmptyElim e
  have key := h 0 (⊥ : SimpleGraph (Fin 0)) hG0
  apply key.1
  simp
