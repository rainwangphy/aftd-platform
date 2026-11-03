import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasSeparatorOfOrderTwo
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_reduces_to_separator_free

Topic: graphs   Node: a7a7b46e056a

Provenance: helper lemma. Induction assembly for the published separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5.

Given the two-vertex separator induction step, the triangle packing-cover inequality for all separator-free finite graphs implies it for all finite graphs.
-/

theorem simple_graph_triangle_cover_reduces_to_separator_free
    (hstep : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (A B : Finset V), A ∪ B = Finset.univ → A.card < Fintype.card V →
      B.card < Fintype.card V → (A ∩ B).card ≤ 2 →
      (∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y) →
      (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < Fintype.card V →
        ∀ H : SimpleGraph W,
          simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H) →
      simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G)
    (hcore : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ¬ simple_graph_has_separator_of_order_two V G →
      simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  classical
  have hall : ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ G : SimpleGraph V,
        simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V instV decV hcard G
      by_cases h : simple_graph_has_separator_of_order_two V G
      · obtain ⟨A,B,hcover,hA,hB,hcardAB,hcross⟩ := h
        apply hstep V G A B hcover hA hB hcardAB hcross
        intro W instW decW hlt H
        apply ih (Fintype.card W) (by omega) W rfl H
      · exact hcore V G h
  intro V instV decV G
  exact hall (Fintype.card V) V rfl G
