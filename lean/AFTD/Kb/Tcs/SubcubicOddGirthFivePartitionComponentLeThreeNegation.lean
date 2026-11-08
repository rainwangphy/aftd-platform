import AFTD.Prelude

/-!
# subcubic_odd_girth_five_partition_component_le_three_negation

Topic: graphs   Node: 6986a7333c68

Provenance: original. Related work: arXiv:2611.05178 Question 5.4 -- Weighted Max Cut in Subcubic Graphs

It is not the case that every finite simple graph with maximum degree at most 3, clique-free of order 3, and not bipartite admits a partition of its vertex set into an independent set L and a complement R = Lᶜ such that every connected component of the induced subgraph G[R] has order at most 3.
-/

set_option maxHeartbeats 4000000
universe u

/-- The Wagner graph (Möbius ladder M8): on `ULift (Fin 8)`, vertex `i` is adjacent
to `i+1` and to `i+4` (mod 8). It is cubic, triangle-free and not bipartite. -/
def subcubic_odd_girth_five_partition_component_le_three_negation_wg :
    SimpleGraph (ULift.{u, 0} (Fin 8)) :=
  SimpleGraph.fromRel fun i j => j.down = i.down + 1 ∨ j.down = i.down + 4

instance subcubic_odd_girth_five_partition_component_le_three_negation_wg_dec :
    DecidableRel subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.Adj := by
  unfold subcubic_odd_girth_five_partition_component_le_three_negation_wg SimpleGraph.fromRel
  infer_instance

/-- The Wagner graph has maximum degree at most 3. -/
theorem subcubic_odd_girth_five_partition_component_le_three_negation_wg_maxDegree :
    subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.maxDegree ≤ 3 := by
  decide

/-- The Wagner graph is triangle-free (clique-free of order 3). -/
theorem subcubic_odd_girth_five_partition_component_le_three_negation_wg_cliqueFree :
    subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.CliqueFree 3 := by
  unfold SimpleGraph.CliqueFree
  decide

/-- The Wagner graph is not bipartite (it contains an odd cycle). -/
theorem subcubic_odd_girth_five_partition_component_le_three_negation_wg_not_bipartite :
    ¬ subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.IsBipartite := by
  rw [SimpleGraph.IsBipartite, SimpleGraph.Colorable]
  rintro ⟨c⟩
  have key : ∀ f : ULift.{u, 0} (Fin 8) → Fin 2,
      ∃ i j : ULift.{u, 0} (Fin 8),
        subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.Adj i j ∧ f i = f j := by
    decide
  obtain ⟨i, j, hij, heq⟩ := key c.toFun
  exact c.valid hij heq

/-- Key finite fact for the Wagner graph: for every independent vertex set `L`
there is a vertex `v` of the complement whose connected component in the induced
complement graph has at least four vertices. -/
theorem subcubic_odd_girth_five_partition_component_le_three_negation_wg_key :
    ∀ L : Finset (ULift.{u, 0} (Fin 8)),
      (∀ x ∈ L, ∀ y ∈ L, x ≠ y →
        ¬ subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}.Adj x y) →
      ∃ v : ↥((↑L)ᶜ : Set (ULift.{u, 0} (Fin 8))),
        4 ≤ (Finset.univ.filter (fun w =>
          (SimpleGraph.induce (↑L)ᶜ
            subcubic_odd_girth_five_partition_component_le_three_negation_wg.{u}).Reachable v w)).card := by
  decide

/-- Bridge lemma: if some component of the complement-induced graph `G.induce Kᶜ`
contains at least four vertices (witnessed by a Finset `S` of vertices reachable
from `v`), then the hypothesis that every such component has at most three
vertices fails. Stated with `Nat.card` so no `Classical` Fintype scope is needed. -/
lemma subcubic_odd_girth_five_partition_component_le_three_negation_card_contra
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Set V) (v : ↥(Kᶜ)) {S : Finset ↥(Kᶜ)}
    (hS : 4 ≤ S.card)
    (hSreach : ∀ w ∈ S, (G.induce Kᶜ).Reachable v w)
    (hcomp : ∀ C : G.ComponentCompl K, Nat.card C ≤ 3) : False := by
  classical
  let C₀ : G.ComponentCompl K := G.componentComplMk (v := v.val) v.prop
  have hC₀ : Nat.card C₀ ≤ 3 := hcomp C₀
  have hmem : ∀ w ∈ S, (w.val : V) ∈ C₀ := by
    intro w hw
    have heq : G.componentComplMk (v := w.val) w.prop = C₀ := by
      simp only [C₀]
      unfold SimpleGraph.componentComplMk
      exact (SimpleGraph.ConnectedComponent.sound (hSreach w hw)).symm
    rw [← heq]
    exact G.componentComplMk_mem w.prop
  have hinj : Function.Injective
      (fun w : ↥S => (⟨w.val.val, hmem w.val w.prop⟩ : {x : V // x ∈ C₀})) := by
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  have hle : Fintype.card ↥S ≤ Fintype.card {x : V // x ∈ C₀} :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe] at hle
  have hC₀' : Fintype.card {x : V // x ∈ C₀} ≤ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hC₀
  omega

/-- Refutation of Question 5.4 of arXiv:2611.05178: not every subcubic triangle-free non-bipartite graph admits an independent set whose complement has all connected components of order at most 3. -/
theorem subcubic_odd_girth_five_partition_component_le_three_negation :
    ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.maxDegree ≤ 3 → G.CliqueFree 3 → ¬G.IsBipartite →
        ∃ L : Finset V, G.induce (L : Set V) = ⊥ ∧
          ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
            open scoped Classical in Fintype.card C ≤ 3) := by
  intro H
  classical
  obtain ⟨L, hind, hcomp⟩ := H subcubic_odd_girth_five_partition_component_le_three_negation_wg
    subcubic_odd_girth_five_partition_component_le_three_negation_wg_maxDegree
    subcubic_odd_girth_five_partition_component_le_three_negation_wg_cliqueFree
    subcubic_odd_girth_five_partition_component_le_three_negation_wg_not_bipartite
  have hL : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      ¬ subcubic_odd_girth_five_partition_component_le_three_negation_wg.Adj x y := by
    intro x hx y hy hxy hadj
    have hadj' : (subcubic_odd_girth_five_partition_component_le_three_negation_wg.induce
        (↑L)).Adj ⟨x, by simpa using hx⟩ ⟨y, by simpa using hy⟩ := by
      rwa [SimpleGraph.induce_adj]
    rw [hind] at hadj'
    exact (SimpleGraph.bot_adj _ _).mp hadj'
  obtain ⟨v, hv⟩ :=
    subcubic_odd_girth_five_partition_component_le_three_negation_wg_key L hL
  have hcomp' : ∀ C : subcubic_odd_girth_five_partition_component_le_three_negation_wg.ComponentCompl (↑L),
      Nat.card C ≤ 3 := by
    intro C
    rw [Nat.card_eq_fintype_card]
    exact hcomp C
  refine subcubic_odd_girth_five_partition_component_le_three_negation_card_contra
    subcubic_odd_girth_five_partition_component_le_three_negation_wg (↑L : Set _) v
    (S := Finset.univ.filter (fun w =>
      (SimpleGraph.induce (↑L)ᶜ
        subcubic_odd_girth_five_partition_component_le_three_negation_wg).Reachable v w)) ?_ ?_ hcomp'
  · exact hv
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
