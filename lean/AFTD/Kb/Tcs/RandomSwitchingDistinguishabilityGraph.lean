import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel
import AFTD.Kb.Tcs.ChannelDistinguishabilityGraph
import AFTD.Kb.Tcs.RandomSwitchingChannel
import AFTD.Kb.Tcs.SimpleGraphCategoricalProd

/-!
# random_switching_distinguishability_graph

Topic: information   Node: 3a5b620e57bd

Provenance: helper lemma. arXiv:2610.41977, Proposition 5.1, Equation (5.2)

For any discrete memoryless channels W_G and W_H and switching parameter p ∈ (0, 1), the distinguishability graph of the random switching channel is the categorical product D(W_G) × D(W_H).
-/

open Set

private lemma random_switching_distinguishability_graph_support_nonempty
    {A Y : Type*} [Fintype Y] (W : DiscreteMemorylessChannel A Y) (a : A) :
    ∃ y, 0 < W.prob a y := by
  by_contra h
  push Not at h
  have h0 : ∑ y, W.prob a y = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact le_antisymm (h y) (W.prob_nonneg a y)
  linarith [W.prob_sum a]

private lemma random_switching_distinguishability_graph_support_eq
    {A B Y Z : Type*} [Fintype Y] [Fintype Z]
    (W_G : DiscreteMemorylessChannel A Y) (W_H : DiscreteMemorylessChannel B Z)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ab : A × B) :
    {x : Y ⊕ Z | 0 < (random_switching_channel W_G W_H p hp0 hp1).prob ab x}
      = Sum.inl '' {y : Y | 0 < W_G.prob ab.1 y} ∪ Sum.inr '' {z : Z | 0 < W_H.prob ab.2 z} := by
  ext x
  cases x with
  | inl y =>
    rw [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      left
      simp only [random_switching_channel, mul_pos_iff_of_pos_left hp0] at h
      exact mem_image_of_mem Sum.inl h
    · rintro (h | h)
      · rcases (Set.mem_image Sum.inl _ _).mp h with ⟨y', hy', hEq⟩
        injection hEq with hEq'
        rw [hEq'] at hy'
        simp only [random_switching_channel, mul_pos_iff_of_pos_left hp0]
        exact hy'
      · rcases (Set.mem_image Sum.inr _ _).mp h with ⟨z, hz, hz'⟩
        exact absurd hz' (by simp)
  | inr z =>
    rw [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      right
      simp only [random_switching_channel] at h
      exact mem_image_of_mem Sum.inr (by
        rw [mul_pos_iff_of_pos_left] at h
        · exact h
        · linarith)
    · rintro (h | h)
      · rcases (Set.mem_image Sum.inl _ _).mp h with ⟨y', hy', hy'⟩
        exact absurd hy' (by simp)
      · rcases (Set.mem_image Sum.inr _ _).mp h with ⟨z', hz', hEq⟩
        injection hEq with hEq'
        rw [hEq'] at hz'
        simp only [random_switching_channel]
        rw [mul_pos_iff_of_pos_left]
        · exact hz'
        · linarith

private lemma random_switching_distinguishability_graph_disj
    {A B Y Z : Type*} [Fintype Y] [Fintype Z]
    (W_G : DiscreteMemorylessChannel A Y) (W_H : DiscreteMemorylessChannel B Z)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ab ab' : A × B) :
    Disjoint {x : Y ⊕ Z | 0 < (random_switching_channel W_G W_H p hp0 hp1).prob ab x}
        {x : Y ⊕ Z | 0 < (random_switching_channel W_G W_H p hp0 hp1).prob ab' x} ↔
      Disjoint {y : Y | 0 < W_G.prob ab.1 y} {y : Y | 0 < W_G.prob ab'.1 y} ∧
        Disjoint {z : Z | 0 < W_H.prob ab.2 z} {z : Z | 0 < W_H.prob ab'.2 z} := by
  rw [random_switching_distinguishability_graph_support_eq W_G W_H p hp0 hp1 ab,
    random_switching_distinguishability_graph_support_eq W_G W_H p hp0 hp1 ab']
  rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
  rw [Set.disjoint_image_iff Sum.inl_injective, Set.disjoint_image_iff Sum.inr_injective]
  simp only [Set.disjoint_image_inl_image_inr, Set.disjoint_image_inl_image_inr.symm, and_true, true_and]

/-- The distinguishability graph of a random switching channel is the categorical product of the component distinguishability graphs. -/
theorem random_switching_distinguishability_graph {A B Y Z : Type*} [Fintype Y] [Fintype Z]
    (W_G : DiscreteMemorylessChannel A Y) (W_H : DiscreteMemorylessChannel B Z)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    channel_distinguishability_graph (random_switching_channel W_G W_H p hp0 hp1) =
      simple_graph_categorical_prod (channel_distinguishability_graph W_G)
        (channel_distinguishability_graph W_H) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  simp only [channel_distinguishability_graph, simple_graph_categorical_prod]
  constructor
  · rintro ⟨hne, hdisj⟩
    obtain ⟨hdG, hdH⟩ := (random_switching_distinguishability_graph_disj W_G W_H p hp0 hp1 u v).mp hdisj
    refine ⟨⟨?_, hdG⟩, ⟨?_, hdH⟩⟩
    · intro h
      rw [← h] at hdG
      obtain ⟨y, hy⟩ := random_switching_distinguishability_graph_support_nonempty W_G u.1
      exact (Set.disjoint_left.mp hdG hy) hy
    · intro h
      rw [← h] at hdH
      obtain ⟨z, hz⟩ := random_switching_distinguishability_graph_support_nonempty W_H u.2
      exact (Set.disjoint_left.mp hdH hz) hz
  · rintro ⟨⟨hne1, hdG⟩, ⟨hne2, hdH⟩⟩
    refine ⟨?_, (random_switching_distinguishability_graph_disj W_G W_H p hp0 hp1 u v).mpr ⟨hdG, hdH⟩⟩
    intro h
    exact hne1 (congrArg Prod.fst h)
