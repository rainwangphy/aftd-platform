import AFTD.Prelude
import AFTD.Kb.Tcs.SupertokenGraph

/-!
# supertoken_graph_regular_of_degree_le_s

Topic: graphs   Node: 646a46507c1b

Provenance: helper lemma. arXiv:2611.06275 Theorem 2.4

Let G be a finite simple d-regular graph on vertex type V, and let s and k be natural numbers such that k ≤ s. Then the supertoken graph supertoken_graph G k s is regular of degree k * d.
-/

lemma supertoken_graph_regular_of_degree_le_s_card_filter_le_k {V : Type*} [DecidableEq V]
    {k : ℕ} (x : Fin k → V) (v : V) :
    (Finset.univ.filter (fun i => x i = v)).card ≤ k := by
  have : (Finset.univ.filter (fun i => x i = v)).card ≤ (Finset.univ : Finset (Fin k)).card :=
    Finset.card_filter_le _ _
  simpa using this

lemma supertoken_graph_regular_of_degree_le_s_card_filter_le_s {V : Type*} [DecidableEq V]
    {k s : ℕ} (hk : k ≤ s) (x : Fin k → V) (v : V) :
    (Finset.univ.filter (fun i => x i = v)).card ≤ s :=
  (supertoken_graph_regular_of_degree_le_s_card_filter_le_k x v).trans hk

def supertoken_graph_regular_of_degree_le_s_to_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k s : ℕ) (hk : k ≤ s)
    (x : { x : Fin k → V // ∀ v : V, (Finset.univ.filter (fun i => x i = v)).card ≤ s })
    (p : Σ (i : Fin k), G.neighborSet (x.1 i)) :
    (supertoken_graph G k s).neighborSet x :=
  ⟨⟨Function.update x.1 p.1 p.2.1, supertoken_graph_regular_of_degree_le_s_card_filter_le_s hk _⟩, by
    dsimp [supertoken_graph]
    refine ⟨p.1, ?_, ?_⟩
    · dsimp
      rw [Function.update_self]
      exact p.2.2
    · intro j hj
      dsimp
      rw [Function.update_of_ne hj]⟩

lemma supertoken_graph_regular_of_degree_le_s_to_neighbor_inj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k s : ℕ) (hk : k ≤ s)
    (x : { x : Fin k → V // ∀ v : V, (Finset.univ.filter (fun i => x i = v)).card ≤ s }) :
    Function.Injective (supertoken_graph_regular_of_degree_le_s_to_neighbor G k s hk x) := by
  rintro ⟨i₁, u₁, hu₁⟩ ⟨i₂, u₂, hu₂⟩ h
  have hfn : Function.update x.1 i₁ u₁ = Function.update x.1 i₂ u₂ := by
    have h1 := congr_arg Subtype.val h
    exact congr_arg Subtype.val h1
  have h_ne1 : u₁ ≠ x.1 i₁ := by
    intro heq
    have hadj : G.Adj (x.1 i₁) u₁ := hu₁
    rw [heq] at hadj
    exact hadj.ne rfl
  have hi : i₁ = i₂ := by
    by_contra hne
    have h1 : Function.update x.1 i₁ u₁ i₁ = Function.update x.1 i₂ u₂ i₁ := by rw [hfn]
    simp only [Function.update_self] at h1
    rw [Function.update_of_ne hne] at h1
    exact h_ne1 h1
  subst hi
  have hu : u₁ = u₂ := by
    have h1 : Function.update x.1 i₁ u₁ i₁ = Function.update x.1 i₁ u₂ i₁ := by rw [hfn]
    simp only [Function.update_self] at h1
    exact h1
  subst hu
  rfl

lemma supertoken_graph_regular_of_degree_le_s_to_neighbor_surj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k s : ℕ) (hk : k ≤ s)
    (x : { x : Fin k → V // ∀ v : V, (Finset.univ.filter (fun i => x i = v)).card ≤ s }) :
    Function.Surjective (supertoken_graph_regular_of_degree_le_s_to_neighbor G k s hk x) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, hadj, heq⟩ := hy
  have hu : y.1 i ∈ G.neighborSet (x.1 i) := hadj
  refine ⟨⟨i, ⟨y.1 i, hu⟩⟩, ?_⟩
  ext1
  ext1
  ext j
  dsimp [supertoken_graph_regular_of_degree_le_s_to_neighbor]
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
  · rw [Function.update_of_ne hji]
    exact heq j hji

open scoped Classical in
/-- The supertoken graph of a d-regular graph with k ≤ s tokens is regular of degree kd. -/
theorem supertoken_graph_regular_of_degree_le_s {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (s : ℕ) (k : ℕ) (hk : k ≤ s) :
    (supertoken_graph G k s).IsRegularOfDegree (k * d) := by
  intro x
  have hcard : Fintype.card ((supertoken_graph G k s).neighborSet x) = k * d := by
    have e := Equiv.ofBijective (supertoken_graph_regular_of_degree_le_s_to_neighbor G k s hk x)
      ⟨supertoken_graph_regular_of_degree_le_s_to_neighbor_inj G k s hk x,
       supertoken_graph_regular_of_degree_le_s_to_neighbor_surj G k s hk x⟩
    rw [← Fintype.card_congr e]
    rw [Fintype.card_sigma]
    simp_rw [SimpleGraph.card_neighborSet_eq_degree]
    simp_rw [hreg (x.1 _)]
    simp
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact hcard
