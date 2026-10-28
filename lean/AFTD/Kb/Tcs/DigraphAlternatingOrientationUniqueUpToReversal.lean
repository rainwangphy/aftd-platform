import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphExtIff
import AFTD.Kb.Tcs.DigraphIsAlternatingOrientation
import AFTD.Kb.Tcs.SimpleGraphIsRotationSystem
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_alternating_orientation_unique_up_to_reversal

Topic: graphs   Node: 544db06e36f9

Provenance: helper lemma. step towards three_connected_plane_eulerian_arborescence_minimizers_alternating

On any connected graph with a rotation system σ, an alternating orientation is uniquely determined up to reversal: any two alternating orientations D₁ and D₂ satisfy D₁ = D₂ or D₁ is the reversal of D₂.
-/

/-- On any connected graph with a rotation system σ, an alternating orientation is uniquely determined up to reversal: any two alternating orientations D₁ and D₂ satisfy D₁ = D₂ or D₁ is the reversal of D₂. -/
theorem digraph_alternating_orientation_unique_up_to_reversal {V : Type*}
    (G : SimpleGraph V) (hG : G.Connected) (σ : Equiv.Perm G.Dart)
    (hσ : simple_graph_is_rotation_system G σ)
    (D₁ D₂ : Digraph V)
    (hD₁ : digraph_is_alternating_orientation G σ D₁)
    (hD₂ : digraph_is_alternating_orientation G σ D₂) :
    D₁ = D₂ ∨ ∀ u v, D₁.Adj u v ↔ D₂.Adj v u := by
  classical
  let A : G.Dart → Prop := fun d =>
    (D₁.Adj d.toProd.1 d.toProd.2 ↔ D₂.Adj d.toProd.1 d.toProd.2)
  have hAσ : ∀ d : G.Dart, A (σ d) ↔ A d := by
    intro d
    dsimp only [A]
    have h1 := hD₁.2 d
    have h2 := hD₂.2 d
    tauto
  have hApow : ∀ (i : ℤ) (d : G.Dart), A ((σ ^ i) d) ↔ A d := by
    have key : ∀ (a : Equiv.Perm G.Dart), (∀ d, A (a d) ↔ A d) →
        ∀ d, A ((a * σ) d) ↔ A d := by
      intro a ha d
      rw [Equiv.Perm.mul_apply]
      exact (ha (σ d)).trans (hAσ d)
    have keyinv : ∀ (a : Equiv.Perm G.Dart), (∀ d, A (a d) ↔ A d) →
        ∀ d, A ((a * σ⁻¹) d) ↔ A d := by
      intro a ha d
      rw [Equiv.Perm.mul_apply]
      have hinv : A (σ⁻¹ d) ↔ A d := by
        have h := (hAσ (σ⁻¹ d)).symm
        simpa using h
      exact (ha (σ⁻¹ d)).trans hinv
    intro i d
    exact zpow_induction_right (P := fun a => ∀ d, A (a d) ↔ A d) (g := σ)
      (fun d => by simp) key keyinv i d
  have hsame : ∀ d e : G.Dart, d.toProd.1 = e.toProd.1 → (A d ↔ A e) := by
    intro d e hde
    obtain ⟨i, hi⟩ := hσ.2 d e hde
    rw [← hi]
    exact (hApow i d).symm
  have hrev : ∀ d : G.Dart,
      A ⟨(d.toProd.2, d.toProd.1), SimpleGraph.Adj.symm d.adj⟩ ↔ A d := by
    intro d
    dsimp only [A]
    have ho1 := (hD₁.1.1 d.toProd.1 d.toProd.2).mpr d.adj
    have ha1 := hD₁.1.2 d.toProd.1 d.toProd.2
    have ho2 := (hD₂.1.1 d.toProd.1 d.toProd.2).mpr d.adj
    have ha2 := hD₂.1.2 d.toProd.1 d.toProd.2
    tauto
  have hedge : ∀ {u v : V} (h : G.Adj u v) (d e : G.Dart),
      d.toProd.1 = u → e.toProd.1 = v → (A d ↔ A e) := by
    intro u v h d e hd he
    have h1 : A d ↔ A (⟨(u, v), h⟩ : G.Dart) := hsame d _ (by simpa using hd)
    have h2 : A (⟨(u, v), h⟩ : G.Dart) ↔ A (⟨(v, u), SimpleGraph.Adj.symm h⟩ : G.Dart) :=
      (hrev ⟨(u, v), h⟩).symm
    have h3 : A (⟨(v, u), SimpleGraph.Adj.symm h⟩ : G.Dart) ↔ A e :=
      hsame _ e (by simpa using he.symm)
    exact h1.trans (h2.trans h3)
  have hwalk : ∀ {u v : V} (p : G.Walk u v) (d e : G.Dart),
      d.toProd.1 = u → e.toProd.1 = v → (A d ↔ A e) := by
    intro u v p
    refine SimpleGraph.Walk.rec (motive := fun u v _ =>
      ∀ d e : G.Dart, d.toProd.1 = u → e.toProd.1 = v → (A d ↔ A e)) ?_ ?_ p
    · intro u d e hd he
      exact hsame d e (by rw [hd, he])
    · intro u w x h p' ih d e hd he
      have h1 : A d ↔ A (⟨(w, u), SimpleGraph.Adj.symm h⟩ : G.Dart) := hedge h d _ hd rfl
      have h2 : A (⟨(w, u), SimpleGraph.Adj.symm h⟩ : G.Dart) ↔ A e := ih _ e rfl he
      exact h1.trans h2
  have hall : ∀ d e : G.Dart, A d ↔ A e := by
    intro d e
    exact hwalk (Classical.choice (hG.preconnected d.toProd.1 e.toProd.1)) d e rfl rfl
  by_cases hne : Nonempty G.Dart
  · obtain ⟨d0⟩ := hne
    by_cases hb : A d0
    · left
      apply (digraph_ext_iff D₁ D₂).mpr
      intro u v
      by_cases huv : G.Adj u v
      · have hd : A (⟨(u, v), huv⟩ : G.Dart) := (hall _ d0).mpr hb
        simpa using hd
      · have h1 : ¬ D₁.Adj u v := by
          intro h
          exact huv ((hD₁.1.1 u v).mp (Or.inl h))
        have h2 : ¬ D₂.Adj u v := by
          intro h
          exact huv ((hD₂.1.1 u v).mp (Or.inl h))
        tauto
    · right
      intro u v
      by_cases huv : G.Adj u v
      · have hd : ¬ A (⟨(u, v), huv⟩ : G.Dart) := fun hA => hb ((hall _ d0).mp hA)
        have hd' : ¬ (D₁.Adj u v ↔ D₂.Adj u v) := hd
        have ho2 := (hD₂.1.1 u v).mpr huv
        have ha2 := hD₂.1.2 u v
        tauto
      · have h1 : ¬ D₁.Adj u v := by
          intro h
          exact huv ((hD₁.1.1 u v).mp (Or.inl h))
        have huv' : ¬ G.Adj v u := by
          intro h
          exact huv ((SimpleGraph.adj_comm G u v).mpr h)
        have h2 : ¬ D₂.Adj v u := by
          intro h
          exact huv' ((hD₂.1.1 v u).mp (Or.inl h))
        tauto
  · left
    apply (digraph_ext_iff D₁ D₂).mpr
    intro u v
    have h1 : ¬ D₁.Adj u v := by
      intro h
      exact hne ⟨⟨(u, v), ((hD₁.1.1 u v).mp (Or.inl h))⟩⟩
    have h2 : ¬ D₂.Adj u v := by
      intro h
      exact hne ⟨⟨(u, v), ((hD₂.1.1 u v).mp (Or.inl h))⟩⟩
    tauto
