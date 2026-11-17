import AFTD.Prelude

/-!
# op869_exposed_colors_forbidden

Topic: online_algorithms   Node: 4e05ab398733

Provenance: helper lemma. Online edge connection in arXiv:2610.41516 Lemma 2.5.

In a proper set-valued coloring, if each forbidden color appears on a neighbor of every vertex of T, then no vertex of T uses any forbidden color.
-/

/-- Adjacency to color representatives excludes their colors from a whole simulated block. -/
theorem op869_exposed_colors_forbidden {X γ : Type} [DecidableEq X] [DecidableEq γ] (G : SimpleGraph X)
    (colors : X → Finset γ) (T : Finset X) (forbidden : Finset γ)
    (hproper : ∀ x y, G.Adj x y → Disjoint (colors x) (colors y))
    (hexposure : ∀ c ∈ forbidden, ∀ x ∈ T, ∃ y, G.Adj x y ∧ c ∈ colors y) :
    Disjoint forbidden (T.biUnion colors) := by
  apply Finset.disjoint_left.mpr
  intro c hc hct
  obtain ⟨x, hx, hcx⟩ := Finset.mem_biUnion.mp hct
  obtain ⟨y, hxy, hcy⟩ := hexposure c hc x hx
  exact Finset.disjoint_left.mp (hproper x y hxy) hcx hcy
