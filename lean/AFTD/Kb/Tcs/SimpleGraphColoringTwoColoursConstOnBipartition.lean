import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization

/-!
# simple_graph_coloring_two_colours_const_on_bipartition

Topic: graphs   Node: 0626b45f87c6

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(3): a 2-color coloring of a connected bipartite graph is constant on each side

Let G be a connected finite simple graph with a proper 2-coloring b : V → Fin 2, and let u0, w0 be adjacent with b u0 = 0 and b w0 = 1. Then every proper coloring c : V → Fin n using exactly 2 distinct colors satisfies c v = c u0 when b v = 0 and c v = c w0 when b v = 1.
-/

theorem simple_graph_coloring_two_colours_const_on_bipartition_fin_two (a : Fin 2) : ¬ a = 0 ↔ a = 1 := by fin_cases a <;> decide

theorem simple_graph_coloring_two_colours_const_on_bipartition {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hconn : G.Connected) (b : G.Coloring (Fin 2)) (u0 w0 : V) (hb0 : b u0 = 0) (hb1 : b w0 = 1)
    (hadj : G.Adj u0 w0) (c : G.Coloring (Fin n)) (hc : (Finset.univ.image c).card = 2) :
    ∀ v, c v = if b v = 0 then c u0 else c w0 := by
  classical
  have hne : c u0 ≠ c w0 := c.valid hadj
  have himg : Finset.univ.image c = {c u0, c w0} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp
    · rw [hc, Finset.card_pair hne]
  have hmem : ∀ v, c v = c u0 ∨ c v = c w0 := by
    intro v
    have : c v ∈ Finset.univ.image c := Finset.mem_image_of_mem _ (Finset.mem_univ v)
    rw [himg] at this
    simpa using this
  have key : ∀ {a z : V} (q : G.Walk a z), z = u0 → c a = if b a = 0 then c u0 else c w0 := by
    intro a z q
    induction q with
    | nil => intro hz; subst hz; simp [hb0]
    | @cons x z _ h q ih =>
    intro hz
    have e1 := ih hz
    have hbx : b x ≠ b z := b.valid h
    have hcx : c x ≠ c z := c.valid h
    rcases hmem x with hx | hx
    · by_cases hz : b z = 0
      · rw [if_pos hz] at e1
        exact absurd (hx.trans e1.symm) hcx
      · rw [if_neg hz] at e1
        have : b x = 0 := by
          rw [simple_graph_coloring_two_colours_const_on_bipartition_fin_two] at hz
          by_contra hx0; rw [simple_graph_coloring_two_colours_const_on_bipartition_fin_two] at hx0; exact hbx (hx0.trans hz.symm)
        rw [if_pos this, hx]
    · by_cases hz : b z = 0
      · rw [if_pos hz] at e1
        have : ¬ b x = 0 := fun h0 => hbx (h0.trans hz.symm)
        rw [if_neg this, hx]
      · rw [if_neg hz] at e1
        exact absurd (hx.trans e1.symm) hcx
  intro v
  obtain ⟨p⟩ := hconn.preconnected v u0
  exact key p rfl
