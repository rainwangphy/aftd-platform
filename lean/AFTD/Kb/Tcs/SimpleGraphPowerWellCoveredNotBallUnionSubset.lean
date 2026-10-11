import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphExistsMaximalIndepSuperset

/-!
# simple_graph_power_well_covered_not_ball_union_subset

Topic: graphs   Node: 0ad1d5727ad5

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Lemma 2.7. The proof uses well-coveredness directly (two maximal independent sets of different sizes) instead of the independence number.

Let G be a finite graph and d ≥ 1 with G^d well-covered. Then there are no vertices s, t, w with d_G(s, t) ≥ d + 1 and B_d(s) ∪ B_d(t) ⊆ B_d(w), where B_d(x) is the set of vertices at distance at most d from x.
-/

theorem simple_graph_power_well_covered_not_ball_union_subset {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (d : ℕ) (hd : 1 ≤ d)
    (hwc : simple_graph_is_well_covered (simple_graph_power G d)) (s t w : V)
    (hst : ((d + 1 : ℕ) : ℕ∞) ≤ G.edist s t) :
    ¬ ∀ x : V, (G.edist s x ≤ d ∨ G.edist t x ≤ d) → G.edist w x ≤ d := by
  intro hball
  set P := simple_graph_power G d
  have hsw : G.edist w s ≤ d := hball s (Or.inl (by simp))
  have htw : G.edist w t ≤ d := hball t (Or.inr (by simp))
  have hlt : ∀ x y : V, G.edist x y ≤ d → ¬ ((d + 1 : ℕ) : ℕ∞) ≤ G.edist x y := by
    intro x y h1 h2
    have := h2.trans h1
    norm_cast at this
    omega
  have hst_ne : s ≠ t := by
    intro h; subst h; simp at hst
  have hws : w ≠ s := by
    intro h; subst h; exact hlt w t htw hst
  have hwt : w ≠ t := by
    intro h; subst h; rw [SimpleGraph.edist_comm] at hsw; exact hlt s w hsw hst
  have hadjw : ∀ x, x ≠ w → (G.edist s x ≤ d ∨ G.edist t x ≤ d) → P.Adj w x :=
    fun x hx h => ⟨fun e => hx e.symm, hball x h⟩
  obtain ⟨X, hwX, hX⟩ := simple_graph_exists_maximal_indep_superset P {w} (by simp)
  have hwX' : w ∈ X := hwX (Finset.mem_singleton_self w)
  have hsX : s ∉ X := fun h => hX.1 hwX' h hws (hadjw s hws.symm (Or.inl (by simp)))
  have htX : t ∉ X := fun h => hX.1 hwX' h hwt (hadjw t hwt.symm (Or.inr (by simp)))
  set Y := X.erase w ∪ {s, t}
  have hYind : P.IsIndepSet (Y : Set V) := by
    have key : ∀ x ∈ X.erase w, ∀ y ∈ ({s, t} : Finset V), ¬ P.Adj y x := by
      intro x hx y hy hadj
      rw [Finset.mem_erase] at hx
      have hyx : G.edist y x ≤ d := hadj.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      have : P.Adj w x := by
        rcases hy with rfl | rfl
        · exact hadjw x hx.1 (Or.inl hyx)
        · exact hadjw x hx.1 (Or.inr hyx)
      exact hX.1 hwX' hx.2 (fun e => hx.1 e.symm) this
    intro x hx y hy hxy hadj
    simp only [Y, Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hX.1 (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy hadj
    · exact key x hx y hy hadj.symm
    · exact key y hy x hx hadj
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      have hst' : ¬ P.Adj s t := fun h => hlt s t h.2 hst
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hst' hadj
      · exact hst' hadj.symm
      · exact hxy rfl
  obtain ⟨Z, hYZ, hZ⟩ := simple_graph_exists_maximal_indep_superset P Y hYind
  have hcardY : Y.card = X.card + 1 := by
    have hdisj : Disjoint (X.erase w) {s, t} := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact hsX (Finset.mem_of_mem_erase hx)
      · exact htX (Finset.mem_of_mem_erase hx)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hwX',
      Finset.card_pair hst_ne]
    have : 1 ≤ X.card := Finset.card_pos.2 ⟨w, hwX'⟩
    omega
  have h1 := Finset.card_le_card hYZ
  have h2 := hwc X Z hX hZ
  omega
