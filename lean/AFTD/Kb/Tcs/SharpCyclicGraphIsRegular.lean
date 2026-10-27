import AFTD.Prelude
import AFTD.Kb.Tcs.AdmitsSharpCyclicLabeling
import AFTD.Kb.Tcs.CyclicMatrixFourierZeroZeroNeZero
import AFTD.Kb.Tcs.CyclicFourierColZeroEqZeroOfSharp
import AFTD.Kb.Tcs.RowSumEqOfFourierColZeroVanish
import AFTD.Kb.Tcs.CyclicMatrixFourier
import AFTD.Kb.Tcs.IsSharpCyclicLabeling

/-!
# sharp_cyclic_graph_is_regular

Topic: combinatorics   Node: a4d2a3933d8a

Provenance: formalization of a published result. Source: arXiv:2610.31807 Theorem 3.14

Every finite simple graph G with at least one edge that admits a sharp cyclic labeling on ZMod N is regular of some degree d.
-/

/-- Every simple graph with at least one edge admitting a sharp cyclic labeling is regular. -/
theorem sharp_cyclic_graph_is_regular {V : Type*} [Fintype V] (N : ℕ) [NeZero N]
    (G : SimpleGraph V) [DecidableRel G.Adj] (he : ∃ u v, G.Adj u v)
    (hs : admits_sharp_cyclic_labeling N G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  obtain ⟨π, hπ⟩ := hs
  let M : Matrix (ZMod N) (ZMod N) ℂ := Matrix.of fun x y => if G.Adj (π x) (π y) then (1:ℂ) else 0
  have h0 : cyclic_matrix_fourier N M 0 0 ≠ 0 :=
    cyclic_matrix_fourier_zero_zero_ne_zero N G π he
  have hF : ∀ m : ZMod N, m ≠ 0 → cyclic_matrix_fourier N M m 0 = 0 :=
    fun m hm => cyclic_fourier_col_zero_eq_zero_of_sharp N M hπ h0 m hm
  have hrow : ∀ x : ZMod N, (∑ y : ZMod N, M x y) = ∑ y : ZMod N, M 0 y :=
    fun x => row_sum_eq_of_fourier_col_zero_vanish N M hF x
  have hdeg : ∀ x : ZMod N, (∑ y : ZMod N, M x y) = (G.degree (π x) : ℂ) := by
    intro x
    have h1 : (∑ y : ZMod N, M x y) =
        ((Finset.univ.filter (fun y => G.Adj (π x) (π y))).card : ℂ) := by
      simp only [M, Matrix.of_apply]
      rw [Finset.sum_boole]
    have h2 : (Finset.univ.filter (fun y : ZMod N => G.Adj (π x) (π y))).card =
        G.degree (π x) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun y _ => π y)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact (SimpleGraph.mem_neighborFinset G (π x) (π y)).mpr hy
      · intro y1 _ y2 _ h
        exact π.injective h
      · intro v hv
        simp only [SimpleGraph.mem_neighborFinset] at hv
        exact ⟨π.symm v, by simp [hv], by simp⟩
    rw [h1, h2]
  refine ⟨G.degree (π 0), ?_⟩
  intro v
  have hd1 : (G.degree v : ℂ) = (G.degree (π 0) : ℂ) := by
    rw [← π.apply_symm_apply v, ← hdeg (π.symm v), ← hdeg 0]
    exact hrow (π.symm v)
  exact_mod_cast hd1
