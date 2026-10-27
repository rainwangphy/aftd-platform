import AFTD.Prelude
import AFTD.Kb.Tcs.ThirdPrincipalSpecialization
import AFTD.Kb.Tcs.G

/-!
# third_principal_specialization_congr

Topic: graphs   Node: 5c5c1dbed16c

Provenance: helper lemma. arXiv:2610.31785 Proposition 3.3

If two finite graphs are isomorphic, their third principal specializations are equal as bivariate polynomials.
-/

def third_principal_specialization_congr_coloring_equiv {V W α : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    H.Coloring α ≃ G.Coloring α where
  toFun c := c.comp e.toHom
  invFun c := c.comp e.symm.toHom
  left_inv c := by ext; simp
  right_inv c := by ext; simp

/-- Isomorphic graphs have equal third principal specializations. -/
theorem third_principal_specialization_congr {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) : third_principal_specialization G = third_principal_specialization H := by
  unfold third_principal_specialization
  rw [← Equiv.sum_comp (third_principal_specialization_congr_coloring_equiv G H e)]
  apply Fintype.sum_congr
  intro c
  have h1 : ∑ v : V, ((c.comp e.toHom) v).val = ∑ w : W, (c w).val := by
    have h : (fun v => ((c.comp e.toHom) v).val) = (fun w => (c w).val) ∘ e.toEquiv := rfl
    rw [h]
    exact Equiv.sum_comp e.toEquiv (fun w => (c w).val)
  have h2 : (Finset.univ.image (c.comp e.toHom)).card = (Finset.univ.image c).card := by
    have h : (c.comp e.toHom : V → Fin 3) = c ∘ e.toEquiv := rfl
    rw [h, ← Finset.image_image, Finset.image_univ_equiv]
  show (MvPolynomial.X 0 ^ ∑ v, ((c.comp e.toHom) v).val) *
       MvPolynomial.X 1 ^ (Finset.image (c.comp e.toHom) Finset.univ).card =
       (MvPolynomial.X 0 ^ ∑ w, (c w).val) *
       MvPolynomial.X 1 ^ (Finset.image c Finset.univ).card
  rw [h1, h2]
