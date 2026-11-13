import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.Tcs.ForestSymmetricFiberEquiv
import AFTD.Kb.Tcs.ForestGreedyStepNeg

/-!
# forest_greedy_symmetric_merge

Topic: online_algorithms   Node: 45e068bc8a82

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

The greedy update of two independent finite uniform symmetric integer laws with a fair tie coin has symmetric value counts.
-/

theorem forest_greedy_symmetric_merge
    (α β : Type) [Fintype α] [Fintype β] (X : α → ℤ) (Y : β → ℤ)
    (hx : ∀ z : ℤ, (Finset.univ.filter (fun a => X a = z)).card =
      (Finset.univ.filter (fun a => X a = -z)).card)
    (hy : ∀ z : ℤ, (Finset.univ.filter (fun b => Y b = z)).card =
      (Finset.univ.filter (fun b => Y b = -z)).card) :
    ∀ z : ℤ, (Finset.univ.filter (fun p : α × β × Bool =>
      forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2 = z)).card =
      (Finset.univ.filter (fun p : α × β × Bool =>
      forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2 = -z)).card := by
  classical
  obtain ⟨ex, hex⟩ := forest_symmetric_fiber_equiv α X hx
  obtain ⟨ey, hey⟩ := forest_symmetric_fiber_equiv β Y hy
  let ee : α × β × Bool ≃ α × β × Bool := ex.prodCongr (ey.prodCongr Equiv.boolNot)
  let f : α × β × Bool → ℤ := fun p => forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2
  have hstep (p : α × β × Bool) : f (ee p) = -f p := by
    change forest_greedy_signed_step (X (ex p.1)) (Y (ey p.2.1)) (!p.2.2) = _
    rw [hex, hey]
    exact forest_greedy_step_neg _ _ _
  intro z
  let ez : {p // f p = z} ≃ {p // f p = -z} := ee.subtypeEquiv (by
    intro p
    rw [hstep]
    omega)
  simpa only [Fintype.card_subtype] using Fintype.card_congr ez
