import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193StableAnchorAvoidanceForcesNonanchor
import AFTD.Kb.Tcs.Op193NonanchoredColorExposesAllColors
import AFTD.Kb.Tcs.Op193CoveringColorObstruction

/-!
# op_193_noncolorable_if_stable_anchor_avoidance

Topic: graphs   Node: fcb79d8c7607

Provenance: helper lemma. Stable-anchor refinement of the coloring argument in arXiv:2610.17884 Section 3.

If the cycle-only stable k-set graph is not (m-2k+1)-colorable and every family of m-2k+2 stable k-sets can be met in at most one point by another stable k-set, then the cycle plus an isolated vertex is not (m-2k+2)-colorable.
-/

theorem op_193_noncolorable_if_stable_anchor_avoidance (k m : ℕ) (hk : 2 ≤ k)
    (hcycle : ¬ (GStableKneser (SimpleGraph.cycleGraph m) k).Colorable (m-2*k+1))
    (havoid : ∀ A : Fin (m-2*k+2) → {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
      ∃ S : {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
        ∀ j, (S.1 ∩ (A j).1).card ≤ 1) :
    ¬ (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).Colorable (m-2*k+2) := by
  classical
  let q := m-2*k+1
  have hq : m-2*k+2 = q+1 := by dsimp [q]
  rw [hq]
  apply op_193_covering_color_obstruction m k (q+1) (by omega)
  intro c hc
  let c' : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin (q+1) :=
    fun S => c ⟨S.1, ⟨S.2.2, S.2.1⟩⟩
  have hc' : ∀ U W, Disjoint U.1 W.1 → c' U ≠ c' W := by
    intro U W hd
    exact hc _ _ hd
  have hmin : ¬ ∃ d : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin q,
      ∀ U W, Disjoint U.1 W.1 → d U ≠ d W := by
    rintro ⟨d, hd⟩
    apply hcycle
    refine ⟨SimpleGraph.Coloring.mk (fun S => d ⟨S.1, ⟨S.2.card_eq, S.2.isIndepSet⟩⟩) ?_⟩
    intro U W hadj
    exact hd _ _ hadj.1
  obtain ⟨j, hj⟩ := op_193_stable_anchor_avoidance_forces_nonanchor m k (q+1) c' havoid
  obtain ⟨F, hf, hi, hall⟩ := op_193_nonanchored_color_exposes_all_colors m k q hk c' hc' hmin j hj
  refine ⟨F, hf, hi, ?_⟩
  intro i
  obtain ⟨U, hU, hdis⟩ := hall i
  exact ⟨⟨U.1, ⟨U.2.2, U.2.1⟩⟩, hU, hdis⟩
