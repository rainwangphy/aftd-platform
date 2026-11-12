import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193CoveringColorObstruction
import AFTD.Kb.Tcs.Op193CubicCycleAnchorAvoidance
import AFTD.Kb.Tcs.Op193AvoidanceForcesNonanchor
import AFTD.Kb.Tcs.Op193NonanchoredColorExposesAllColors

/-!
# op_193_cubic_noncolorable_if_cycle_lower

Topic: graphs   Node: 0abc882ecdc7

Provenance: helper lemma. Explicit-threshold refinement of arXiv:2610.17884 Section 3.

For k at least 3 and m at least k((k-1)²+1), if the cycle-stable k-set graph is not (m-2k+1)-colorable, then adding an isolated vertex gives a stable k-set graph that is not (m-2k+2)-colorable.
-/

theorem op_193_cubic_noncolorable_if_cycle_lower (k m : ℕ) (hk : 3 ≤ k)
    (hm : k * ((k-1)^2+1) ≤ m)
    (hcycle : ¬ (GStableKneser (SimpleGraph.cycleGraph m) k).Colorable (m-2*k+1)) :
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
  have havoid : ∀ A : Fin (q+1) → Finset (Fin m), (∀ j, (A j).card ≤ k) →
      ∃ S : {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
        ∀ j, (S.1 ∩ A j).card ≤ 1 := by
    intro A hA
    have := op_193_cubic_cycle_anchor_avoidance k m hk hm A hA
    obtain ⟨S, hcard, hind, hav⟩ := this
    refine ⟨⟨S, hcard, hind⟩, ?_⟩
    intro j
    exact hav j
  obtain ⟨j, hj⟩ := op_193_avoidance_forces_nonanchor m k (q+1) c' havoid
  obtain ⟨F, hf, hi, hall⟩ := op_193_nonanchored_color_exposes_all_colors m k q (by omega) c' hc' hmin j hj
  refine ⟨F, hf, hi, ?_⟩
  intro i
  obtain ⟨U, hU, hdis⟩ := hall i
  exact ⟨⟨U.1, ⟨U.2.2, U.2.1⟩⟩, hU, hdis⟩
