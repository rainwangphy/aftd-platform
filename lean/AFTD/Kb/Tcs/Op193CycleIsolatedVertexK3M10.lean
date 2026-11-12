import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193CycleIsolatedVertexChromaticLe
import AFTD.Kb.Tcs.Op193K3M10AtLeast85Vertices
import AFTD.Kb.Tcs.Op193K3M10CaseA0
import AFTD.Kb.Tcs.Op193K3M10CaseA3
import AFTD.Kb.Tcs.Op193K3M10CaseA4
import AFTD.Kb.Tcs.Op193K3M10CaseA5
import AFTD.Kb.Tcs.Op193K3M10CaseB2x1
import AFTD.Kb.Tcs.Op193K3M10CaseB2x4
import AFTD.Kb.Tcs.Op193K3M10CaseB3x0
import AFTD.Kb.Tcs.Op193K3M10CaseB3x1
import AFTD.Kb.Tcs.Op193K3M10CaseB3x4
import AFTD.Kb.Tcs.Op193K3M10CaseB4x0
import AFTD.Kb.Tcs.Op193K3M10CaseB4x3
import AFTD.Kb.Tcs.Op193K3M10CaseB4x5

/-!
# op_193_cycle_isolated_vertex_k3_m10

Topic: graphs   Node: 14863d99be60

Provenance: helper lemma. OP-193 finite boundary case, experiment 23347.

The stable triple graph of the ten-cycle plus an isolated vertex has chromatic number seven.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open Inbox777M10
theorem in777_m10_conditional
    (leaf_a0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 0), False)
    (leaf_a3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 3), False)
    (leaf_a4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 4), False)
    (leaf_a5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 5), False)
    (leaf_b2x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 1), False)
    (leaf_b2x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 4), False)
    (leaf_b2x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 5), False)
    (leaf_b3x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 0), False)
    (leaf_b3x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 1), False)
    (leaf_b3x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 4), False)
    (leaf_b3x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 5), False)
    (leaf_b4x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 0), False)
    (leaf_b4x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 3), False)
    (leaf_b4x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 5), False)
    (leaf_b5x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 0), False)
    (leaf_b5x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 3), False)
    (leaf_b5x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 4), False)
    : ¬ (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).Colorable 6 := by
  rintro ⟨C⟩
  let raw : Fin 85 → Fin 6 := fun i => C ⟨verts i, verts_valid i⟩
  have hproper : ∀ i j, Disjoint (verts i) (verts j) → raw i ≠ raw j := by
    intro i j hd
    apply C.valid
    refine ⟨hd, ?_⟩
    intro heq
    have hv : verts i = verts j := congrArg Subtype.val heq
    have hn : (verts i).Nonempty := Finset.card_pos.mp (by rw [(verts_valid i).card_eq]; decide)
    obtain ⟨x, hx⟩ := hn
    exact (Finset.disjoint_left.mp hd) hx (by rw [← hv]; exact hx)
  have h01 : raw 0 ≠ raw 22 := hproper _ _ (by decide)
  have h02 : raw 0 ≠ raw 82 := hproper _ _ (by decide)
  have h12 : raw 22 ≠ raw 82 := hproper _ _ (by decide)
  have h03 : raw 0 ≠ raw 84 := hproper _ _ (by decide)
  have h13 : raw 22 ≠ raw 84 := hproper _ _ (by decide)
  let p := normalization (raw 0) (raw 22) (raw 82) (raw 84)
  let c : Fin 85 → Fin 6 := fun i => p (raw i)
  have hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j := by
    intro i j hd heq
    exact hproper i j hd (p.injective heq)
  have hs := normalization_spec (raw 0) (raw 22) (raw 82) (raw 84) h01 h02 h12 h03 h13
  have h0 : c 0 = 0 := hs.1
  have h1 : c 22 = 1 := hs.2.1
  have h2 : c 82 = 2 := hs.2.2.1
  have h84 : c 84 = 2 ∨ c 84 = 3 := hs.2.2.2
  have h74n1 : c 74 ≠ 1 := by simpa [h1] using hp 74 22 (by decide)
  have h74n2 : c 74 ≠ 2 := by simpa [h2] using hp 74 82 (by decide)
  have h83n0 : c 83 ≠ 0 := by simpa [h0] using hp 83 0 (by decide)
  have h83n1 : c 83 ≠ 1 := by simpa [h1] using hp 83 22 (by decide)
  rcases h84 with h84 | h84
  · generalize heq : c 74 = x
    fin_cases x
    all_goals first
      | exact leaf_a0 c hp h0 h1 h2 h84 heq
      | exact leaf_a3 c hp h0 h1 h2 h84 heq
      | exact leaf_a4 c hp h0 h1 h2 h84 heq
      | exact leaf_a5 c hp h0 h1 h2 h84 heq
      | exact False.elim (h74n1 heq)
      | exact False.elim (h74n2 heq)
  · generalize heq83 : c 83 = x
    fin_cases x
    all_goals try (first | exact False.elim (h83n0 heq83) | exact False.elim (h83n1 heq83))
    ·
      have hn0 : c 25 ≠ 0 := by simpa [h0] using hp 25 0 (by decide)
      have hn2 : c 25 ≠ 2 := by simpa [heq83] using hp 25 83 (by decide)
      have hn3 : c 25 ≠ 3 := by simpa [h84] using hp 25 84 (by decide)
      generalize hev : c 25 = y
      fin_cases y
      all_goals first
        | exact leaf_b2x1 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b2x4 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b2x5 c hp h0 h1 h2 h84 heq83 hev
        | exact False.elim (hn0 hev)
        | exact False.elim (hn2 hev)
        | exact False.elim (hn3 hev)
    ·
      have hn2 : c 15 ≠ 2 := by simpa [h2] using hp 15 82 (by decide)
      have hn3 : c 15 ≠ 3 := by simpa [heq83] using hp 15 83 (by decide)
      generalize hev : c 15 = y
      fin_cases y
      all_goals first
        | exact leaf_b3x0 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b3x1 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b3x4 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b3x5 c hp h0 h1 h2 h84 heq83 hev
        | exact False.elim (hn2 hev)
        | exact False.elim (hn3 hev)
    ·
      have hn1 : c 12 ≠ 1 := by simpa [h1] using hp 12 22 (by decide)
      have hn2 : c 12 ≠ 2 := by simpa [h2] using hp 12 82 (by decide)
      have hn4 : c 12 ≠ 4 := by simpa [heq83] using hp 12 83 (by decide)
      generalize hev : c 12 = y
      fin_cases y
      all_goals first
        | exact leaf_b4x0 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b4x3 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b4x5 c hp h0 h1 h2 h84 heq83 hev
        | exact False.elim (hn1 hev)
        | exact False.elim (hn2 hev)
        | exact False.elim (hn4 hev)
    ·
      have hn1 : c 12 ≠ 1 := by simpa [h1] using hp 12 22 (by decide)
      have hn2 : c 12 ≠ 2 := by simpa [h2] using hp 12 82 (by decide)
      have hn5 : c 12 ≠ 5 := by simpa [heq83] using hp 12 83 (by decide)
      generalize hev : c 12 = y
      fin_cases y
      all_goals first
        | exact leaf_b5x0 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b5x3 c hp h0 h1 h2 h84 heq83 hev
        | exact leaf_b5x4 c hp h0 h1 h2 h84 heq83 hev
        | exact False.elim (hn1 hev)
        | exact False.elim (hn2 hev)
        | exact False.elim (hn5 hev)

theorem in777_m10_complete_conditional
    (leaf_a0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 0), False)
    (leaf_a3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 3), False)
    (leaf_a4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 4), False)
    (leaf_a5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 5), False)
    (leaf_b2x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 1), False)
    (leaf_b2x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 4), False)
    (leaf_b2x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 5), False)
    (leaf_b3x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 0), False)
    (leaf_b3x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 1), False)
    (leaf_b3x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 4), False)
    (leaf_b3x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 5), False)
    (leaf_b4x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 0), False)
    (leaf_b4x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 3), False)
    (leaf_b4x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 5), False)
    (leaf_b5x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 0), False)
    (leaf_b5x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 3), False)
    (leaf_b5x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 4), False)
    : (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber = 7 := by
  have hnot : ¬ (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).Colorable 6 :=
    in777_m10_conditional
      leaf_a0
      leaf_a3
      leaf_a4
      leaf_a5
      leaf_b2x1
      leaf_b2x4
      leaf_b2x5
      leaf_b3x0
      leaf_b3x1
      leaf_b3x4
      leaf_b3x5
      leaf_b4x0
      leaf_b4x3
      leaf_b4x5
      leaf_b5x0
      leaf_b5x3
      leaf_b5x4
  have hu : (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber ≤ 7 := by
    have h := op_193_cycle_isolated_vertex_chromatic_le 3 10 (by omega) (by omega)
    have hnum : ((10 : ℕ) : ℕ∞) - 2 * ((3 : ℕ) : ℕ∞) + 3 = 7 := by decide
    rw [hnum] at h
    exact h
  have hn : ¬ (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber ≤ 6 := by
    intro h
    apply hnot
    exact (SimpleGraph.chromaticNumber_le_iff_colorable (n := 6)).mp h
  have hl : (6 : ℕ∞) < (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber := lt_of_not_ge hn
  apply le_antisymm hu
  exact ENat.natCast_add_one_le_iff.mpr hl


open Inbox777M10
theorem in777_m10_symmetry_conditional
    (leaf_a0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 0), False)
    (leaf_a3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 3), False)
    (leaf_a4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 4), False)
    (leaf_a5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 2)
    (h4 : c 74 = 5), False)
    (leaf_b2x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 1), False)
    (leaf_b2x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 4), False)
    (leaf_b3x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 0), False)
    (leaf_b3x1 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 1), False)
    (leaf_b3x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 4), False)
    (leaf_b4x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 0), False)
    (leaf_b4x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 3), False)
    (leaf_b4x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 4)
    (h5 : c 12 = 5), False)
    : (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber = 7 := by
  have leaf_b2x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 2)
    (h5 : c 25 = 5), False := by
    intro c hp h0 h1 h2 h3 h4 h5
    let d : Fin 85 → Fin 6 := fun i => Equiv.swap (4 : Fin 6) 5 (c i)
    have hd : ∀ i j, Disjoint (verts i) (verts j) → d i ≠ d j := by
      intro i j hij heq
      exact hp i j hij ((Equiv.swap (4 : Fin 6) 5).injective heq)
    apply leaf_b2x4 d hd
    all_goals simp [d, h0, h1, h2, h3, h4, h5] <;> decide
  have leaf_b3x5 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 3)
    (h5 : c 15 = 5), False := by
    intro c hp h0 h1 h2 h3 h4 h5
    let d : Fin 85 → Fin 6 := fun i => Equiv.swap (4 : Fin 6) 5 (c i)
    have hd : ∀ i j, Disjoint (verts i) (verts j) → d i ≠ d j := by
      intro i j hij heq
      exact hp i j hij ((Equiv.swap (4 : Fin 6) 5).injective heq)
    apply leaf_b3x4 d hd
    all_goals simp [d, h0, h1, h2, h3, h4, h5] <;> decide
  have leaf_b5x0 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 0), False := by
    intro c hp h0 h1 h2 h3 h4 h5
    let d : Fin 85 → Fin 6 := fun i => Equiv.swap (4 : Fin 6) 5 (c i)
    have hd : ∀ i j, Disjoint (verts i) (verts j) → d i ≠ d j := by
      intro i j hij heq
      exact hp i j hij ((Equiv.swap (4 : Fin 6) 5).injective heq)
    apply leaf_b4x0 d hd
    all_goals simp [d, h0, h1, h2, h3, h4, h5] <;> decide
  have leaf_b5x3 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 3), False := by
    intro c hp h0 h1 h2 h3 h4 h5
    let d : Fin 85 → Fin 6 := fun i => Equiv.swap (4 : Fin 6) 5 (c i)
    have hd : ∀ i j, Disjoint (verts i) (verts j) → d i ≠ d j := by
      intro i j hij heq
      exact hp i j hij ((Equiv.swap (4 : Fin 6) 5).injective heq)
    apply leaf_b4x3 d hd
    all_goals simp [d, h0, h1, h2, h3, h4, h5] <;> decide
  have leaf_b5x4 : ∀ (c : Fin 85 → Fin 6)
    (hp : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (h0 : c 0 = 0)
    (h1 : c 22 = 1)
    (h2 : c 82 = 2)
    (h3 : c 84 = 3)
    (h4 : c 83 = 5)
    (h5 : c 12 = 4), False := by
    intro c hp h0 h1 h2 h3 h4 h5
    let d : Fin 85 → Fin 6 := fun i => Equiv.swap (4 : Fin 6) 5 (c i)
    have hd : ∀ i j, Disjoint (verts i) (verts j) → d i ≠ d j := by
      intro i j hij heq
      exact hp i j hij ((Equiv.swap (4 : Fin 6) 5).injective heq)
    apply leaf_b4x5 d hd
    all_goals simp [d, h0, h1, h2, h3, h4, h5] <;> decide
  exact in777_m10_complete_conditional
    leaf_a0
    leaf_a3
    leaf_a4
    leaf_a5
    leaf_b2x1
    leaf_b2x4
    leaf_b2x5
    leaf_b3x0
    leaf_b3x1
    leaf_b3x4
    leaf_b3x5
    leaf_b4x0
    leaf_b4x3
    leaf_b4x5
    leaf_b5x0
    leaf_b5x3
    leaf_b5x4

theorem op_193_cycle_isolated_vertex_k3_m10 :
    (GStableKneser ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)) 3).chromaticNumber = 7 := by
  exact in777_m10_symmetry_conditional
    op_193_k3_m10_case_a0
    op_193_k3_m10_case_a3
    op_193_k3_m10_case_a4
    op_193_k3_m10_case_a5
    op_193_k3_m10_case_b2x1
    op_193_k3_m10_case_b2x4
    op_193_k3_m10_case_b3x0
    op_193_k3_m10_case_b3x1
    op_193_k3_m10_case_b3x4
    op_193_k3_m10_case_b4x0
    op_193_k3_m10_case_b4x3
    op_193_k3_m10_case_b4x5
