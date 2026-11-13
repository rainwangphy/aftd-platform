import AFTD.Prelude
import AFTD.Kb.Tcs.PosetBraidMap

/-!
# poset_braid_map_involutive

Topic: combinatorics   Node: 83f59e9b64ef

Provenance: formalization of a published result. Source: scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:492

For any partially ordered set P with decidable order, the bipartite map poset_braid_map is an involution on pairs: poset_braid_map (poset_braid_map p) = p for all p.
-/

/-- The poset braid map is an involution. -/
theorem poset_braid_map_involutive {P : Type*} [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)]
    (p : (P ⊕ (P × ZMod 2)) × (P ⊕ (P × ZMod 2))) :
    poset_braid_map (poset_braid_map p) = p := by
  have h2 (e : ZMod 2) : e + 1 + 1 = e := by fin_cases e <;> rfl
  rcases p with ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩ <;>
    first | rfl | (dsimp [poset_braid_map]; split_ifs <;> simp [h2])
