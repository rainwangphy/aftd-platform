import AFTD.Prelude
import AFTD.Kb.Tcs.IsApTileStep

/-!
# is_ap_tile_step_Icc_self

Topic: combinatorics   Node: f0419d685a84

Provenance: helper lemma. arXiv:2611.05321 Definition 1.4

For any natural number k with [NeZero k], the initial interval Finset.Icc 1 k is an arithmetic progression tile of step k.
-/

/-- The interval {1, ..., k} contains exactly one representative of each residue class modulo k. -/
theorem is_ap_tile_step_Icc_self (k : ℕ) [NeZero k] :
    is_ap_tile_step k (Finset.Icc 1 k) := by
  intro r
  let x := (r - 1).val + 1
  have hx_mem : x ∈ (Finset.Icc 1 k).filter (fun (a : ℕ) => (a : ZMod k) = r) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.le_add_left 1 _, ZMod.val_lt (r - 1)⟩, ?_⟩
    dsimp [x]
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  have hx_uniq : ∀ y ∈ (Finset.Icc 1 k).filter (fun (a : ℕ) => (a : ZMod k) = r), y = x := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    rcases hy with ⟨⟨hy1, hy2⟩, hyr⟩
    have hcast : ((y - 1 : ℕ) : ZMod k) = r - 1 := by
      rw [Nat.cast_sub hy1, hyr, Nat.cast_one]
    have hval : ((y - 1 : ℕ) : ZMod k).val = (y - 1) % k := ZMod.val_natCast k (y - 1)
    have hmod : (y - 1) % k = y - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hcast] at hval
    dsimp [x]
    omega
  have hs : (Finset.Icc 1 k).filter (fun (a : ℕ) => (a : ZMod k) = r) = {x} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hx_mem, hx_uniq⟩
  rw [hs, Finset.card_singleton]
