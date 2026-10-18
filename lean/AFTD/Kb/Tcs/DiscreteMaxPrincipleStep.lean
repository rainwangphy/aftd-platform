import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# discrete_max_principle_step

Topic: combinatorics   Node: 94e71ef1893e

Provenance: helper lemma. step towards finset_midpoint_balanced_exists_nonzero_minor

If w_ext(0) = 0 and 2*w_ext(l.succ) = w_ext(u l.succ) + w_ext(v l.succ) for all l, and V > 0 is the maximum of w_ext, then S = {j | w_ext j = V} is nonempty, 0 ∉ S, and S is closed under u and v.
-/

/-- For an integer vector w_ext vanishing at 0 and satisfying the discrete midpoint harmonic equation at all succ indices, the argmax of a strictly positive maximum does not contain 0 and is closed under the midpoint index maps u and v. -/
theorem discrete_max_principle_step (k : ℕ) (u v : Fin (k + 1) → Fin (k + 1))
    (w_ext : Fin (k + 1) → ℤ)
    (hw0 : w_ext 0 = 0)
    (hmid : ∀ l : Fin k, 2 * w_ext l.succ = w_ext (u l.succ) + w_ext (v l.succ))
    (V : ℤ) (hV : 0 < V) (m : Fin (k + 1)) (hm : w_ext m = V)
    (hmax : ∀ j, w_ext j ≤ V) :
    let S := Finset.univ.filter (fun j => w_ext j = V)
    S.Nonempty ∧ (0 : Fin (k + 1)) ∉ S ∧
    ∀ i ∈ S, u i ∈ S ∧ v i ∈ S := by
  intro S
  have hmS : m ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ m, hm⟩
  have hS_nonempty : S.Nonempty := ⟨m, hmS⟩
  have h0_not_mem : (0 : Fin (k + 1)) ∉ S := by
    rw [Finset.mem_filter]
    rintro ⟨-, h0⟩
    rw [hw0] at h0
    linarith
  refine ⟨hS_nonempty, h0_not_mem, ?_⟩
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨-, hwi⟩ := hi
  have hne : i ≠ 0 := by
    rintro rfl
    exact h0_not_mem (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ 0, hwi⟩)
  obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hne
  have hsum : 2 * V = w_ext (u l.succ) + w_ext (v l.succ) := by
    linarith [hmid l]
  have hu_le : w_ext (u l.succ) ≤ V := hmax (u l.succ)
  have hv_le : w_ext (v l.succ) ≤ V := hmax (v l.succ)
  have hu_eq : w_ext (u l.succ) = V := by linarith
  have hv_eq : w_ext (v l.succ) = V := by linarith
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hu_eq⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hv_eq⟩
