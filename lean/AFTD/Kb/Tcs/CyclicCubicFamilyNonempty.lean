import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicFamily

/-!
# cyclic_cubic_family_nonempty

Topic: quantum   Node: 4cfefec6ebc8

Provenance: helper lemma. step towards cyclic_cubic_t_count_upper_bound

For every n ≥ 6, every member of cyclic_cubic_family n is nonempty.
-/

lemma cyclic_cubic_family_nonempty_helper (n : ℕ) (s : Finset ℕ) (k : ℕ) (hk : k < n) (hs : k ∈ s) :
    ({i : Fin n | (i : ℕ) ∈ s} : Finset (Fin n)).Nonempty := by
  use ⟨k, hk⟩
  simp [hs]

/-- Every parity in cyclic_cubic_family n is nonempty for n ≥ 6. -/
theorem cyclic_cubic_family_nonempty (n : ℕ) (hn : 6 ≤ n) : ∀ y ∈ cyclic_cubic_family n, y.Nonempty := by
  intro y hy
  unfold cyclic_cubic_family at hy
  simp only [Finset.mem_image] at hy
  rcases hy with ⟨s, hs, rfl⟩
  simp only [Finset.mem_union] at hs
  rcases hs with (hsA | hsB) | hsC
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hsA
    rcases hsA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cyclic_cubic_family_nonempty_helper n _ 1 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ (n - 3) (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ (n - 3) (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 1 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ (n - 4) (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ (n - 4) (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp)
  · simp only [Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton] at hsB
    rcases hsB with ⟨k, hk, rfl | rfl⟩
    · exact cyclic_cubic_family_nonempty_helper n _ k (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ k (by omega) (by simp)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hsC
    rcases hsC with rfl | rfl | rfl
    · exact cyclic_cubic_family_nonempty_helper n _ 2 (by omega) (by simp; omega)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp)
    · exact cyclic_cubic_family_nonempty_helper n _ 0 (by omega) (by simp; omega)
