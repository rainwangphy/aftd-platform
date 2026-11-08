import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.F

/-!
# proj_physical_pairs_coset_bijective

Topic: quantum   Node: 427fb0591207

Provenance: helper lemma. arXiv:2610.04621 Lemma 5

If the coordinate projection v ↦ (v.1|_S, v.2|_S) onto a subset S of physical pairs is a bijection from a subspace L of V_k to (S → F_2) × (S → F_2), then for every vector a, it is also a bijection from the translate a + L to (S → F_2) × (S → F_2).
-/

open scoped Pointwise in
/-- Projection onto coordinate pairs is bijective on any coset of a subspace if it is bijective on the subspace. -/
lemma proj_physical_pairs_coset_bijective {k : ℕ}
    (L : Submodule (F 2) (V k 2)) (S : Finset (Fin k))
    (hbij : Set.BijOn (fun v : V k 2 => ((fun (s : S) => v.1 s.1), (fun (s : S) => v.2 s.1))) (L : Set (V k 2)) Set.univ)
    (a : V k 2) :
    Set.BijOn (fun v : V k 2 => ((fun (s : S) => v.1 s.1), (fun (s : S) => v.2 s.1))) (a +ᵥ (L : Set (V k 2))) Set.univ := by
  let f : V k 2 → ((S → F 2) × (S → F 2)) :=
    fun v => ((fun (s : S) => v.1 s.1), (fun (s : S) => v.2 s.1))
  have hfadd : ∀ x y : V k 2, f (x + y) = f x + f y := by
    intro x y
    ext s <;> simp [f]
  change Set.BijOn f (a +ᵥ (L : Set (V k 2))) Set.univ
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_univ _
  · intro x hx y hy hxy
    rw [Set.mem_vadd_set] at hx hy
    obtain ⟨lx, hlx, rfl⟩ := hx
    obtain ⟨ly, hly, rfl⟩ := hy
    simp only [vadd_eq_add] at hxy
    rw [hfadd, hfadd] at hxy
    have hfl : f lx = f ly := add_left_cancel hxy
    have hlxy : lx = ly := hbij.2.1 hlx hly hfl
    rw [hlxy]
  · intro y hy
    have hy' : y - f a ∈ f '' (L : Set (V k 2)) := hbij.2.2 (Set.mem_univ _)
    obtain ⟨l, hl, hfl⟩ := hy'
    refine ⟨a + l, ?_, ?_⟩
    · rw [Set.mem_vadd_set]
      exact ⟨l, hl, by rw [vadd_eq_add]⟩
    · rw [hfadd, hfl]
      abel
