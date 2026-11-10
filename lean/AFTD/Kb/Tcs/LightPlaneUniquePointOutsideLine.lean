import AFTD.Prelude
import AFTD.Kb.Tcs.AffineLine
import AFTD.Kb.Tcs.AffinePlane

/-!
# light_plane_unique_point_outside_line

Topic: combinatorics   Node: 5190e3b8ed0f

Provenance: helper lemma. arXiv:2611.12153 Lemma 2.3 -- The strong cylinder conjecture over prime fields

Let p be a prime, S ⊆ (ℤ/pℤ)³, and let P, v ∈ (ℤ/pℤ)³ with v ≠ 0. Suppose f is a nonzero linear functional such that the affine plane defined by f(x) = f(P) contains the affine line through P in direction v. If S meets the affine line in p - 1 points and meets the plane in p points, then there exists a unique point Q in S on the plane that does not lie on the line.
-/

/-- A light plane containing an affine line meeting S in p - 1 points contains a unique point of S outside that line. -/
theorem light_plane_unique_point_outside_line
    (p : ℕ) [Fact p.Prime]
    (S : Set (Fin 3 → ZMod p))
    (P v : Fin 3 → ZMod p) (hv : v ≠ 0)
    (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p) (hf : f ≠ 0)
    (hline : affine_line P v ⊆ affine_plane f (f P))
    (hS_line : (S ∩ affine_line P v).ncard = p - 1)
    (hS_plane : (S ∩ affine_plane f (f P)).ncard = p) :
    ∃! Q, Q ∈ S ∩ affine_plane f (f P) ∧ Q ∉ affine_line P v := by
  have hsub : S ∩ affine_line P v ⊆ S ∩ affine_plane f (f P) :=
    Set.inter_subset_inter_right S hline
  have hcard : ((S ∩ affine_plane f (f P)) \ (S ∩ affine_line P v)).ncard = 1 := by
    rw [Set.ncard_sdiff hsub (Set.toFinite _)]
    rw [hS_plane, hS_line]
    have hp : 2 ≤ p := Nat.Prime.two_le Fact.out
    omega
  have heq : {Q | Q ∈ S ∩ affine_plane f (f P) ∧ Q ∉ affine_line P v} =
      (S ∩ affine_plane f (f P)) \ (S ∩ affine_line P v) := by
    ext x
    dsimp
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  change ∃! Q, Q ∈ {Q | Q ∈ S ∩ affine_plane f (f P) ∧ Q ∉ affine_line P v}
  rw [heq]
  exact Set.singleton_iff_unique_mem.mp (Set.ncard_eq_one.mp hcard)
