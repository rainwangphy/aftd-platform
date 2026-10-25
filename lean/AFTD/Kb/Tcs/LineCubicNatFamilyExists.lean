import AFTD.Prelude
import AFTD.Kb.Tcs.LineCubicBoundaryExtension

/-!
# line_cubic_nat_family_exists

Topic: quantum   Node: eb505f75ef48

Provenance: helper lemma. Auxiliary construction for OP-4, the line cubic exact-count question in arXiv:2610.01024; new boundary induction developed here.

Every n at least five admits a bounded natural-index support family of size 2n+1 with the required line cubic moments and the boundary invariant.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace LineBuild

def base : Finset (Finset ℕ) :=
  {{0,3,4},{0,1,3,4},{1,4},{1,2,4},{0,2,3,4},{0,1,2,3,4},
    {2,3,4},{2},{2,3},{3},{3,4}}

theorem good_base : Good 5 base := by
  constructor <;> decide +kernel

def family : ℕ → Finset (Finset ℕ)
  | 0 => base
  | k+1 => step (k+5) (family k)

theorem good_family (k : ℕ) : Good (k+5) (family k) := by
  induction k with
  | zero => exact good_base
  | succ k hk =>
    simpa [family, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      good_step (k+5) (by omega) (family k) hk


end LineBuild

theorem line_cubic_nat_family_exists (n : ℕ) (hn : 5 ≤ n) : ∃ S : Finset (Finset ℕ), LineBuild.Good n S := by
  have he : n-5+5 = n := by omega
  have hg := LineBuild.good_family (n-5)
  rw [he] at hg
  exact ⟨LineBuild.family (n-5),hg⟩
