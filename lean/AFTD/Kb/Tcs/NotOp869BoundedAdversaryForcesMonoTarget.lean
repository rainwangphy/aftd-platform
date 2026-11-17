import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869BoundedAdversaryOneVertex
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# not_op869_bounded_adversary_forces_mono_target

Topic: online_algorithms   Node: ee8e1979e98e

Provenance: original. Related work: refutes `op869_bounded_adversary_forces_mono_target`

The statement `op869_bounded_adversary_forces_mono_target` is false: A one-vertex one-move game forces one color but cannot force two.
-/

theorem not_op869_bounded_adversary_forces_mono_target : ¬ (∀ {n : ℕ} (k t K K' D : ℕ) (hKK : K ≤ K')
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C), op869_bounded_adversary_forces k t K' D fuel i P C) := by
  intro h
  have hw : op869_bounded_adversary_forces 1 1 1 0 1 0
      (fun _ : Fin 1 => ∅) (fun _ : Fin 1 => ∅) :=
    op869_bounded_adversary_one_vertex (by decide) (by decide)
  have hb := h (n:=1) 1 1 1 2 0 (by decide) 1 0 (fun _ : Fin 1 => ∅) (fun _ : Fin 1 => ∅) hw
  have hfalse : ¬ op869_bounded_adversary_forces 1 1 2 0 1 0
      (fun _ : Fin 1 => ∅) (fun _ : Fin 1 => ∅) := by
    classical
    simp only [op869_bounded_adversary_forces, dif_pos (by decide : 0 < 1)]
    rintro ⟨S, hS, hcolor, hdegree, hnext⟩
    have hS0 : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨a, ha⟩
      have h := hS a ha
      omega
    subst S
    have h := hnext {0} (by simp) (by simp)
    simp [op869_bounded_adversary_forces] at h
  exact hfalse hb
