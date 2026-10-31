import AFTD.Prelude
import AFTD.Kb.Tcs.StandardQuad
import AFTD.Kb.Tcs.IsTotallyIsotropic
import AFTD.Kb.Tcs.DistanceSet
import AFTD.Kb.Tcs.CylinderSet
import AFTD.Kb.Tcs.DiffSqScaled
import AFTD.Kb.Tcs.CylinderCard
import AFTD.Kb.Tcs.CylinderDistanceSet
import AFTD.Kb.Tcs.StandardQuadConsCons
import AFTD.Kb.Tcs.CylinderConstructionStep

/-!
# cylinder_construction_distance_set

Topic: combinatorics   Node: 3e2665f3019d

Provenance: formalization of a published result. Source: arXiv:2610.34758 Lemma 2.3 -- Geometric progressions in distance sets in odd dimensions over prime fields

Let $p$ be an odd prime (with $p$ prime and $p$ odd) and let $m \ge 0$ be a natural number. There exist an $m$-dimensional submodule $W \le (\mathbb{Z}/p\mathbb{Z})^{2m+1}$ that is totally isotropic with respect to $Q_{2m+1}$ and a vector $e \in (\mathbb{Z}/p\mathbb{Z})^{2m+1}$ orthogonal to $W$ under the standard dot product with $e \notin W$ such that $\kappa := Q_{2m+1}(e) \neq 0$, and for every subset $A \subset \mathbb{Z}/p\mathbb{Z}$, the cylinder set $E_A = \{w + a \cdot e : w \in W, a \in A\}$ satisfies $|E_A| = p^m |A|$ and $\Delta(E_A) = \kappa (A - A)^2$.
-/

lemma cylinder_construction_distance_set_exists
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ∃ (W : Submodule (ZMod p) (Fin (2 * m + 1) → ZMod p)) (e : Fin (2 * m + 1) → ZMod p),
      Module.finrank (ZMod p) W = m ∧
      is_totally_isotropic (2 * m + 1) W ∧
      (∀ w ∈ W, dotProduct e w = 0) ∧
      e ∉ W ∧
      standard_quad (2 * m + 1) e ≠ 0 := by
  induction m with
  | zero =>
    use ⊥
    use fun _ => 1
    refine ⟨finrank_bot (ZMod p) (Fin 1 → ZMod p), ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [Submodule.mem_bot] at hw
      subst hw
      simp [standard_quad]
    · intro w hw
      rw [Submodule.mem_bot] at hw
      subst hw
      simp
    · intro he
      rw [Submodule.mem_bot] at he
      have : (fun (_ : Fin 1) => (1 : ZMod p)) 0 = 0 := congr_fun he 0
      norm_num at this
    · simp [standard_quad]
  | succ m ih =>
    have h_eq : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [h_eq]
    rcases ih with ⟨W, e, hdim, hiso, horth, he, hquad⟩
    exact cylinder_construction_step p (2 * m + 1) m W e hdim hiso horth he hquad

/-- Cylinder construction of distance sets in odd dimensions via isotropic subspaces (Lemma 2.3). -/
theorem cylinder_construction_distance_set
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p) (m : ℕ) :
    ∃ (W : Submodule (ZMod p) (Fin (2 * m + 1) → ZMod p)) (e : Fin (2 * m + 1) → ZMod p),
      Module.finrank (ZMod p) W = m ∧
      is_totally_isotropic (2 * m + 1) W ∧
      (∀ w ∈ W, dotProduct e w = 0) ∧
      e ∉ W ∧
      let κ := standard_quad (2 * m + 1) e
      κ ≠ 0 ∧
      ∀ A : Set (ZMod p),
        (cylinder_set (2 * m + 1) W e A).ncard = p ^ m * A.ncard ∧
        distance_set (2 * m + 1) (cylinder_set (2 * m + 1) W e A) = diff_sq_scaled κ A := by
  have _ := hp_odd
  rcases cylinder_construction_distance_set_exists p m with ⟨W, e, hdim, hiso, horth, he, hquad⟩
  refine ⟨W, e, hdim, hiso, horth, he, hquad, fun A => ⟨?_, ?_⟩⟩
  · exact cylinder_card (2 * m + 1) p m W e hdim he A
  · exact cylinder_distance_set (2 * m + 1) W e hiso horth A
