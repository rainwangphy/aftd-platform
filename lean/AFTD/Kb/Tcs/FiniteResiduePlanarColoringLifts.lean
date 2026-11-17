import AFTD.Prelude

/-!
# finite_residue_planar_coloring_lifts

Topic: combinatorics   Node: 205b4129ba62

Provenance: helper lemma. OP-1482; local-to-global finite-residue coloring reduction

Let K be a field with a subring A, a ring homomorphism from A to ZMod p, and the property that every unit vector in the coordinate plane over K has coordinates in A. If the coordinate plane over ZMod p has a coloring avoiding false unit r-progressions and true unit m-progressions, then the coordinate plane over K has such a coloring.
-/

theorem finite_residue_planar_coloring_lifts (K : Type*) [Field K] (A : Subring K) (p r m : ℕ) (φ : A →+* ZMod p) (hunit : ∀ v : Fin 2 → K, (∑ i : Fin 2, (v i)^2) = 1 → ∀ i, v i ∈ A) (c₀ : (Fin 2 → ZMod p) → Bool) (hred : ∀ x v : Fin 2 → ZMod p, (∑ i : Fin 2, (v i)^2) = 1 → ¬ ∀ k : Fin r, c₀ (fun i => x i + (k.val : ZMod p) * v i) = false) (hblue : ∀ x v : Fin 2 → ZMod p, (∑ i : Fin 2, (v i)^2) = 1 → ¬ ∀ k : Fin m, c₀ (fun i => x i + (k.val : ZMod p) * v i) = true) : ∃ c : (Fin 2 → K) → Bool, (∀ x v : Fin 2 → K, (∑ i : Fin 2, (v i)^2) = 1 → ¬ ∀ k : Fin r, c (fun i => x i + (k.val : K) * v i) = false) ∧ (∀ x v : Fin 2 → K, (∑ i : Fin 2, (v i)^2) = 1 → ¬ ∀ k : Fin m, c (fun i => x i + (k.val : K) * v i) = true) := by
  classical
  let V := Fin 2 → K
  let H : AddSubgroup V := {
    carrier := {x | ∀ i, x i ∈ A}
    zero_mem' := by intro i; exact A.zero_mem
    add_mem' := by intro x y hx hy i; exact A.add_mem (hx i) (hy i)
    neg_mem' := by intro x hx i; exact A.neg_mem (hx i)
  }
  let Q := V ⧸ H
  let proj : V → Q := QuotientAddGroup.mk' H
  have hsurj : Function.Surjective proj := QuotientAddGroup.mk'_surjective H
  let repr : Q → V := fun q => Classical.choose (hsurj q)
  have hrepr (q : Q) : proj (repr q) = q := Classical.choose_spec (hsurj q)
  have hdiff (x : V) : x - repr (proj x) ∈ H := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    exact (hrepr (proj x)).symm
  let read (x : V) (i : Fin 2) : A := ⟨x i - repr (proj x) i, hdiff x i⟩
  let c : V → Bool := fun x => c₀ (fun i => φ (read x i))
  have transfer (x v : V) (hv : (∑ i : Fin 2, (v i)^2) = 1) (k : ℕ) :
      c (fun i => x i + (k : K) * v i) =
        c₀ (fun i => φ (read x i) + (k : ZMod p) * φ (⟨v i, hunit v hv i⟩ : A)) := by
    have hk : (fun i : Fin 2 => (k : K) * v i) ∈ H := by
      intro i
      exact A.mul_mem (show ((k : A) : K) ∈ A from (k : A).property) (hunit v hv i)
    have heq : proj (fun i => x i + (k : K) * v i) = proj x := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hh : (fun i => x i + (k : K) * v i) - x = (fun i => (k : K) * v i) := by
        funext i
        change x i + (k : K) * v i - x i = (k : K) * v i
        ring
      rw [hh]
      exact hk
    dsimp only [c]
    congr 1
    funext i
    have hid : read (fun i => x i + (k : K) * v i) i =
        read x i + (k : A) * (⟨v i, hunit v hv i⟩ : A) := by
      apply Subtype.ext
      simp only [read, heq, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
      ring
    rw [hid, map_add, map_mul, map_natCast]
  have mapped_unit (v : V) (hv : (∑ i : Fin 2, (v i)^2) = 1) :
      (∑ i : Fin 2, (φ (⟨v i, hunit v hv i⟩ : A))^2) = 1 := by
    have hA : (∑ i : Fin 2, ((⟨v i, hunit v hv i⟩ : A))^2) = 1 := by
      apply Subtype.ext
      simpa using hv
    calc
      _ = φ (∑ i : Fin 2, ((⟨v i, hunit v hv i⟩ : A))^2) := by
        rw [map_sum]
        simp only [map_pow]
      _ = 1 := by rw [hA, map_one]
  refine ⟨c, ?_, ?_⟩
  · intro x v hv hh
    apply hred (fun i => φ (read x i)) (fun i => φ (⟨v i, hunit v hv i⟩ : A)) (mapped_unit v hv)
    intro k
    have hk := hh k
    rw [transfer x v hv k.val] at hk
    exact hk
  · intro x v hv hh
    apply hblue (fun i => φ (read x i)) (fun i => φ (⟨v i, hunit v hv i⟩ : A)) (mapped_unit v hv)
    intro k
    have hk := hh k
    rw [transfer x v hv k.val] at hk
    exact hk
