import AFTD.Prelude
import AFTD.Kb.Tcs.Zmod3PermIsAffine
import AFTD.Kb.Tcs.NowhereZeroAffineIsConstant

/-!
# latin_hypercube_is_affine

Topic: combinatorics   Node: 8cafa9c6d2c1

Provenance: helper lemma. step towards ternary_minimal_line_cover_minimum_card_eq_hyperplane

Every order-3 Latin hypercube f : (Fin m → ZMod 3) → ZMod 3 (a function whose restriction to every 1D coordinate line is a bijection) is an affine function f(x) = (∑ i, a i * x i) + b with all coefficients a i nonzero.
-/

/-- Every order-3 Latin hypercube over ZMod 3 is an affine function with nonzero directional coefficients. -/
theorem latin_hypercube_is_affine (m : ℕ) (f : (Fin m → ZMod 3) → ZMod 3) (hf : ∀ (i : Fin m) (c : Fin m → ZMod 3), Function.Bijective (fun t => f (Function.update c i t))) : ∃ (a : Fin m → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3), ∀ x, f x = (∑ i, a i * x i) + b := by
  revert f
  induction m with
  | zero =>
      intro f hf
      refine ⟨fun i => Fin.elim0 i, ?_, f (fun i => Fin.elim0 i), ?_⟩
      · intro i; exact Fin.elim0 i
      · intro x
        have hx : x = fun i => Fin.elim0 i := by
          funext i
          exact Fin.elim0 i
        rw [hx]
        simp
  | succ m ih =>
      intro f hf
      let g : ZMod 3 → (Fin m → ZMod 3) → ZMod 3 := fun c y => f (Fin.cons c y)
      have hg : ∀ c, ∀ (i : Fin m) (cc : Fin m → ZMod 3), Function.Bijective (fun t => g c (Function.update cc i t)) := by
        intro c i cc
        simpa only [g, Fin.cons_update] using hf (Fin.succ i) (Fin.cons c cc)
      obtain ⟨a0, ha0, b0, h0⟩ := ih (g 0) (hg 0)
      obtain ⟨a1, ha1, b1, h1⟩ := ih (g 1) (hg 1)
      let d : ZMod 3 := b1 - b0
      have hline : ∀ y : Fin m → ZMod 3, Function.Bijective (fun t => f (Fin.cons t y)) := by
        intro y
        simpa only [Fin.update_cons_zero] using hf 0 (Fin.cons (0 : ZMod 3) y)
      have hcoef : ∀ i, a1 i - a0 i = 0 := by
        apply nowhere_zero_affine_is_constant m (fun i => a1 i - a0 i) (b1 - b0)
        intro y
        have hsum : (∑ i, (a1 i - a0 i) * y i) = (∑ i, a1 i * y i) - (∑ i, a0 i * y i) := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          ext i
          rw [sub_mul]
        have hd : (∑ i, (a1 i - a0 i) * y i) + (b1 - b0) = g 1 y - g 0 y := by
          rw [h1 y, h0 y, hsum]
          ring
        rw [hd]
        obtain ⟨A, B, hA, hAB⟩ := zmod3_perm_is_affine (fun t => f (Fin.cons t y)) (hline y)
        have hdiff : g 1 y - g 0 y = A := by
          change f (Fin.cons (1 : ZMod 3) y) - f (Fin.cons (0 : ZMod 3) y) = A
          rw [hAB 1, hAB 0]
          ring
        rw [hdiff]
        exact hA
      have hdeq : ∀ i, a1 i = a0 i := by
        intro i
        exact sub_eq_zero.mp (hcoef i)
      have hdiffd : ∀ y : Fin m → ZMod 3, g 1 y - g 0 y = d := by
        intro y
        rw [h1 y, h0 y]
        simp only [hdeq]
        ring
      have hb : d ≠ 0 := by
        let y : Fin m → ZMod 3 := fun _ => 0
        obtain ⟨A, B, hA, hAB⟩ := zmod3_perm_is_affine (fun t => f (Fin.cons t y)) (hline y)
        have hAeq : A = d := by
          calc
            A = A * 1 + B - B := by ring
            _ = f (Fin.cons (1 : ZMod 3) y) - B := by rw [hAB 1]
            _ = f (Fin.cons (1 : ZMod 3) y) - f (Fin.cons (0 : ZMod 3) y) := by
              rw [hAB 0]
              ring
            _ = g 1 y - g 0 y := rfl
            _ = d := hdiffd y
        rw [← hAeq]
        exact hA
      have hmain : ∀ (c : ZMod 3) (y : Fin m → ZMod 3), g c y = c * d + g 0 y := by
        intro c y
        obtain ⟨A, B, hA, hAB⟩ := zmod3_perm_is_affine (fun t => f (Fin.cons t y)) (hline y)
        have hB : B = g 0 y := by
          have h0c := hAB 0
          change f (Fin.cons (0 : ZMod 3) y) = A * 0 + B at h0c
          simpa [g] using h0c.symm
        have hAeq : A = d := by
          calc
            A = A * 1 + B - B := by ring
            _ = f (Fin.cons (1 : ZMod 3) y) - B := by rw [hAB 1]
            _ = f (Fin.cons (1 : ZMod 3) y) - f (Fin.cons (0 : ZMod 3) y) := by
              rw [hAB 0]
              ring
            _ = g 1 y - g 0 y := rfl
            _ = d := hdiffd y
        calc
          g c y = f (Fin.cons c y) := rfl
          _ = A * c + B := hAB c
          _ = c * d + g 0 y := by rw [hAeq, hB]; ring
      let a : Fin (m+1) → ZMod 3 := fun j => Fin.cases d a0 j
      refine ⟨a, ?_, b0, ?_⟩
      · intro j
        cases j using Fin.cases with
        | zero => simpa [a] using hb
        | succ i => simpa [a] using ha0 i
      · intro x
        have hx : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
        rw [← hx]
        change g (x 0) (Fin.tail x) = (∑ i, a i * Fin.cons (x 0) (Fin.tail x) i) + b0
        rw [hmain (x 0) (Fin.tail x)]
        rw [h0 (Fin.tail x)]
        rw [Fin.sum_univ_succ]
        simp only [a, Fin.cases_zero, Fin.cases_succ, Fin.tail, Fin.cons_zero, Fin.cons_succ]
        ring
