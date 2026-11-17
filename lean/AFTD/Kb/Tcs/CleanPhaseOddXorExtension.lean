import AFTD.Prelude
import AFTD.Kb.Tcs.PhaseQueryComputesCleanly

/-!
# clean_phase_odd_xor_extension

Topic: quantum   Node: 2d72016553fb

Provenance: helper lemma. Supporting circuit reduction for OP-1638 and the clean-phase adversary method in arXiv:2611.16412 Section 5.

For any Boolean function invariant under complementing all inputs, an odd-query clean phase circuit yields a clean phase circuit with the same number of queries for the XOR of that function with one additional input bit.
-/

section
variable {B : Type} [Fintype B]

lemma phase_mat_mul_scalar (M : Matrix B B ℂ) (z : ℂ) (v : B → ℂ) :
    M.mulVec (fun i => z * v i) = fun i => z * M.mulVec v i := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

lemma phase_list_scaling (old new : B → ℂ) (z : ℂ)
    (hphase : ∀ b, new b = z * old b) (L : List (Matrix B B ℂ))
    (v : B → ℂ) (c : ℂ) :
    L.foldl (fun w M => M.mulVec (fun b => new b * w b)) (fun b => c * v b) =
      fun b => (c * z ^ L.length) *
        (L.foldl (fun w M => M.mulVec (fun b => old b * w b)) v) b := by
  induction L generalizing v c with
  | nil => simp
  | cons M L ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hstep : M.mulVec (fun b => new b * (c * v b)) =
          fun b => (c * z) * M.mulVec (fun b => old b * v b) b := by
        have heq : (fun b => new b * (c * v b)) =
            (fun b => (c * z) * (old b * v b)) := by
          funext b
          rw [hphase b]
          ring
        rw [heq, phase_mat_mul_scalar]
      rw [hstep, ih]
      simp only [pow_succ]
      funext b
      ring

end

/-- An odd clean-phase circuit extends to an extra XOR input using the original dummy query index. -/
theorem clean_phase_odd_xor_extension {N q : ℕ}
    (f : (Fin N → Bool) → Bool)
    (hinv : ∀ x, f (fun i => !(x i)) = f x)
    (hq : Odd q) (hclean : phase_query_computes_cleanly f q) :
    phase_query_computes_cleanly
      (fun x : Fin (N + 1) → Bool => Bool.xor (x 0) (f (fun i => x i.succ))) q := by
  rcases hclean with ⟨B, instF, instD, reg, ψ0, hnorm, U0, hU0, steps, hsteps, hresult⟩
  letI : Fintype B := instF
  letI : DecidableEq B := instD
  let reg' : B → Option (Fin (N + 1)) := fun b =>
    some (match reg b with | none => 0 | some i => i.succ)
  refine ⟨B, instF, instD, reg', ψ0, hnorm, U0, hU0, steps, hsteps, ?_⟩
  intro x b
  let y : Fin N → Bool := fun i => Bool.xor (x i.succ) (x 0)
  let z : ℂ := if x 0 then -1 else 1
  let old : B → ℂ := fun b => match reg b with
    | none => 1
    | some i => if y i then -1 else 1
  let new : B → ℂ := fun b => if x (match reg b with | none => 0 | some i => i.succ) then -1 else 1
  have hphase : ∀ b, new b = z * old b := by
    intro b
    cases hr : reg b with
    | none => simp [new, z, old, hr]
    | some i =>
        cases ha : x 0 <;> cases hi : x i.succ <;> simp [new, z, old, y, hr, ha, hi, Bool.xor]
  have hfold := phase_list_scaling old new z hphase (List.ofFn steps) (Matrix.mulVec U0 ψ0) 1
  simp only [one_mul, List.length_ofFn] at hfold
  change ((List.ofFn steps).foldl (fun w M => M.mulVec (fun j => new j * w j))
    (Matrix.mulVec U0 ψ0)) b = _
  rw [congrFun hfold b]
  have ho := hresult y b
  change ((List.ofFn steps).foldl (fun w M => M.mulVec (fun j => old j * w j))
      (Matrix.mulVec U0 ψ0)) b = (if f y then (-1 : ℂ) else 1) * ψ0 b at ho
  rw [ho]
  have hf : f y = f (fun i => x i.succ) := by
    cases ha : x 0 with
    | false => simp [y, ha]
    | true => simpa [y, ha, Bool.xor] using hinv (fun i => x i.succ)
  rw [hf]
  cases ha : x 0 <;> cases hb : f (fun i => x i.succ) <;>
    simp [z, ha, hb, Bool.xor, hq.neg_one_pow]
