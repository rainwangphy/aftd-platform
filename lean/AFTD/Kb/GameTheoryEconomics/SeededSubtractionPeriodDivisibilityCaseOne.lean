import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SeededSubtractionSeq
import AFTD.Kb.GameTheoryEconomics.LeastEventualPeriod
import AFTD.Kb.GameTheoryEconomics.IsEventualPeriod

/-!
# seeded_subtraction_period_divisibility_case_one

Topic: combinatorial_games   Node: ab50069af260

Provenance: original. Related work: knowledgebase, OP-1251

For parameter $a = 1$, every binary seed of length 3 generates a subtraction sequence whose least eventual period is 4, which divides $3(1) + 1 = 4$.
-/

/-- The state transition for the a=1 subtraction recurrence acting on the last-three-values triple. -/
def seeded_subtraction_period_divisibility_case_one_step (t : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (t.2.1, t.2.2, !t.2.2 || !t.2.1 || !t.1)

/-- The window `(w n, w (n+1), w (n+2))` of the generated sequence. -/
def seeded_subtraction_period_divisibility_case_one_triple (seed : Fin 3 → Bool) (n : ℕ) : Bool × Bool × Bool :=
  (seeded_subtraction_seq 1 seed n, seeded_subtraction_seq 1 seed (n+1), seeded_subtraction_seq 1 seed (n+2))

/-- Unfolding the recurrence for `a = 1` at indices at least 3. -/
theorem seeded_subtraction_period_divisibility_case_one_rec (seed : Fin 3 → Bool) (n : ℕ) (h : 3 ≤ n) :
    seeded_subtraction_seq 1 seed n =
      (!seeded_subtraction_seq 1 seed (n-1) || !seeded_subtraction_seq 1 seed (n-2) || !seeded_subtraction_seq 1 seed (n-3)) := by
  conv_lhs => rw [seeded_subtraction_seq]
  dsimp only
  rw [dif_neg (by omega : ¬ n < 2 * 1 + 1)]
  rw [dif_neg (by decide : ¬ (1 = 0))]

/-- Shifting the window by one applies the state transition. -/
theorem seeded_subtraction_period_divisibility_case_one_triple_succ (seed : Fin 3 → Bool) (n : ℕ) :
    seeded_subtraction_period_divisibility_case_one_triple seed (n+1) =
      seeded_subtraction_period_divisibility_case_one_step (seeded_subtraction_period_divisibility_case_one_triple seed n) := by
  unfold seeded_subtraction_period_divisibility_case_one_triple seeded_subtraction_period_divisibility_case_one_step
  simp only
  rw [seeded_subtraction_period_divisibility_case_one_rec seed (n+3) (by omega)]
  simp

/-- The window at index `n` is the `n`-fold iterate of the transition applied to the seed. -/
theorem seeded_subtraction_period_divisibility_case_one_triple_iterate (seed : Fin 3 → Bool) (n : ℕ) :
    seeded_subtraction_period_divisibility_case_one_triple seed n =
      seeded_subtraction_period_divisibility_case_one_step^[n] (seeded_subtraction_period_divisibility_case_one_triple seed 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [seeded_subtraction_period_divisibility_case_one_triple_succ, ih, Function.iterate_succ_apply']

/-- The transition satisfies `T^6 = T^2` on all triples. -/
theorem seeded_subtraction_period_divisibility_case_one_step_six :
    ∀ t : Bool × Bool × Bool,
      seeded_subtraction_period_divisibility_case_one_step^[6] t =
        seeded_subtraction_period_divisibility_case_one_step^[2] t := by decide

/-- The four-term block of values starting at any index at least 2 is not invariant under shifts by 1, 2, or 3. -/
theorem seeded_subtraction_period_divisibility_case_one_witness :
    ∀ t : Bool × Bool × Bool, ∀ p : Fin 3,
      ∃ n : Fin 5,
        (seeded_subtraction_period_divisibility_case_one_step^[2 + n.val + (p.val + 1)] t).1 ≠
        (seeded_subtraction_period_divisibility_case_one_step^[2 + n.val] t).1 := by decide

/-- Every value from index 2 onwards repeats with period 4. -/
theorem seeded_subtraction_period_divisibility_case_one_period_four (seed : Fin 3 → Bool) (n : ℕ) (hn : 2 ≤ n) :
    seeded_subtraction_seq 1 seed (n+4) = seeded_subtraction_seq 1 seed n := by
  have key : seeded_subtraction_period_divisibility_case_one_triple seed (n+4) =
      seeded_subtraction_period_divisibility_case_one_triple seed n := by
    calc seeded_subtraction_period_divisibility_case_one_triple seed (n+4)
        = seeded_subtraction_period_divisibility_case_one_step^[n+4] (seeded_subtraction_period_divisibility_case_one_triple seed 0) := seeded_subtraction_period_divisibility_case_one_triple_iterate seed (n+4)
      _ = seeded_subtraction_period_divisibility_case_one_step^[n-2] (seeded_subtraction_period_divisibility_case_one_step^[6] (seeded_subtraction_period_divisibility_case_one_triple seed 0)) := by
            rw [show n + 4 = (n - 2) + 6 from by omega, Function.iterate_add_apply]
      _ = seeded_subtraction_period_divisibility_case_one_step^[n-2] (seeded_subtraction_period_divisibility_case_one_step^[2] (seeded_subtraction_period_divisibility_case_one_triple seed 0)) := by
            rw [seeded_subtraction_period_divisibility_case_one_step_six]
      _ = seeded_subtraction_period_divisibility_case_one_step^[(n-2)+2] (seeded_subtraction_period_divisibility_case_one_triple seed 0) := by rw [← Function.iterate_add_apply]
      _ = seeded_subtraction_period_divisibility_case_one_step^[n] (seeded_subtraction_period_divisibility_case_one_triple seed 0) := by rw [show (n-2)+2 = n from by omega]
      _ = seeded_subtraction_period_divisibility_case_one_triple seed n := (seeded_subtraction_period_divisibility_case_one_triple_iterate seed n).symm
  exact congrArg Prod.fst key

/-- Shifting an index at least 2 by any multiple of 4 leaves the value unchanged. -/
theorem seeded_subtraction_period_divisibility_case_one_period_mult (seed : Fin 3 → Bool) (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    seeded_subtraction_seq 1 seed (m + 4*k) = seeded_subtraction_seq 1 seed m := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hstep : m + 4*(j+1) = (m + 4*j) + 4 := by ring
      rw [hstep, seeded_subtraction_period_divisibility_case_one_period_four seed (m+4*j) (by omega), ih]

/-- 4 is an eventual period of every sequence generated with `a = 1`. -/
theorem seeded_subtraction_period_divisibility_case_one_eventual_four (seed : Fin 3 → Bool) :
    is_eventual_period (seeded_subtraction_seq 1 seed) 4 :=
  ⟨by decide, 2, fun n hn => seeded_subtraction_period_divisibility_case_one_period_four seed n hn⟩

/-- No `p` with `1 ≤ p ≤ 3` is an eventual period, because within each period-4 block the lone `false` shifts. -/
theorem seeded_subtraction_period_divisibility_case_one_not_eventual_lt_four (seed : Fin 3 → Bool) (p : ℕ) (hp : 0 < p) (hp4 : p ≤ 3) :
    ¬ is_eventual_period (seeded_subtraction_seq 1 seed) p := by
  rintro ⟨_, N, hN⟩
  have hp3 : p - 1 < 3 := by omega
  obtain ⟨n, hn⟩ := seeded_subtraction_period_divisibility_case_one_witness
    (seeded_subtraction_period_divisibility_case_one_triple seed 0) ⟨p-1, hp3⟩
  have hval : (⟨p-1, hp3⟩ : Fin 3).val + 1 = p := by simp; omega
  rw [hval] at hn
  have hv : ∀ k : ℕ,
      (seeded_subtraction_period_divisibility_case_one_step^[k] (seeded_subtraction_period_divisibility_case_one_triple seed 0)).1 =
        seeded_subtraction_seq 1 seed k := by
    intro k
    rw [← seeded_subtraction_period_divisibility_case_one_triple_iterate]
    rfl
  have hmismatch : seeded_subtraction_seq 1 seed (2 + n.val + p) ≠ seeded_subtraction_seq 1 seed (2 + n.val) := by
    rw [← hv (2+n.val+p), ← hv (2+n.val)]
    exact hn
  set a := 2 + n.val with ha
  set b := 2 + n.val + p with hb
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have h1 : seeded_subtraction_seq 1 seed ((a + 4*N) + p) = seeded_subtraction_seq 1 seed (a + 4*N) := hN _ (by omega)
  have h2 : seeded_subtraction_seq 1 seed (a + 4*N) = seeded_subtraction_seq 1 seed a := seeded_subtraction_period_divisibility_case_one_period_mult seed a ha2 N
  have h3 : seeded_subtraction_seq 1 seed (b + 4*N) = seeded_subtraction_seq 1 seed b := seeded_subtraction_period_divisibility_case_one_period_mult seed b hb2 N
  have heq : (a + 4*N) + p = b + 4*N := by omega
  rw [heq] at h1
  have hfinal : seeded_subtraction_seq 1 seed b = seeded_subtraction_seq 1 seed a := by
    calc seeded_subtraction_seq 1 seed b
        = seeded_subtraction_seq 1 seed (b + 4*N) := h3.symm
      _ = seeded_subtraction_seq 1 seed (a + 4*N) := h1
      _ = seeded_subtraction_seq 1 seed a := h2
  exact hmismatch hfinal

/-- The least eventual period of every sequence generated with `a = 1` is exactly 4. -/
theorem seeded_subtraction_period_divisibility_case_one_least_period (seed : Fin 3 → Bool) :
    least_eventual_period (seeded_subtraction_seq 1 seed) = 4 := by
  unfold least_eventual_period
  set S := {p : ℕ | is_eventual_period (seeded_subtraction_seq 1 seed) p} with hS
  have hne : S.Nonempty := ⟨4, seeded_subtraction_period_divisibility_case_one_eventual_four seed⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  have hle : sInf S ≤ 4 := Nat.sInf_le (seeded_subtraction_period_divisibility_case_one_eventual_four seed)
  apply le_antisymm hle
  by_contra hcon
  have hlt : sInf S < 4 := Nat.lt_of_not_le hcon
  have hpos : 0 < sInf S := hmem.1
  exact seeded_subtraction_period_divisibility_case_one_not_eventual_lt_four seed (sInf S) hpos (by omega) hmem

/-- For a = 1, every seed of length 3 generates a sequence with least eventual period 4, dividing 3(1)+1. -/
theorem seeded_subtraction_period_divisibility_case_one :
    (∀ seed : Fin 3 → Bool, least_eventual_period (seeded_subtraction_seq 1 seed) = 4) ∧
    (∀ seed : Fin 3 → Bool,
      least_eventual_period (seeded_subtraction_seq 1 seed) ∣ 3 * 1 ∨
      least_eventual_period (seeded_subtraction_seq 1 seed) ∣ 3 * 1 + 1) := by
  constructor
  · intro seed
    exact seeded_subtraction_period_divisibility_case_one_least_period seed
  · intro seed
    rw [seeded_subtraction_period_divisibility_case_one_least_period seed]
    right
    norm_num
