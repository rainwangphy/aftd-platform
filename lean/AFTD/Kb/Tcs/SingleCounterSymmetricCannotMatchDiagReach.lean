import AFTD.Prelude
import AFTD.Kb.Tcs.SingleCounterStepPreservesOneCoord
import AFTD.Kb.Tcs.DiagTwoCounterMachineIsSymmetric
import AFTD.Kb.Tcs.DiagTwoCounterMachineReachRelIff
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachineIsSingleCounterUpdate
import AFTD.Kb.Tcs.TwoCounterMachine
import AFTD.Kb.Tcs.TwoCounterMachineStep
import AFTD.Kb.Tcs.TwoCounterMachineIsSymmetric
import AFTD.Kb.Tcs.TwoCounterMachineReachRel

/-!
# single_counter_symmetric_cannot_match_diag_reach

Topic: automata   Node: 3c0f7f81b963

Provenance: helper lemma. step towards op_360_single_counter_update_strictly_less_expressive

No finite-state symmetric 2-counter machine with single-counter updates can have reachability relation equal to that of the diagonal machine between false and true.
-/

def single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum :
    TwoCounterInstr → ℕ
  | TwoCounterInstr.update w1 w2 => w1.natAbs + w2.natAbs
  | _ => 0

noncomputable def single_counter_symmetric_cannot_match_diag_reach_weight_bound
    {Q : Type*} (M : TwoCounterMachine Q) : ℕ :=
  M.transitions.sum (fun t => single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum t.2.1)

lemma single_counter_symmetric_cannot_match_diag_reach_weight_bound_spec
    {Q : Type*} (M : TwoCounterMachine Q) (q q' : Q) (w1 w2 : ℤ)
    (hmem : (q, TwoCounterInstr.update w1 w2, q') ∈ M.transitions) :
    w1.natAbs ≤ single_counter_symmetric_cannot_match_diag_reach_weight_bound M ∧
      w2.natAbs ≤ single_counter_symmetric_cannot_match_diag_reach_weight_bound M := by
  unfold single_counter_symmetric_cannot_match_diag_reach_weight_bound
  have hnonneg : ∀ i ∈ M.transitions,
      0 ≤ single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum i.2.1 := by
    intro i _; cases i.2.1 <;> simp [single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum]
  have hle := Finset.single_le_sum
    (f := fun t => single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum t.2.1) hnonneg hmem
  have hval : single_counter_symmetric_cannot_match_diag_reach_instr_abs_sum
      (TwoCounterInstr.update w1 w2) = w1.natAbs + w2.natAbs := rfl
  rw [show (⟨q, TwoCounterInstr.update w1 w2, q'⟩ : Q × TwoCounterInstr × Q).2.1
        = TwoCounterInstr.update w1 w2 from rfl] at hle
  simp only [hval] at hle
  constructor <;> omega

lemma single_counter_symmetric_cannot_match_diag_reach_alt_endpoint
    {Q : Type*} (M : TwoCounterMachine Q)
    (hsym : two_counter_machine_is_symmetric M)
    (hsc : two_counter_machine_is_single_counter_update M)
    (B : ℕ)
    (hB : ∀ (q q' : Q) (a b : ℤ),
      (q, TwoCounterInstr.update a b, q') ∈ M.transitions → a.natAbs ≤ B ∧ b.natAbs ≤ B)
    (s0 : Q) (x : ℕ × ℕ) (t : Q) (y : ℕ × ℕ)
    (h : Relation.ReflTransGen (two_counter_machine_step M) (s0, x) (t, y))
    (hxy : x ≠ y) (hbig1 : 2 * B + 1 ≤ y.1) (hbig2 : 2 * B + 1 ≤ y.2) :
    ∃ y' : ℕ × ℕ, y' ≠ y ∧
      Relation.ReflTransGen (two_counter_machine_step M) (s0, x) (t, y') := by
  classical
  revert hbig1 hbig2
  let motive : (z : Q × ℕ × ℕ) →
      Relation.ReflTransGen (two_counter_machine_step M) (s0, x) z → Prop :=
    fun z _ => x ≠ z.2 → 2 * B + 1 ≤ z.2.1 → 2 * B + 1 ≤ z.2.2 →
      ∃ y' : ℕ × ℕ, y' ≠ z.2 ∧
        Relation.ReflTransGen (two_counter_machine_step M) (s0, x) (z.1, y')
  have hmain : motive (t, y) h := by
    refine Relation.ReflTransGen.rec (motive := motive) ?base ?step h
    · intro hxx; exact absurd rfl hxx
    · intro b c hpath hstep ih hxc hb1 hb2
      rcases hstep with ⟨w1, w2, htrans, heq1, heq2⟩ | ⟨htr, hz, hce⟩ | ⟨htr, hz, hce⟩
      · by_cases hzero : w1 = 0 ∧ w2 = 0
        · obtain ⟨hw1, hw2⟩ := hzero
          subst hw1; subst hw2
          have hc1 : c.2.1 = b.2.1 := by omega
          have hc2 : c.2.2 = b.2.2 := by omega
          have hbc : b.2 = c.2 := by ext <;> simp [hc1, hc2]
          have ihx : x ≠ b.2 := by rw [hbc]; exact hxc
          have ihb1 : 2 * B + 1 ≤ b.2.1 := by rw [← hc1]; exact hb1
          have ihb2 : 2 * B + 1 ≤ b.2.2 := by rw [← hc2]; exact hb2
          obtain ⟨y', hy'ne, hy'path⟩ := ih ihx ihb1 ihb2
          refine ⟨y', ?_, ?_⟩
          · rw [← hbc]; exact hy'ne
          · exact Relation.ReflTransGen.tail hy'path
              (Or.inl ⟨0, 0, by simpa using htrans, by simp, by simp⟩)
        · have hsingle : w1 = 0 ∨ w2 = 0 := hsc b.1 c.1 w1 w2 htrans
          have hwne : w1 ≠ w2 := by
            intro he
            apply hzero
            rcases hsingle with h1 | h2
            · subst h1; subst he; exact ⟨rfl, rfl⟩
            · subst h2; subst he; exact ⟨rfl, rfl⟩
          obtain ⟨hbw1, hbw2⟩ := hB b.1 c.1 w1 w2 htrans
          have hbnd1 : |w1| ≤ (B : ℤ) := by
            rw [← Int.natCast_natAbs]; exact_mod_cast hbw1
          have hbnd2 : |w2| ≤ (B : ℤ) := by
            rw [← Int.natCast_natAbs]; exact_mod_cast hbw2
          have hbnd1lo := (abs_le.mp hbnd1).1
          have hbnd1hi := (abs_le.mp hbnd1).2
          have hbnd2lo := (abs_le.mp hbnd2).1
          have hbnd2hi := (abs_le.mp hbnd2).2
          have hpos1 : (0 : ℤ) ≤ (b.2.1 : ℤ) + w2 := by
            have : (b.2.1 : ℤ) = (c.2.1 : ℤ) - w1 := by omega
            rw [this]; omega
          have hpos2 : (0 : ℤ) ≤ (b.2.2 : ℤ) + w1 := by
            have : (b.2.2 : ℤ) = (c.2.2 : ℤ) - w2 := by omega
            rw [this]; omega
          refine ⟨(((b.2.1 : ℤ) + w2).toNat, ((b.2.2 : ℤ) + w1).toNat), ?_, ?_⟩
          · intro heq
            have h1' : (↑(((b.2.1 : ℤ) + w2).toNat) : ℤ) = (c.2.1 : ℤ) := by
              have := congrArg (fun p : ℕ × ℕ => p.1) heq
              exact_mod_cast this
            rw [Int.toNat_of_nonneg hpos1] at h1'
            have hEq : ((b.2.1 : ℤ) + w1) = (c.2.1 : ℤ) := heq1
            omega
          · exact Relation.ReflTransGen.tail hpath
              (Or.inl ⟨w2, w1, hsym b.1 c.1 w1 w2 htrans,
                by rw [Int.toNat_of_nonneg hpos1], by rw [Int.toNat_of_nonneg hpos2]⟩)
      · have : c.2.1 = 0 := by rw [hce, hz]
        omega
      · have : c.2.2 = 0 := by rw [hce, hz]
        omega
  exact hmain hxy

/-- No finite-state symmetric 2-counter machine with single-counter updates can reproduce the reachability relation of the diagonal machine. -/
theorem single_counter_symmetric_cannot_match_diag_reach :
    ∀ (Q' : Type) (_ : Finite Q') (M' : TwoCounterMachine Q') (_ : two_counter_machine_is_symmetric M')
      (_ : two_counter_machine_is_single_counter_update M') (q0 q1 : Q'),
      two_counter_machine_reach_rel M' q0 q1 ≠
        two_counter_machine_reach_rel (⟨{(false, TwoCounterInstr.update 1 1, true)}⟩ : TwoCounterMachine Bool) false true := by
  intro Q' _ M' hsym hsc q0 q1 hEq
  exfalso
  classical
  let B : ℕ := single_counter_symmetric_cannot_match_diag_reach_weight_bound M'
  have hB : ∀ (q q' : Q') (a b : ℤ),
      (q, TwoCounterInstr.update a b, q') ∈ M'.transitions → a.natAbs ≤ B ∧ b.natAbs ≤ B :=
    fun q q' a b h => single_counter_symmetric_cannot_match_diag_reach_weight_bound_spec M' q q' a b h
  let u : ℕ × ℕ := (2 * B + 1, 2 * B + 1)
  let w : ℕ × ℕ := (u.1 + 1, u.2 + 1)
  have hwd : (u, w) ∈ two_counter_machine_reach_rel
      (⟨{(false, TwoCounterInstr.update 1 1, true)}⟩ : TwoCounterMachine Bool) false true := by
    rw [diag_two_counter_machine_reach_rel_iff]
    exact ⟨rfl, rfl⟩
  rw [← hEq] at hwd
  have hpath : Relation.ReflTransGen (two_counter_machine_step M') (q0, u) (q1, w) := by
    simpa only [two_counter_machine_reach_rel, Set.mem_ofPred_eq] using hwd
  have hxy : u ≠ w := by
    intro hh
    have := congrArg (fun p : ℕ × ℕ => p.1) hh
    simp [w] at this
  have hbig1 : 2 * B + 1 ≤ w.1 := by simp [w, u]
  have hbig2 : 2 * B + 1 ≤ w.2 := by simp [w, u]
  obtain ⟨y', hy'ne, hy'path⟩ :=
    single_counter_symmetric_cannot_match_diag_reach_alt_endpoint M' hsym hsc B hB q0 u q1 w hpath hxy hbig1 hbig2
  have hmemM : (u, y') ∈ two_counter_machine_reach_rel M' q0 q1 := by
    simpa only [two_counter_machine_reach_rel, Set.mem_ofPred_eq] using hy'path
  rw [hEq] at hmemM
  rw [diag_two_counter_machine_reach_rel_iff] at hmemM
  apply hy'ne
  ext
  · exact hmemM.1
  · exact hmemM.2
