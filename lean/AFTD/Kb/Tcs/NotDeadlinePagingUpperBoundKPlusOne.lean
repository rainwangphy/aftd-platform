import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest
import AFTD.Kb.Tcs.IsCompetitiveRatio
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.IsOnlineClairvoyantScheduleGen
import AFTD.Kb.Tcs.IsFeasibleSchedule

/-!
# not_deadline_paging_upper_bound_k_plus_one

Topic: online_algorithms   Node: 0c9a28167e6b

Provenance: original. Related work: refutes `deadline_paging_upper_bound_k_plus_one`

The statement `deadline_paging_upper_bound_k_plus_one` is false: The statement (for every k≥1, every finite α with card ≥ k+1, every C₀ of size k, there is an online Alg that is feasible on every feasible instance and (k+1)-competitive) is FALSE already for k=1, |α|=3, |C₀|=1. The failure is not about the ratio at all: the *feasibility* conjunct of `IsCompetitiveRatio` is unsatisfiable, because `IsOnlineClairvoyantScheduleGen` forces the algorithm to commit to the same cache at time 1 on two different feasible instances whose feasibility requires contradictory contents at time 1.

Concretely take α = 3 pages {q0,q1,q2}, C₀={q0}, k=1, and consider two request lists (written (page,arrival,deadline)):
  reqsB = [(q0,0,0),(q2,0,2),(q1,0,2),(q1,2,2)]
  reqsC = [(q0,0,0),(q2,0,2),(q1,0,2),(q2,2,2)]
Both are feasible (k=1):
  reqsB served by cache sequence q0 (t=0), q2 (t=1), q1 (t=2);
  reqsC served by q0 (t=0), q1 (t=1), q2 (t=2).
Their arrival-≤-1 filters are identical (the last request of each has arrival 2), so `IsOnlineClairvoyantScheduleGen` forces Alg reqsB 1 = Alg reqsC 1.

On the one hand, feasibility of Alg reqsB for reqsB: the request (q1,2,2) forces q1 ∈ Alg reqsB 2, hence (card ≤ 1) Alg reqsB 2 = {q1}; then (q2,0,2) forces q2 ∈ Alg reqsB t for some t∈{0,1,2}, and since Alg reqsB 0 = {q0} and Alg reqsB 2 = {q1}, we get q2 ∈ Alg reqsB 1.
On the other hand, feasibility of Alg reqsC for reqsC: (q2,2,2) forces Alg reqsC 2 = {q2}; then (q1,0,2) forces q1 ∈ Alg reqsC t for some t∈{0,1,2}, and since Alg reqsC 0={q0} and Alg reqsC 2={q2}, we get q1 ∈ Alg reqsC 1 = Alg reqsB 1.
Thus both q1 and q2 lie in Alg reqsB 1, contradicting card(Alg reqsB 1) ≤ 1. So no Alg satisfies the feasibility conjunct, hence none is (ρ)-competitive for any ρ.

This is a genuine contradiction in the Lean definitions (fetch-only cost, hard deadlines), independent of the (k+1) bound; it likely stems from the combination of `IsOnlineClairvoyantScheduleGen` (which filters only by arrival) with the requirement of feasibility on all feasible instances. A verified Lean proof of the negation is provided; it instantiates the counterexample using ULift(Fin 3) so it holds at an arbitrary universe level.
-/

theorem not_deadline_paging_upper_bound_k_plus_one : ¬ (∀ (k : ℕ) (hk : 1 ≤ k) {α : Type*} [Fintype α] [DecidableEq α] (hn : k + 1 ≤ Fintype.card α)
    (C₀ : Finset α) (hC₀ : C₀.card = k), ∃ (Alg : List (DeadlineRequest α) → (ℕ → Finset α)),
      IsCompetitiveRatio k C₀ Alg (k + 1 : ℝ)) := by
  classical
  intro h
  let q0 : ULift (Fin 3) := ULift.up 0
  let q1 : ULift (Fin 3) := ULift.up 1
  let q2 : ULift (Fin 3) := ULift.up 2
  obtain ⟨Alg, hgen, hfeas, hcost⟩ :=
    h 1 (le_refl 1) (α := ULift (Fin 3)) (by simp) ({q0} : Finset (ULift (Fin 3))) (by simp [q0])
  let a : DeadlineRequest (ULift (Fin 3)) := ⟨q0, 0, 0, le_refl 0⟩
  let b : DeadlineRequest (ULift (Fin 3)) := ⟨q2, 0, 2, by decide⟩
  let c : DeadlineRequest (ULift (Fin 3)) := ⟨q1, 0, 2, by decide⟩
  let dB : DeadlineRequest (ULift (Fin 3)) := ⟨q1, 2, 2, by decide⟩
  let dC : DeadlineRequest (ULift (Fin 3)) := ⟨q2, 2, 2, by decide⟩
  let reqsB : List (DeadlineRequest (ULift (Fin 3))) := [a, b, c, dB]
  let reqsC : List (DeadlineRequest (ULift (Fin 3))) := [a, b, c, dC]
  let schedB : ℕ → Finset (ULift (Fin 3)) := fun t => if t = 0 then {q0} else if t = 1 then {q2} else {q1}
  let schedC : ℕ → Finset (ULift (Fin 3)) := fun t => if t = 0 then {q0} else if t = 1 then {q1} else {q2}
  have feasB : ∃ opt, IsFeasibleSchedule 1 ({q0} : Finset (ULift (Fin 3))) opt reqsB := by
    refine ⟨schedB, ?_, ?_, ?_⟩
    · simp [schedB]
    · intro t; dsimp only [schedB]; split_ifs <;> simp
    · intro r hr
      simp only [reqsB, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [a], by simp [a], by simp [a, schedB]⟩
      · exact ⟨1, by simp [b], by simp [b], by simp [b, schedB]⟩
      · exact ⟨2, by simp [c], by simp [c], by simp [c, schedB]⟩
      · exact ⟨2, by simp [dB], by simp [dB], by simp [dB, schedB]⟩
  have feasC : ∃ opt, IsFeasibleSchedule 1 ({q0} : Finset (ULift (Fin 3))) opt reqsC := by
    refine ⟨schedC, ?_, ?_, ?_⟩
    · simp [schedC]
    · intro t; dsimp only [schedC]; split_ifs <;> simp
    · intro r hr
      simp only [reqsC, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [a], by simp [a], by simp [a, schedC]⟩
      · exact ⟨2, by simp [b], by simp [b], by simp [b, schedC]⟩
      · exact ⟨1, by simp [c], by simp [c], by simp [c, schedC]⟩
      · exact ⟨2, by simp [dC], by simp [dC], by simp [dC, schedC]⟩
  have hFB := hfeas reqsB feasB
  have hFC := hfeas reqsC feasC
  obtain ⟨h0B, hcardB, hserveB⟩ := hFB
  obtain ⟨h0C, hcardC, hserveC⟩ := hFC
  have hmem1 : q1 ∈ Alg reqsB 2 := by
    obtain ⟨t, ht1, ht2, hmem⟩ := hserveB dB (by simp [reqsB])
    simp only [dB] at ht1 ht2 hmem
    have ht : t = 2 := by omega
    simpa [ht] using hmem
  have hEq1 : Alg reqsB 2 = {q1} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hmem1, fun x hx => Finset.card_le_one.mp (hcardB 2) x hx q1 hmem1⟩
  have hmem2C : q2 ∈ Alg reqsC 2 := by
    obtain ⟨t, ht1, ht2, hmem⟩ := hserveC dC (by simp [reqsC])
    simp only [dC] at ht1 ht2 hmem
    have ht : t = 2 := by omega
    simpa [ht] using hmem
  have hEq2 : Alg reqsC 2 = {q2} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hmem2C, fun x hx => Finset.card_le_one.mp (hcardC 2) x hx q2 hmem2C⟩
  have hB1 : q2 ∈ Alg reqsB 1 := by
    obtain ⟨t, ht1, ht2, hmem⟩ := hserveB b (by simp [reqsB])
    simp only [b] at ht1 ht2 hmem
    interval_cases t
    · rw [h0B] at hmem; simp [q0, q2] at hmem
    · exact hmem
    · rw [hEq1] at hmem; simp [q1, q2] at hmem
  have hC1 : q1 ∈ Alg reqsC 1 := by
    obtain ⟨t, ht1, ht2, hmem⟩ := hserveC c (by simp [reqsC])
    simp only [c] at ht1 ht2 hmem
    interval_cases t
    · rw [h0C] at hmem; simp [q0, q1] at hmem
    · exact hmem
    · rw [hEq2] at hmem; simp [q1, q2] at hmem
  have hfilt : List.filter (fun r => decide (r.arrival ≤ 1)) reqsB
             = List.filter (fun r => decide (r.arrival ≤ 1)) reqsC := by
    simp [reqsB, reqsC, a, b, c, dB, dC]
  have heq := hgen reqsB reqsC 1 hfilt
  have hC1' : q1 ∈ Alg reqsB 1 := by rw [heq]; exact hC1
  have huniq : q1 = q2 := Finset.card_le_one.mp (hcardB 1) q1 hC1' q2 hB1
  exact absurd huniq (by simp [q1, q2])
