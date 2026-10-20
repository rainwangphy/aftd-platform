import AFTD.Prelude
import AFTD.Kb.Tcs.Op98SqExchangeBound
import AFTD.Kb.Tcs.Op98ConflictDegreeBound
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.ConflictNeighborhood
import AFTD.Kb.Tcs.IsSquareLocallyOptimal

/-!
# op_98_one_cluster_packing_bound

Topic: approximation   Node: 74ba7cf714bf

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

If every set o of a packing O has at most one conflict neighbour in A, then weight(O) ≤ 2·weight(A). Each o has exactly one neighbour a (the singleton-square condition excludes zero), so O splits into the fibres Fib a = {o ∈ O : N(A,{o}) = {a}}; each fibre is a packing of at most |a| ≤ 4 sets all conflicting with a, so N(A, Fib a) = {a} and the factor-2 exchange inequality gives weight(Fib a) ≤ 2·weight a. Summing over the pairwise disjoint fibres gives the claim.
-/

/-- Ratio-2 bound in the star-cluster regime where every competitor set has exactly one conflict neighbour. -/
theorem op_98_one_cluster_packing_bound {α : Type*} [DecidableEq α]
    (inst : WeightedSetPackingInstance α 4) (A O : Finset (Finset α))
    (hA : is_square_locally_optimal inst 4 A) (hO : is_packing inst O)
    (h1 : ∀ o ∈ O, (conflict_neighborhood A {o}).card ≤ 1) :
    packing_weight inst O ≤ 2 * packing_weight inst A := by
  have hAp : is_packing inst A := hA.1
  have hloc := hA.2
  have hmemN : ∀ (b : Finset α) (X : Finset (Finset α)),
      b ∈ conflict_neighborhood A X ↔ b ∈ A ∧ ∃ x ∈ X, ¬ Disjoint b x := by
    intro b X
    simp only [conflict_neighborhood, Finset.mem_filter]
  have hmemS : ∀ (b o : Finset α),
      b ∈ conflict_neighborhood A {o} ↔ b ∈ A ∧ ¬ Disjoint b o := by
    intro b o
    rw [hmemN]
    constructor
    · rintro ⟨hb, x, hx, hnd⟩
      rw [Finset.mem_singleton] at hx
      exact ⟨hb, hx ▸ hnd⟩
    · rintro ⟨hb, hnd⟩
      exact ⟨hb, o, Finset.mem_singleton_self o, hnd⟩
  have hne : ∀ o ∈ O, (conflict_neighborhood A {o}).Nonempty := by
    intro o ho
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsub : ({o} : Finset (Finset α)) ⊆ inst.family := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hO.1 ho
    have hp : is_packing inst ({o} : Finset (Finset α)) := by
      refine ⟨hsub, ?_⟩
      intro x hx y hy hne'
      simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hne'
    have h4 : ({o} : Finset (Finset α)).card ≤ 4 := by
      simp only [Finset.card_singleton]; norm_num
    have key := hloc {o} hp h4
    rw [squared_weight, squared_weight, Finset.sum_singleton, hemp, Finset.sum_empty] at key
    have hpos : 0 < inst.weight o := inst.weight_pos o (hO.1 ho)
    nlinarith
  have huniq : ∀ o ∈ O, ∃ a ∈ A, conflict_neighborhood A {o} = {a} := by
    intro o ho
    have hcpos : 0 < (conflict_neighborhood A {o}).card := Finset.card_pos.mpr (hne o ho)
    have hcle := h1 o ho
    have hc : (conflict_neighborhood A {o}).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    refine ⟨a, ?_, ha⟩
    have : a ∈ conflict_neighborhood A {o} := by
      rw [ha]; exact Finset.mem_singleton_self a
    exact (hmemS a o).mp this |>.1
  set Fib : Finset α → Finset (Finset α) :=
    fun a => O.filter (fun o => conflict_neighborhood A {o} = {a}) with hFib
  have hFib_mem : ∀ a o, o ∈ Fib a ↔ o ∈ O ∧ conflict_neighborhood A {o} = {a} := by
    intro a o; simp only [hFib, Finset.mem_filter]
  have hFib_sub : ∀ a, Fib a ⊆ O := by
    intro a o ho; exact (hFib_mem a o).mp ho |>.1
  have hcover : A.biUnion Fib = O := by
    ext o
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨a, _, ho⟩; exact hFib_sub a ho
    · intro ho
      obtain ⟨a, haA, ha⟩ := huniq o ho
      exact ⟨a, haA, (hFib_mem a o).mpr ⟨ho, ha⟩⟩
  have hpdisj : (↑A : Set (Finset α)).PairwiseDisjoint Fib := by
    intro a haA b hbA hne'
    change Disjoint (Fib a) (Fib b)
    rw [Finset.disjoint_left]
    intro o hoa hob
    have h1a : conflict_neighborhood A {o} = {a} := (hFib_mem a o).mp hoa |>.2
    have h1b : conflict_neighborhood A {o} = {b} := (hFib_mem b o).mp hob |>.2
    have : a = b := by
      rw [h1b] at h1a
      exact (Finset.singleton_inj.mp h1a).symm
    exact hne' this
  have hsum1 : packing_weight inst O = ∑ a ∈ A, packing_weight inst (Fib a) := by
    simp only [packing_weight]
    rw [← hcover]
    exact Finset.sum_biUnion (f := fun s => inst.weight s) hpdisj
  have hterm : ∀ a ∈ A, packing_weight inst (Fib a) ≤ 2 * inst.weight a := by
    intro a haA
    have hwa : 0 < inst.weight a := inst.weight_pos a (hAp.1 haA)
    by_cases hemp : Fib a = ∅
    · rw [hemp, packing_weight, Finset.sum_empty]
      linarith
    · have hpk : is_packing inst (Fib a) :=
        ⟨fun x hx => hO.1 (hFib_sub a hx),
         fun x hx y hy hne' => hO.2 (hFib_sub a hx) (hFib_sub a hy) hne'⟩
      have hc4 : (Fib a).card ≤ 4 := by
        have hsub : Fib a ⊆ O.filter (fun o => ¬ Disjoint a o) := by
          intro o ho
          rw [Finset.mem_filter]
          refine ⟨(hFib_mem a o).mp ho |>.1, ?_⟩
          have hconf : conflict_neighborhood A {o} = {a} := (hFib_mem a o).mp ho |>.2
          have hmem : a ∈ conflict_neighborhood A {o} := by
            rw [hconf]; exact Finset.mem_singleton_self a
          exact (hmemS a o).mp hmem |>.2
        calc (Fib a).card ≤ (O.filter (fun o => ¬ Disjoint a o)).card := Finset.card_le_card hsub
          _ ≤ a.card := op_98_conflict_degree_bound inst O a hO
          _ ≤ 4 := inst.card_le a (hAp.1 haA)
      have hN : conflict_neighborhood A (Fib a) = {a} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨?_, ?_⟩
        · rw [hmemN]
          refine ⟨haA, ?_⟩
          obtain ⟨o, ho⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          refine ⟨o, ho, ?_⟩
          have hconf : conflict_neighborhood A {o} = {a} := (hFib_mem a o).mp ho |>.2
          have hmem : a ∈ conflict_neighborhood A {o} := by
            rw [hconf]; exact Finset.mem_singleton_self a
          exact (hmemS a o).mp hmem |>.2
        · intro b hb
          rw [hmemN] at hb
          obtain ⟨hbA, o, ho, hnd⟩ := hb
          have hconf : conflict_neighborhood A {o} = {a} := (hFib_mem a o).mp ho |>.2
          have hmem : b ∈ conflict_neighborhood A {o} := (hmemS b o).mpr ⟨hbA, hnd⟩
          rw [hconf, Finset.mem_singleton] at hmem
          exact hmem
      have hbound := op_98_sq_exchange_bound inst A (Fib a) hA hpk hc4
      rw [hN] at hbound
      simpa [packing_weight] using hbound
  calc packing_weight inst O = ∑ a ∈ A, packing_weight inst (Fib a) := hsum1
    _ ≤ ∑ a ∈ A, 2 * inst.weight a := Finset.sum_le_sum hterm
    _ = 2 * packing_weight inst A := by
        rw [packing_weight, Finset.mul_sum]
