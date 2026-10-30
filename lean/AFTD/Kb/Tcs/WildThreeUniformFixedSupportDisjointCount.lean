import AFTD.Prelude
import AFTD.Kb.Tcs.WildThreeUniformDisjointPairCount
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# wild_three_uniform_fixed_support_disjoint_count

Topic: graphs   Node: 9e1bff68b444

Provenance: helper lemma. IN-364 / OP-306, continuation of the finite weighted-partition route for https://arxiv.org/html/2610.22142v1, Sections3.3 and6. Standard permutation-orbit background: Matchings and Representation Theory (2018), Section4.10, https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/9d33772f-c7dc-409f-a4ed-521da8d87890/content. The witness triple system is standard incidence data; these are route helpers or finite method diagnostics. No wild-number bound, new exact sharpness case, general sign theorem, or research advance is claimed.

For a finite indexed family T_i of three-element sets and a fixed three-element set S, assume each vertex of S occurs in d indices and each distinct pair in S occurs in l indices. If D counts indices disjoint from S and Q counts indices equal to S, then D+Q+3d=N+3l in the integers, where N is the index-type cardinality. Repeated supports count with multiplicity; hypotheses are only needed on S.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem wild_fixed_support_incidence_sum
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (T : ι → Finset κ) (S : Finset κ) :
    (∑ i : ι, ((S ∩ T i).card : ℤ)) =
      ∑ a ∈ S, ((univ.filter fun i => a ∈ T i).card : ℤ) := by
  classical
  have hcard (i : ι) : ((S ∩ T i).card : ℤ) =
      ∑ a ∈ S, if a ∈ T i then (1 : ℤ) else 0 := by
    simp [← sum_filter,filter_mem_eq_inter]
  simp_rw [hcard]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  simp [← sum_filter]

theorem wild_three_uniform_fixed_support_disjoint_count
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (T : ι → Finset κ) (S : Finset κ) (d l : ℕ)
    (hsize : ∀ i, (T i).card = 3) (hS : S.card = 3)
    (hvertex : ∀ a ∈ S, (univ.filter fun i => a ∈ T i).card = d)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (univ.filter fun i => a ∈ T i ∧ b ∈ T i).card = l) :
    ((univ.filter fun i => Disjoint S (T i)).card : ℤ) +
      ((univ.filter fun i => S = T i).card : ℤ) + 3*(d : ℤ) =
        (Fintype.card ι : ℤ) + 3*(l : ℤ) := by
  classical
  have hinter : (∑ i : ι, ((S ∩ T i).card : ℤ)) = 3*(d : ℤ) := by
    rw [wild_fixed_support_incidence_sum]
    calc
      _ = ∑ a ∈ S, (d : ℤ) := by
        apply sum_congr rfl
        intro a ha
        rw [hvertex a ha]
      _ = _ := by simp [hS]
  have hoff : (∑ i : ι, ((S ∩ T i).offDiag.card : ℤ)) = 6*(l : ℤ) := by
    simp_rw [offDiag_inter]
    rw [wild_fixed_support_incidence_sum]
    calc
      _ = ∑ z ∈ S.offDiag, (l : ℤ) := by
        apply sum_congr rfl
        intro z hz
        obtain ⟨ha,hb,hne⟩ := mem_offDiag.mp hz
        have hf : (univ.filter fun i => z ∈ (T i).offDiag) =
            (univ.filter fun i => z.1 ∈ T i ∧ z.2 ∈ T i) := by
          ext i
          simp [mem_offDiag,hne]
        rw [hf,hpair z.1 ha z.2 hb hne]
      _ = _ := by simp [offDiag_card,hS]
  have heq := sum_congr (s₁ := (univ : Finset ι)) rfl
    (fun i _ => wild_three_set_disjoint_indicator S (T i) hS (hsize i))
  have hD : (∑ i : ι, if Disjoint S (T i) then (1 : ℤ) else 0) =
      ((univ.filter fun i => Disjoint S (T i)).card : ℤ) := by simp [← sum_filter]
  have hQ : (∑ i : ι, if S = T i then (1 : ℤ) else 0) =
      ((univ.filter fun i => S = T i).card : ℤ) := by simp [← sum_filter]
  simp only [sum_sub_distrib,sum_add_distrib] at heq
  simp_rw [← mul_sum] at heq
  simp only [sum_const,card_univ,nsmul_eq_mul] at heq
  rw [hinter,hoff,hD,hQ] at heq
  linarith
