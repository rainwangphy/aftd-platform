import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetNonpositivePotentialAcyclic
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicHalfCoverSignaturePairsGeSeven

/-!
# condorcet_heavy_pair_acyclic_cover_potential_break

Topic: social_choice   Node: 98a02491a425

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. FourCoverPotential.lean. Structural support constraint on the new equivalent main route. No new election bound or research novelty is claimed.

For any finite S3 relation, any nonnegative weighted family of induced acyclic sets and real vertex potential has an arrow violating the half-cover potential inequality whenever two distinct coefficients carry at least half the total weight and a third distinct coefficient is positive.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_heavy_pair_acyclic_cover_potential_break
    (m n : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m)) (d : Fin n → ℝ)
    (q : Fin m → ℝ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hd : ∀ v, 0 ≤ d v) (hk : 0 < d k)
    (hheavy : (∑ v, d v) ≤ 2*(d i+d j))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ∃ a b, R a b ∧
      2 * (∑ v, if a ∈ U v then d v else 0) + q a < (∑ v, d v) + q b := by
  classical
  by_contra hbad
  push_neg at hbad
  let p : Fin m → ℝ := fun a => ∑ v, if a ∈ U v then d v else 0
  let T : ℝ := ∑ v, d v
  let A := univ \ (U i ∪ U j)
  let c : Fin m → ℝ := fun a => 2*p a-T
  have hmass (a : Fin m) (I : Finset (Fin n))
      (hI : ∀ v ∈ I, a ∉ U v) : p a + (∑ v ∈ I, d v) ≤ T := by
    rw [← Fintype.sum_ite_mem I d]
    change (∑ v, if a ∈ U v then d v else 0) + (∑ v, if v ∈ I then d v else 0) ≤ ∑ v, d v
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro v hv
    by_cases hvI : v ∈ I
    · simp [hvI,hI v hvI]
    · by_cases ha : a ∈ U v <;> simp [hvI,ha,hd v]
  have hA : WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) := by
    apply condorcet_nonpositive_potential_acyclic m R A (U k) c q
    · intro a ha
      have hnot : a ∉ U i ∧ a ∉ U j := by simpa [A] using ha
      have hp := hmass a {i,j} (by
        intro v hv
        simp only [mem_insert,mem_singleton] at hv
        rcases hv with rfl|rfl
        · exact hnot.1
        · exact hnot.2)
      simp only [sum_pair hij] at hp
      change 2*p a-T ≤ 0
      change T ≤ 2*(d i+d j) at hheavy
      linarith
    · intro a ha hz
      by_contra hak
      have hnot : a ∉ U i ∧ a ∉ U j := by simpa [A] using ha
      have hp := hmass a {i,j,k} (by
        intro v hv
        simp only [mem_insert,mem_singleton] at hv
        rcases hv with rfl|rfl|rfl
        · exact hnot.1
        · exact hnot.2
        · exact hak)
      simp [hij,hik,hjk] at hp
      change 2*p a-T = 0 at hz
      change T ≤ 2*(d i+d j) at hheavy
      linarith
    · intro a b ha hb hab
      have hh := hbad a b hab
      change (∑ v, d v) + q b ≤ 2*p a+q a at hh
      change q b ≤ q a+(2*p a-T)
      dsimp only [T]
      linarith
    · exact hU k
  let V : Fin 3 → Finset (Fin m) := ![U i,U j,A]
  have hV : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ V v} => R a.val b.val) := by
    intro v
    fin_cases v
    · exact hU i
    · exact hU j
    · exact hA
  obtain ⟨a,ha0,ha1,ha2⟩ := condorcet_acyclic_three_sources_omit m 3 R V hroot hV 0 1 2
  have haA : a ∈ A := by simpa [A,V] using And.intro ha0 ha1
  exact ha2 haA
