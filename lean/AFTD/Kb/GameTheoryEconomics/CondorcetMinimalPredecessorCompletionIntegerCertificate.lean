import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPredecessorAcyclicCut
import AFTD.Kb.GameTheoryEconomics.CondorcetCrossedUniformFamilyIncidenceBound

/-!
# condorcet_minimal_predecessor_completion_integer_certificate

Topic: social_choice   Node: 1854199723bb

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

For a globally minimal S_k core and a nonempty uniform family F containing every undominated (k+1)-set, the incidence weights Z*d(a) on core vertices and (k+1)Z-1 on repair indices strictly separate every pair consisting of an acyclic core subset A and a subfamily B of repair sets disjoint from A. The theorem states the integer inequality directly, with its exact total weight.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_minimal_predecessor_completion_integer_certificate
    (m k : ℕ) (hk : 0 < k) (R : Fin m → Fin m → Prop)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hminimal : ∀ S : Finset (Fin m),
      (∀ J : Finset (Fin m), J ⊆ S → J.card ≤ k →
        ∃ a ∈ S, a ∉ J ∧ ∀ b ∈ J, R a b) → S = univ)
    (F : Finset (Finset (Fin m))) (hF : F.Nonempty)
    (hcard : ∀ T ∈ F, T.card = k+1)
    (hcomplete : ∀ T : Finset (Fin m), T.card = k+1 →
      (¬∃ a, a ∉ T ∧ ∀ b ∈ T, R a b) → T ∈ F) :
    let Z := F.card
    let d : Fin m → ℕ := fun a => (F.filter fun T => a∈T).card
    let c := (k+1)*Z-1
    (∑ a,d a) = (k+1)*Z ∧
    ∀ (A : Finset (Fin m)) (B : Finset (Finset (Fin m))),
      WellFounded (fun a b : {a : Fin m // a∈A} => R a.val b.val) →
      B ⊆ F → (∀ T ∈ B, Disjoint A T) →
      2*(Z*(∑ a∈A,d a)+c*B.card) < Z*(∑ a,d a)+c*Z := by
  classical
  dsimp only
  have hdegree : (∑ a : Fin m, (F.filter fun T => a∈T).card) = (k+1)*F.card := by
    calc
      (∑ a : Fin m, (F.filter fun T => a∈T).card) =
          ∑ a : Fin m, ∑ T∈F, if a∈T then 1 else 0 := by
        simp only [card_eq_sum_ones,sum_filter]
      _ = ∑ T∈F, ∑ a : Fin m, if a∈T then 1 else 0 := sum_comm
      _ = ∑ T∈F, T.card := by simp
      _ = ∑ T∈F, (k+1) := sum_congr rfl (fun T hT => hcard T hT)
      _ = (k+1)*F.card := by simp [Nat.mul_comm]
  refine ⟨hdegree,?_⟩
  intro A B hA hBF hB
  have hcut : A=∅ ∨ ∃ T∈F, (A∩T).Nonempty ∧ ¬T⊆A := by
    by_cases hempty : A=∅
    · exact Or.inl hempty
    · obtain ⟨T,hTc,hTb,⟨a,haT,haA⟩,⟨b,hbT,hbA⟩⟩ :=
        condorcet_minimal_predecessor_acyclic_cut m k hk R hroot hminimal A
          (nonempty_iff_ne_empty.mpr hempty) hA
      exact Or.inr ⟨T,hcomplete T hTc hTb,⟨a,mem_inter.mpr ⟨haA,haT⟩⟩,
        fun h => hbA (h hbT)⟩
  have hbound := condorcet_crossed_uniform_family_incidence_bound m (k+1)
    (by omega) F hF hcard A hcut B hBF hB
  have hz : 0<F.card := card_pos.mpr hF
  have hprod : 0<(k+1)*F.card := Nat.mul_pos (by omega) hz
  have hc : ((k+1)*F.card-1)+1 = (k+1)*F.card := Nat.sub_add_cancel (by omega)
  rw [hdegree]
  calc
    2*(F.card*(∑ a∈A,(F.filter fun T => a∈T).card)+((k+1)*F.card-1)*B.card)
        ≤ 2*(((k+1)*F.card-1)*F.card) := Nat.mul_le_mul_left 2 hbound
    _ < F.card*((k+1)*F.card)+((k+1)*F.card-1)*F.card := by
      have heq : F.card*((k+1)*F.card) = ((k+1)*F.card-1)*F.card+F.card := by
        calc
          F.card*((k+1)*F.card) = F.card*(((k+1)*F.card-1)+1) :=
            congrArg (fun x => F.card*x) hc.symm
          _ = ((k+1)*F.card-1)*F.card+F.card := by ring
      omega
