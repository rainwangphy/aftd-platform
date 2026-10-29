import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetPolynomialPotentialDualBound
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.G

/-!
# condorcet_cubic_subset_potential_residue_barrier

Topic: social_choice   Node: 22eb7f489bdf

Provenance: helper lemma. IN-341 complete interpretation of the eight-row cubic diagnostic from IN-339, experiment8338. Supports the OP-19 uniform certificate campaign. The raw arithmetic and affine incidence audit is8502. The strict election convention is Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf ; related selector formulation arXiv:2604.19851v2. No research advance is asserted.

For candidates indexed modulo19, orient a to b when b-a is one of the nine nonzero quadratic residues. Consider any finite family of natural-weighted challenger claims whose committees consist only of out-neighbors of their challenger. Let an integer subset potential be a membership polynomial of degree at most three with zero constant term, with arbitrary signed coefficients. If it satisfies every local removal inequality for this family, then1539 times the total claim weight is at most2869 times its full-set value. Thus it cannot certify a strict half-weight bound. This is a restriction on cubic polynomial potentials, not an election counterexample or dimension bound.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace In341CubicField

abbrev C := ZMod 19
abbrev J := C × Fin 8 × Fin 9

def mults : Fin 9 → C := ![1, 4, 5, 6, 7, 9, 11, 16, 17]
def rowMasks : Fin 8 → ℕ := ![1, 1303, 12481, 42577, 204799, 217083, 228347, 249851]
def coeff : Fin 8 → ℕ := ![2793, 266, 3724, 2527, 6156, 1463, 1539, 1615]
def A (j : J) : Finset C := univ.filter fun b =>
  (rowMasks j.2.1).testBit (((b-j.1)*mults j.2.2).val)
def root (j : J) : C := j.1
def weight (j : J) : ℕ := coeff j.2.1

def mono : Finset (Finset C) :=
  (univ.powersetCard 1 ∪ univ.powersetCard 2) ∪ univ.powersetCard 3

-- Test only actual monomial members, without materializing the full local
-- remaining set for every finite arithmetic check.
def incidence (T : Finset C) : ℕ :=
  ∑ t ∈ T, ∑ i : Fin 8, ∑ q : Fin 9,
    if ∀ b ∈ T, (rowMasks i).testBit (((b-t)*mults q).val) then coeff i else 0

theorem incidence_shift (T : Finset C) (z : C) :
    incidence (T.image fun t => t+z) = incidence T := by
  unfold incidence
  rw [sum_image]
  · apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro q _
    simp only [forall_mem_image, add_sub_add_right_eq_sub]
  · intro a _ b _ hab
    exact add_right_cancel hab

-- Translation reduces the finite verification from all subsets to361
-- pairs of differences. No coefficient or electorate symmetry is assumed.
theorem incidence_zero_row_0 : ∀ v : C, incidence {0,0,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_1 : ∀ v : C, incidence {0,1,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_2 : ∀ v : C, incidence {0,2,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_3 : ∀ v : C, incidence {0,3,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_4 : ∀ v : C, incidence {0,4,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_5 : ∀ v : C, incidence {0,5,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_6 : ∀ v : C, incidence {0,6,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_7 : ∀ v : C, incidence {0,7,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_8 : ∀ v : C, incidence {0,8,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_9 : ∀ v : C, incidence {0,9,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_10 : ∀ v : C, incidence {0,10,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_11 : ∀ v : C, incidence {0,11,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_12 : ∀ v : C, incidence {0,12,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_13 : ∀ v : C, incidence {0,13,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_14 : ∀ v : C, incidence {0,14,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_15 : ∀ v : C, incidence {0,15,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_16 : ∀ v : C, incidence {0,16,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_17 : ∀ v : C, incidence {0,17,v} = 180747 := by
  decide +kernel


theorem incidence_zero_row_18 : ∀ v : C, incidence {0,18,v} = 180747 := by
  decide +kernel



end In341CubicField

open Finset
open scoped BigOperators
set_option maxHeartbeats 300000

-- Keep finite-sum algebra abstract; instantiating a concrete finite universe
-- before this step causes needless definitional expansion of its enumeration.
private theorem in341_incidence_sum_generic
    (C I Q : Type*) [Fintype C] [DecidableEq C] [Fintype I] [Fintype Q]
    (T : Finset C) (A : C × I × Q → Finset C) (L : I → ℕ)
    (P : C → I → Q → C → Prop) [∀ t i q, DecidablePred (P t i q)]
    (hA : ∀ t i q b, b ∈ A (t,i,q) ↔ P t i q b) :
    (∑ j : C × I × Q, if j.1 ∈ T ∧ T ⊆ A j then L j.2.1 else 0) =
      ∑ t ∈ T, ∑ i : I, ∑ q : Q,
        if ∀ b ∈ T, P t i q b then L i else 0 := by
  simp only [Fintype.sum_prod_type]
  calc
    (∑ t : C, ∑ i : I, ∑ q : Q,
      if t ∈ T ∧ T ⊆ A (t,i,q) then L i else 0)
      = ∑ t ∈ T, ∑ i : I, ∑ q : Q,
          if t ∈ T ∧ T ⊆ A (t,i,q) then L i else 0 := by
        symm
        apply sum_subset (subset_univ T)
        intro t _ ht
        simp [ht]
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro q _
      simp only [ht, true_and, Finset.subset_iff, hA]

private theorem in341_claim_slice_le_generic
    (C I Q : Type*) [Fintype C] [DecidableEq C] [Fintype I] [Fintype Q]
    (A : C × I × Q → Finset C) (L : I → ℕ) (S : Finset C) (f : C) :
    (∑ i : I, ∑ q : Q, if S ⊆ (A (f,i,q)).erase f then L i else 0) ≤
      ∑ j : C × I × Q,
        if f = j.1 ∧ S ⊆ (A j).erase j.1 then L j.2.1 else 0 := by
  let g : C → ℕ := fun t => ∑ i : I, ∑ q : Q,
    if f = t ∧ S ⊆ (A (t,i,q)).erase t then L i else 0
  have hh : g f ≤ ∑ t, g t := single_le_sum (fun t _ => Nat.zero_le _) (mem_univ f)
  simpa only [g, Fintype.sum_prod_type, eq_self_iff_true, true_and] using hh
namespace In341CubicField
theorem incidence_zero_certificate : ∀ u v : C, incidence {0,u,v} = 180747 := by
  intro u v
  fin_cases u
  · exact incidence_zero_row_0 v
  · exact incidence_zero_row_1 v
  · exact incidence_zero_row_2 v
  · exact incidence_zero_row_3 v
  · exact incidence_zero_row_4 v
  · exact incidence_zero_row_5 v
  · exact incidence_zero_row_6 v
  · exact incidence_zero_row_7 v
  · exact incidence_zero_row_8 v
  · exact incidence_zero_row_9 v
  · exact incidence_zero_row_10 v
  · exact incidence_zero_row_11 v
  · exact incidence_zero_row_12 v
  · exact incidence_zero_row_13 v
  · exact incidence_zero_row_14 v
  · exact incidence_zero_row_15 v
  · exact incidence_zero_row_16 v
  · exact incidence_zero_row_17 v
  · exact incidence_zero_row_18 v

theorem incidence_of_card (T : Finset C) (hpos : 0 < T.card) (hcard : T.card ≤ 3) :
    incidence T = 180747 := by
  have htuple : ∃ x y z : C, T = {x,y,z} := by
    have hc : T.card=1 ∨ T.card=2 ∨ T.card=3 := by omega
    rcases hc with h1 | h2 | h3
    · obtain ⟨x,hx⟩ := card_eq_one.mp h1
      exact ⟨x,x,x,by simpa using hx⟩
    · obtain ⟨x,y,_,hxy⟩ := card_eq_two.mp h2
      exact ⟨x,y,y,by simpa using hxy⟩
    · obtain ⟨x,y,z,_,_,_,hxyz⟩ := card_eq_three.mp h3
      exact ⟨x,y,z,hxyz⟩
  rcases htuple with ⟨x,y,z,rfl⟩
  have hs := incidence_shift ({0,y-x,z-x} : Finset C) x
  simp only [image_insert, image_singleton, zero_add, sub_add_cancel] at hs
  exact hs.trans (incidence_zero_certificate (y-x) (z-x))

theorem incidence_certificate : ∀ T ∈ mono, incidence T = 180747 := by
  intro T hT
  have hm := hT
  simp only [mono, mem_union, mem_powersetCard, subset_univ, true_and] at hm
  apply incidence_of_card T <;> omega

theorem root_mem : ∀ j, root j ∈ A j := by
  intro j
  rcases j with ⟨t,i,q⟩
  simp only [root, A, mem_filter, mem_univ, true_and, sub_self, zero_mul]
  fin_cases i <;> decide +kernel

theorem row_cover : ∀ (q : Fin 9) (b : C),
    b.val ∈ ({1,4,5,6,7,9,11,16,17} : Finset ℕ) →
    ∀ i : Fin 4, (rowMasks ⟨i.val+4, by omega⟩).testBit ((b*mults q).val) := by
  decide +kernel

end In341CubicField


-- Append after PolynomialDual.lean and CubicIncidence.lean for testing.

namespace In341CubicField

set_option backward.isDefEq.respectTransparency false in
theorem incidence_eq_sum (T : Finset C) :
    (∑ j : J, if root j ∈ T ∧ T ⊆ A j then weight j else 0) = incidence T := by
  simpa only [root,weight,incidence] using
    in341_incidence_sum_generic C (Fin 8) (Fin 9) T A coeff
      (fun t i q b => (rowMasks i).testBit (((b-t)*mults q).val))
      (fun t i q b => by simp only [A,mem_filter,mem_univ,true_and])

set_option backward.isDefEq.respectTransparency false in
theorem claim_coverage (S : Finset C) (f : C)
    (hf : f ∉ S)
    (hc : ∀ b ∈ S,
      (b-f).val ∈ ({1,4,5,6,7,9,11,16,17} : Finset ℕ)) :
    96957 ≤ ∑ j : J, if f = root j ∧ S ⊆ (A j).erase (root j) then weight j else 0 := by
  have hsub : ∀ (i : Fin 8), 4 ≤ i.val → ∀ q : Fin 9,
      S ⊆ (A (f,i,q)).erase f := by
    intro i hi q b hb
    let k : Fin 4 := ⟨i.val-4, by omega⟩
    have hk : (⟨k.val+4, by omega⟩ : Fin 8) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    have hr := row_cover q (b-f) (hc b hb) k
    rw [hk] at hr
    refine mem_erase.mpr ⟨by intro he; subst b; exact hf hb, ?_⟩
    change b ∈ univ.filter (fun b => (rowMasks i).testBit (((b-f)*mults q).val))
    exact mem_filter.mpr ⟨mem_univ _, hr⟩
  have hpart : ∀ i : Fin 8,
      (if 4 ≤ i.val then 9*coeff i else 0) ≤
        ∑ q : Fin 9, if S ⊆ (A (f,i,q)).erase f then coeff i else 0 := by
    intro i
    by_cases hi : 4 ≤ i.val
    · simp [hi, hsub i hi, mul_comm]
    · simp only [hi, if_false]
      exact sum_nonneg fun q _ => by positivity
  have hsum := sum_le_sum (s := univ) (fun i _ => hpart i)
  have heval : (∑ i : Fin 8, if 4 ≤ i.val then 9*coeff i else 0) = 96957 := by
    decide +kernel
  rw [heval] at hsum
  apply hsum.trans
  simpa only [root,weight] using in341_claim_slice_le_generic C (Fin 8) (Fin 9) A coeff S f

end In341CubicField

set_option backward.isDefEq.respectTransparency false

theorem condorcet_cubic_subset_potential_residue_barrier
    (q : ℕ) (S : Fin q → Finset (ZMod 19)) (f : Fin q → ZMod 19)
    (w : Fin q → ℕ) (H : Finset (ZMod 19) → ℤ)
    (c : Finset (ZMod 19) → ℤ)
    (hform : ∀ R, H R = ∑ T ∈
      (((univ : Finset (ZMod 19)).powersetCard 1 ∪ univ.powersetCard 2) ∪
        univ.powersetCard 3), if T ⊆ R then c T else 0)
    (hout : ∀ i, f i ∉ S i)
    (hcompat : ∀ i, ∀ b ∈ S i,
      (b-f i).val ∈ ({1,4,5,6,7,9,11,16,17} : Finset ℕ))
    (hstep : ∀ R : Finset (ZMod 19), ∀ b ∈ R,
      ((∑ i, if f i = b ∧ S i ⊆ R.erase b then w i else 0) : ℤ) +
        H (R.erase b) ≤ H R) :
    (1539 : ℤ) * (∑ i, (w i : ℤ)) ≤ 2869 * H univ := by
  have hd := condorcet_polynomial_potential_dual_bound
    (ZMod 19) (Fin q) In341CubicField.J In341CubicField.mono c H hform S f w
    In341CubicField.A In341CubicField.root In341CubicField.weight 180747 96957
    In341CubicField.root_mem
    (fun T hT => (In341CubicField.incidence_eq_sum T).trans
      (In341CubicField.incidence_certificate T hT))
    (fun i => In341CubicField.claim_coverage (S i) (f i) (hout i) (hcompat i))
    hstep
  norm_num at hd
  omega
