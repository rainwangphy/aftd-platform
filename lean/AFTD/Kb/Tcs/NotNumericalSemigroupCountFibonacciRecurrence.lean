import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroupCount
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupGenus
import AFTD.Kb.Tcs.NumericalSemigroupMultiplicity
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber

/-!
# not_numerical_semigroup_count_fibonacci_recurrence

Topic: combinatorics   Node: da44034a2b8c

Provenance: original. Related work: refutes `numerical_semigroup_count_fibonacci_recurrence`

The statement `numerical_semigroup_count_fibonacci_recurrence` is false: The identity is false. Take F = 3, m = 2, g = 2: indeed F + 2 = 5 ≤ 6 = 3*m and m = 2 ≤ 2 = F - 1.

LHS: n_{3,2,2} = 1. The complement of such a semigroup is contained in {0,1,2,3} (3 is a gap, everything ≥ 4 is in S), 0 is in S, multiplicity 2 forces 2 ∈ S and 1 ∉ S, and the genus is 2, so the gap set is exactly {1,3}. Hence the unique such semigroup is {0,2} ∪ [4,∞).

RHS: n_{1,1,1} + n_{1,1,0} = 0 + 0. A semigroup with Frobenius number 1 has 1 as a gap (1 = sSup of the gap set, and the sSup of a finite nonempty set of naturals is a member of it), while multiplicity 1 forces 1 ∈ S (sInf of the positive elements is a member). Contradiction.

So the claimed equation reads 1 = 0. The recurrence fails for every (F, m, g) = (F, F-1, F-1) with F ≥ 3 (the semigroup {0, F-1} ∪ [F+1,∞)); brute-force enumeration up to F = 18 finds no other failures. A probable correction is to add the hypothesis m ≤ F - 2 (equivalently F ≥ m + 2).
-/

theorem not_numerical_semigroup_count_fibonacci_recurrence : ¬ (∀ (F m g : ℕ) (hlow : F + 2 ≤ 3 * m) (hhigh : m ≤ F - 1), numerical_semigroup_count F m g =
      numerical_semigroup_count (F - 2) (m - 1) (g - 1) +
      numerical_semigroup_count (F - 2) (m - 1) (g - 2)) := by
  intro hcontra
  have mult_mem : ∀ (S : NumericalSemigroup) (m : ℕ), numerical_semigroup_multiplicity S = m →
      0 < m → m ∈ (S.toAddSubmonoid : Set ℕ) := by
    intro S m h hm
    unfold numerical_semigroup_multiplicity at h
    set A : Set ℕ := {x : ℕ | x ∈ (S.toAddSubmonoid : Set ℕ) ∧ 0 < x} with hA
    have hne : A.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc, Nat.sInf_empty] at h
      omega
    have hmem := Nat.sInf_mem hne
    rw [h] at hmem
    exact hmem.1
  have mult_le : ∀ (S : NumericalSemigroup) (m : ℕ), numerical_semigroup_multiplicity S = m →
      ∀ x ∈ (S.toAddSubmonoid : Set ℕ), 0 < x → m ≤ x := by
    intro S m h x hx hx0
    unfold numerical_semigroup_multiplicity at h
    rw [← h]
    exact Nat.sInf_le ⟨hx, hx0⟩
  have frob_mem_compl : ∀ (S : NumericalSemigroup) (F : ℕ),
      numerical_semigroup_frobenius_number S = F → 0 < F →
      F ∈ (S.toAddSubmonoid : Set ℕ)ᶜ := by
    intro S F h hF
    unfold numerical_semigroup_frobenius_number at h
    have hne : ((S.toAddSubmonoid : Set ℕ)ᶜ).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc, csSup_empty] at h
      simp at h
      omega
    have hmem := Nat.sSup_mem hne S.finite_compl.bddAbove
    rwa [h] at hmem
  have compl_le_frob : ∀ (S : NumericalSemigroup) (F : ℕ),
      numerical_semigroup_frobenius_number S = F →
      ∀ x ∈ (S.toAddSubmonoid : Set ℕ)ᶜ, x ≤ F := by
    intro S F h x hx
    unfold numerical_semigroup_frobenius_number at h
    calc x ≤ sSup ((S.toAddSubmonoid : Set ℕ)ᶜ) := le_csSup S.finite_compl.bddAbove hx
      _ = F := h
  let nsC : Set ℕ := {0, 2} ∪ Set.Ici 4
  have nsC_add : ∀ a ∈ nsC, ∀ b ∈ nsC, a + b ∈ nsC := by
    intro a ha b hb
    simp only [nsC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ici] at *
    omega
  let nsSub : AddSubmonoid ℕ :=
    { carrier := nsC, zero_mem' := by simp [nsC],
      add_mem' := fun {a b : ℕ} (ha : a ∈ nsC) (hb : b ∈ nsC) => nsC_add a ha b hb }
  have nsSub_carrier : (nsSub : Set ℕ) = nsC := rfl
  have nsSub_compl : (nsC : Set ℕ)ᶜ = {1, 3} := by
    ext n
    simp only [nsC, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_Ici]
    omega
  have hnsF : ((nsSub : Set ℕ)ᶜ).Finite := by
    rw [nsSub_carrier, nsSub_compl]
    exact Set.toFinite _
  let nsS : NumericalSemigroup := { toAddSubmonoid := nsSub, finite_compl := hnsF }
  have nsS_carrier : (nsS.toAddSubmonoid : Set ℕ) = nsC := nsSub_carrier
  have nsS_frob : numerical_semigroup_frobenius_number nsS = 3 := by
    unfold numerical_semigroup_frobenius_number
    rw [nsS_carrier, nsSub_compl]
    norm_num
  have nsS_genus : numerical_semigroup_genus nsS = 2 := by
    unfold numerical_semigroup_genus
    rw [nsS_carrier, nsSub_compl]
    simp
  have nsS_mult : numerical_semigroup_multiplicity nsS = 2 := by
    unfold numerical_semigroup_multiplicity
    rw [nsS_carrier]
    have hmem : (2:ℕ) ∈ {x : ℕ | x ∈ nsC ∧ 0 < x} := by simp [nsC]
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · apply le_csInf ⟨2, hmem⟩
      intro b hb
      simp only [Set.mem_setOf_eq, nsC, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_Ici] at hb
      omega
  have uniq : ∀ S : NumericalSemigroup, numerical_semigroup_frobenius_number S = 3 →
      numerical_semigroup_multiplicity S = 2 → numerical_semigroup_genus S = 2 → S = nsS := by
    intro S hfrob hmult hgen
    set C : Set ℕ := (S.toAddSubmonoid : Set ℕ)ᶜ with hC
    have h3C : 3 ∈ C := by
      rw [hC]
      exact frob_mem_compl S 3 hfrob (by norm_num)
    have hupper : ∀ n ∈ C, n ≤ 3 := by
      intro n hn
      rw [hC] at hn
      exact compl_le_frob S 3 hfrob n hn
    have h0S : (0:ℕ) ∈ (S.toAddSubmonoid : Set ℕ) := S.toAddSubmonoid.zero_mem
    have h2S : (2:ℕ) ∈ (S.toAddSubmonoid : Set ℕ) := mult_mem S 2 hmult (by norm_num)
    have hsub : C ⊆ {1, 3} := by
      intro n hn
      have hn3 : n ≤ 3 := hupper n hn
      rw [hC] at hn
      have hn0 : n ≠ 0 := fun h => hn (h ▸ h0S)
      have hn2 : n ≠ 2 := fun h => hn (h ▸ h2S)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have h1C : 1 ∈ C := by
      by_contra h1
      have hsub3 : C ⊆ ({3} : Set ℕ) := by
        intro n hn
        have h := hsub hn
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        rcases h with h | h
        · rw [h] at hn; exact absurd hn h1
        · exact h
      have hle : C.ncard ≤ ({3} : Set ℕ).ncard := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      rw [Set.ncard_singleton] at hle
      have hgen' : C.ncard = 2 := by
        rw [hC]
        exact hgen
      omega
    have hCeq : C = {1, 3} := by
      apply Set.Subset.antisymm hsub
      intro n hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl
      · exact h1C
      · exact h3C
    have hcarrier : (S.toAddSubmonoid : Set ℕ) = nsC := by
      ext n
      constructor
      · intro hn
        have hnotC : n ∉ C := by
          rw [hC]
          intro hmem
          exact hmem hn
        rw [hCeq] at hnotC
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotC
        simp only [nsC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Ici]
        omega
      · intro hn
        by_contra hns
        have hmem : n ∈ C := by rw [hC]; exact hns
        rw [hCeq] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        simp only [nsC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_Ici] at hn
        omega
    have hsubeq : S.toAddSubmonoid = nsSub := by
      apply AddSubmonoid.ext
      intro n
      change n ∈ (S.toAddSubmonoid : Set ℕ) ↔ n ∈ (nsC : Set ℕ)
      rw [hcarrier]
    have hnsS : nsS = ⟨nsSub, hnsF⟩ := rfl
    rw [hnsS]
    obtain ⟨a, b⟩ := S
    simp only [NumericalSemigroup.mk.injEq]
    exact hsubeq
  have hX : {S : NumericalSemigroup | numerical_semigroup_frobenius_number S = 3 ∧
      numerical_semigroup_multiplicity S = 2 ∧ numerical_semigroup_genus S = 2} = {nsS} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, b, c⟩
      exact uniq S a b c
    · rintro rfl
      exact ⟨nsS_frob, nsS_mult, nsS_genus⟩
  have hcount3 : numerical_semigroup_count 3 2 2 = 1 := by
    unfold numerical_semigroup_count
    rw [hX, Set.ncard_singleton]
  have count_one_zero : ∀ g : ℕ, numerical_semigroup_count 1 1 g = 0 := by
    intro g
    unfold numerical_semigroup_count
    have hempty : {S : NumericalSemigroup | numerical_semigroup_frobenius_number S = 1 ∧
        numerical_semigroup_multiplicity S = 1 ∧ numerical_semigroup_genus S = g} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨S, hfrob, hmult, -⟩
      have h1mem : (1:ℕ) ∈ (S.toAddSubmonoid : Set ℕ) := mult_mem S 1 hmult (by norm_num)
      have h1compl : (1:ℕ) ∈ (S.toAddSubmonoid : Set ℕ)ᶜ :=
        frob_mem_compl S 1 hfrob (by norm_num)
      exact h1compl h1mem
    rw [hempty]
    simp
  have h1 := hcontra 3 2 2 (by norm_num) (by norm_num)
  rw [hcount3] at h1
  have h1' : (1:ℕ) = numerical_semigroup_count 1 1 1 + numerical_semigroup_count 1 1 0 := h1
  rw [count_one_zero 1, count_one_zero 0] at h1'
  omega
