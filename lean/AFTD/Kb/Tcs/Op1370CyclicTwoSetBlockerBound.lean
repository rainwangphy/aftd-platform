import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.F

/-!
# op1370_cyclic_two_set_blocker_bound

Topic: combinatorics   Node: 619e7b259c4f

Provenance: original. Related work: A cyclic complementary-pair case of Conjecture 4.3 in arXiv:2611.12199; no uncomplementedness is assumed.

Let n be at least four, and let three families of subsets of Fin n be mutually strongly incomparable. Choose four distinct coordinates x, a, b, c. Suppose the first family contains {x,a} and the complement of {x,c}, the second contains {x,b} and the complement of {x,a}, and the third contains {x,c} and the complement of {x,b}. Then the total number of sets is at most 3 times 2^(n-3). No uncomplementedness is assumed.
-/

set_option maxHeartbeats 4000000

private lemma op1370_cyclic_two_set_blocker_bound_trace0 (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
  (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h1 : ({x,b} : Finset (Fin n)) ∈ 𝒜 1 ∧ ({x,a} : Finset (Fin n))ᶜ ∈ 𝒜 1)
  (h2 : ({x,c} : Finset (Fin n)) ∈ 𝒜 2 ∧ ({x,b} : Finset (Fin n))ᶜ ∈ 𝒜 2)
  (A : Finset (Fin n)) (hA : A ∈ 𝒜 0) :
  A ∩ ({x,a,b,c} : Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}} : Finset (Finset (Fin n))) := by
  classical
  have hU1 : ¬ (({x,b} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 1 0 (by decide) {x,b} h1.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU2 : ¬ (({x,c} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 2 0 (by decide) {x,c} h2.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU3 : ¬ (A ∩ {x,a,b,c} ⊆ ({b,c} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,a} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxa
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxa ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hybc : y ∈ ({b,c} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxa hybc
      rcases hyxa with h1 | h1 <;> rcases hybc with h2 | h2
      · exact hxb (h1.symm.trans h2)
      · exact hxc (h1.symm.trans h2)
      · exact hab (h1.symm.trans h2)
      · exact hac (h1.symm.trans h2)
    exact hinc 0 1 (by decide) A hA ({x,a}ᶜ) h1.2 hAc
  have hU4 : ¬ (A ∩ {x,a,b,c} ⊆ ({a,c} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,b} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxb
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxb ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hyac : y ∈ ({a,c} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxb hyac
      rcases hyxb with h1 | h1 <;> rcases hyac with h2 | h2
      · exact hxa (h1.symm.trans h2)
      · exact hxc (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
      · exact hbc (h1.symm.trans h2)
    exact hinc 0 2 (by decide) A hA ({x,b}ᶜ) h2.2 hAc
  have hTsub : A ∩ {x,a,b,c} ⊆ ({x,a,b,c} : Finset (Fin n)) := Finset.inter_subset_right
  have key : (A ∩ {x,a,b,c} = {x,a}) ∨ (A ∩ {x,a,b,c} = {a,b}) ∨ (A ∩ {x,a,b,c} = {a,b,c}) ∨ (A ∩ {x,a,b,c} = {x}) := by
    by_cases hx : x ∈ A ∩ {x,a,b,c}
    · have hbt : b ∉ A ∩ {x,a,b,c} := by
        intro hb
        exact hU1 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact hb)
      have hct : c ∉ A ∩ {x,a,b,c} := by
        intro hc
        exact hU2 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact hc)
      have hTsub2 : A ∩ {x,a,b,c} ⊆ ({x,a} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · left; exact h
        · right; exact h
        · exact absurd (h ▸ hy) hbt
        · exact absurd (h ▸ hy) hct
      by_cases ha : a ∈ A ∩ {x,a,b,c}
      · left
        refine Finset.Subset.antisymm hTsub2 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with h | h
        · rw [h]; exact hx
        · rw [h]; exact ha
      · right; right; right
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub2 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h
          · exact h
          · exact absurd (h ▸ hy) ha
        · intro y hy
          simp only [Finset.mem_singleton] at hy
          rw [hy]; exact hx
    · have haT : a ∈ A ∩ {x,a,b,c} := by
        by_contra haT
        apply hU3
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · exact absurd (h ▸ hy) haT
        · left; exact h
        · right; exact h
      have hbT : b ∈ A ∩ {x,a,b,c} := by
        by_contra hbT
        apply hU4
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · exact absurd (h ▸ hy) hbT
        · right; exact h
      have hTsub3 : A ∩ {x,a,b,c} ⊆ ({a,b,c} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · right; left; exact h
        · right; right; exact h
      by_cases hcT : c ∈ A ∩ {x,a,b,c}
      · right; right; left
        refine Finset.Subset.antisymm hTsub3 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        rcases hy with h | h | h
        · rw [h]; exact haT
        · rw [h]; exact hbT
        · rw [h]; exact hcT
      · right; left
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub3 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h | h
          · left; exact h
          · right; exact h
          · exact absurd (h ▸ hy) hcT
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with h | h
          · rw [h]; exact haT
          · rw [h]; exact hbT
  rcases key with h | h | h | h <;> rw [h] <;> simp

private lemma op1370_cyclic_two_set_blocker_bound_trace1 (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
  (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h0 : ({x,a} : Finset (Fin n)) ∈ 𝒜 0 ∧ ({x,c} : Finset (Fin n))ᶜ ∈ 𝒜 0)
  (h2 : ({x,c} : Finset (Fin n)) ∈ 𝒜 2 ∧ ({x,b} : Finset (Fin n))ᶜ ∈ 𝒜 2)
  (A : Finset (Fin n)) (hA : A ∈ 𝒜 1) :
  A ∩ ({x,a,b,c} : Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}} : Finset (Finset (Fin n))) := by
  classical
  have hU1 : ¬ (({x,a} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 0 1 (by decide) {x,a} h0.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU2 : ¬ (({x,c} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 2 1 (by decide) {x,c} h2.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU3 : ¬ (A ∩ {x,a,b,c} ⊆ ({a,b} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,c} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxc
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxc ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hyab : y ∈ ({a,b} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxc hyab
      rcases hyxc with h1 | h1 <;> rcases hyab with h2 | h2
      · exact hxa (h1.symm.trans h2)
      · exact hxb (h1.symm.trans h2)
      · exact hac (h2.symm.trans h1)
      · exact hbc (h2.symm.trans h1)
    exact hinc 1 0 (by decide) A hA ({x,c}ᶜ) h0.2 hAc
  have hU4 : ¬ (A ∩ {x,a,b,c} ⊆ ({a,c} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,b} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxb
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxb ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hyac : y ∈ ({a,c} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxb hyac
      rcases hyxb with h1 | h1 <;> rcases hyac with h2 | h2
      · exact hxa (h1.symm.trans h2)
      · exact hxc (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
      · exact hbc (h1.symm.trans h2)
    exact hinc 1 2 (by decide) A hA ({x,b}ᶜ) h2.2 hAc
  have hTsub : A ∩ {x,a,b,c} ⊆ ({x,a,b,c} : Finset (Fin n)) := Finset.inter_subset_right
  have key : (A ∩ {x,a,b,c} = {x,b}) ∨ (A ∩ {x,a,b,c} = {b,c}) ∨ (A ∩ {x,a,b,c} = {a,b,c}) ∨ (A ∩ {x,a,b,c} = {x}) := by
    by_cases hx : x ∈ A ∩ {x,a,b,c}
    · have hat : a ∉ A ∩ {x,a,b,c} := by
        intro ha
        exact hU1 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact ha)
      have hct : c ∉ A ∩ {x,a,b,c} := by
        intro hc
        exact hU2 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact hc)
      have hTsub2 : A ∩ {x,a,b,c} ⊆ ({x,b} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · left; exact h
        · exact absurd (h ▸ hy) hat
        · right; exact h
        · exact absurd (h ▸ hy) hct
      by_cases hb : b ∈ A ∩ {x,a,b,c}
      · left
        refine Finset.Subset.antisymm hTsub2 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with h | h
        · rw [h]; exact hx
        · rw [h]; exact hb
      · right; right; right
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub2 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h
          · exact h
          · exact absurd (h ▸ hy) hb
        · intro y hy
          simp only [Finset.mem_singleton] at hy
          rw [hy]; exact hx
    · have hcT : c ∈ A ∩ {x,a,b,c} := by
        by_contra hcT
        apply hU3
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · right; exact h
        · exact absurd (h ▸ hy) hcT
      have hbT : b ∈ A ∩ {x,a,b,c} := by
        by_contra hbT
        apply hU4
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · exact absurd (h ▸ hy) hbT
        · right; exact h
      have hTsub3 : A ∩ {x,a,b,c} ⊆ ({a,b,c} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · right; left; exact h
        · right; right; exact h
      by_cases haT : a ∈ A ∩ {x,a,b,c}
      · right; right; left
        refine Finset.Subset.antisymm hTsub3 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        rcases hy with h | h | h
        · rw [h]; exact haT
        · rw [h]; exact hbT
        · rw [h]; exact hcT
      · right; left
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub3 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h | h
          · exact absurd (h ▸ hy) haT
          · left; exact h
          · right; exact h
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with h | h
          · rw [h]; exact hbT
          · rw [h]; exact hcT
  rcases key with h | h | h | h <;> rw [h] <;> simp

private lemma op1370_cyclic_two_set_blocker_bound_trace2 (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
  (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h0 : ({x,a} : Finset (Fin n)) ∈ 𝒜 0 ∧ ({x,c} : Finset (Fin n))ᶜ ∈ 𝒜 0)
  (h1 : ({x,b} : Finset (Fin n)) ∈ 𝒜 1 ∧ ({x,a} : Finset (Fin n))ᶜ ∈ 𝒜 1)
  (A : Finset (Fin n)) (hA : A ∈ 𝒜 2) :
  A ∩ ({x,a,b,c} : Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}} : Finset (Finset (Fin n))) := by
  classical
  have hU1 : ¬ (({x,a} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 0 2 (by decide) {x,a} h0.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU2 : ¬ (({x,b} : Finset (Fin n)) ⊆ A ∩ {x,a,b,c}) := fun hsub =>
    hinc 1 2 (by decide) {x,b} h1.1 A hA (hsub.trans Finset.inter_subset_left)
  have hU3 : ¬ (A ∩ {x,a,b,c} ⊆ ({a,b} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,c} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxc
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxc ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hyab : y ∈ ({a,b} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxc hyab
      rcases hyxc with h1 | h1 <;> rcases hyab with h2 | h2
      · exact hxa (h1.symm.trans h2)
      · exact hxb (h1.symm.trans h2)
      · exact hac (h2.symm.trans h1)
      · exact hbc (h2.symm.trans h1)
    exact hinc 2 0 (by decide) A hA ({x,c}ᶜ) h0.2 hAc
  have hU4 : ¬ (A ∩ {x,a,b,c} ⊆ ({b,c} : Finset (Fin n))) := by
    intro hsub
    have hAc : A ⊆ ({x,a} : Finset (Fin n))ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyxa
      have hyC : y ∈ ({x,a,b,c} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyxa ⊢
        tauto
      have hy' : y ∈ A ∩ {x,a,b,c} := Finset.mem_inter.mpr ⟨hy, hyC⟩
      have hybc : y ∈ ({b,c} : Finset (Fin n)) := hsub hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyxa hybc
      rcases hyxa with h1 | h1 <;> rcases hybc with h2 | h2
      · exact hxb (h1.symm.trans h2)
      · exact hxc (h1.symm.trans h2)
      · exact hab (h1.symm.trans h2)
      · exact hac (h1.symm.trans h2)
    exact hinc 2 1 (by decide) A hA ({x,a}ᶜ) h1.2 hAc
  have hTsub : A ∩ {x,a,b,c} ⊆ ({x,a,b,c} : Finset (Fin n)) := Finset.inter_subset_right
  have key : (A ∩ {x,a,b,c} = {x,c}) ∨ (A ∩ {x,a,b,c} = {a,c}) ∨ (A ∩ {x,a,b,c} = {a,b,c}) ∨ (A ∩ {x,a,b,c} = {x}) := by
    by_cases hx : x ∈ A ∩ {x,a,b,c}
    · have hat : a ∉ A ∩ {x,a,b,c} := by
        intro ha
        exact hU1 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact ha)
      have hbt : b ∉ A ∩ {x,a,b,c} := by
        intro hb
        exact hU2 (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl
          · exact hx
          · exact hb)
      have hTsub2 : A ∩ {x,a,b,c} ⊆ ({x,c} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · left; exact h
        · exact absurd (h ▸ hy) hat
        · exact absurd (h ▸ hy) hbt
        · right; exact h
      by_cases hc : c ∈ A ∩ {x,a,b,c}
      · left
        refine Finset.Subset.antisymm hTsub2 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with h | h
        · rw [h]; exact hx
        · rw [h]; exact hc
      · right; right; right
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub2 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h
          · exact h
          · exact absurd (h ▸ hy) hc
        · intro y hy
          simp only [Finset.mem_singleton] at hy
          rw [hy]; exact hx
    · have hcT : c ∈ A ∩ {x,a,b,c} := by
        by_contra hcT
        apply hU3
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · right; exact h
        · exact absurd (h ▸ hy) hcT
      have haT : a ∈ A ∩ {x,a,b,c} := by
        by_contra haT
        apply hU4
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · exact absurd (h ▸ hy) haT
        · left; exact h
        · right; exact h
      have hTsub3 : A ∩ {x,a,b,c} ⊆ ({a,b,c} : Finset (Fin n)) := by
        intro y hy
        have hyC := hTsub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyC ⊢
        rcases hyC with h | h | h | h
        · exact absurd (h ▸ hy) hx
        · left; exact h
        · right; left; exact h
        · right; right; exact h
      by_cases hbT : b ∈ A ∩ {x,a,b,c}
      · right; right; left
        refine Finset.Subset.antisymm hTsub3 ?_
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        rcases hy with h | h | h
        · rw [h]; exact haT
        · rw [h]; exact hbT
        · rw [h]; exact hcT
      · right; left
        refine Finset.Subset.antisymm ?_ ?_
        · intro y hy
          have h2 := hTsub3 hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at h2 ⊢
          rcases h2 with h | h | h
          · left; exact h
          · exact absurd (h ▸ hy) hbT
          · right; exact h
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with h | h
          · rw [h]; exact haT
          · rw [h]; exact hcT
  rcases key with h | h | h | h <;> rw [h] <;> simp

private lemma op1370_cyclic_two_set_blocker_bound_nxbG0 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({x,b}:Finset (Fin n)) ∉ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : b ∈ ({x,a}:Finset (Fin n)) := by
      have ht : b ∈ ({x,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxb h' | exact hxb h'.symm | exact hab h' | exact hab h'.symm
  · have hm : x ∈ ({a,b}:Finset (Fin n)) := by
      have ht : x ∈ ({x,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h' | exact hxa h'.symm | exact hxb h' | exact hxb h'.symm
  · have hm : x ∈ ({a,b,c}:Finset (Fin n)) := by
      have ht : x ∈ ({x,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h'|h' <;> first | exact hxa h' | exact hxa h'.symm | exact hxb h' | exact hxb h'.symm | exact hxc h' | exact hxc h'.symm
  · have hm : b ∈ ({x}:Finset (Fin n)) := by
      have ht : b ∈ ({x,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxb hm | exact hxb hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_nxaG1 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({x,a}:Finset (Fin n)) ∉ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : a ∈ ({x,b}:Finset (Fin n)) := by
      have ht : a ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h'.symm | exact hxa h' | exact hab h'.symm | exact hab h'
  · have hm : x ∈ ({b,c}:Finset (Fin n)) := by
      have ht : x ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxb h' | exact hxb h'.symm | exact hxc h' | exact hxc h'.symm
  · have hm : x ∈ ({a,b,c}:Finset (Fin n)) := by
      have ht : x ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h'|h' <;> first | exact hxa h' | exact hxa h'.symm | exact hxb h' | exact hxb h'.symm | exact hxc h' | exact hxc h'.symm
  · have hm : a ∈ ({x}:Finset (Fin n)) := by
      have ht : a ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxa hm | exact hxa hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_nxaG2 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({x,a}:Finset (Fin n)) ∉ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : a ∈ ({x,c}:Finset (Fin n)) := by
      have ht : a ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h'.symm | exact hxa h' | exact hac h' | exact hac h'.symm
  · have hm : x ∈ ({a,c}:Finset (Fin n)) := by
      have ht : x ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h' | exact hxa h'.symm | exact hxc h' | exact hxc h'.symm
  · have hm : x ∈ ({a,b,c}:Finset (Fin n)) := by
      have ht : x ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h'|h' <;> first | exact hxa h' | exact hxa h'.symm | exact hxb h' | exact hxb h'.symm | exact hxc h' | exact hxc h'.symm
  · have hm : a ∈ ({x}:Finset (Fin n)) := by
      have ht : a ∈ ({x,a}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxa hm | exact hxa hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_nbcG0 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({b,c}:Finset (Fin n)) ∉ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : b ∈ ({x,a}:Finset (Fin n)) := by
      have ht : b ∈ ({b,c}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxb h' | exact hxb h'.symm | exact hab h' | exact hab h'.symm
  · have hm : c ∈ ({a,b}:Finset (Fin n)) := by
      have ht : c ∈ ({b,c}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hac h'.symm | exact hac h' | exact hbc h'.symm | exact hbc h'
  · have hm : a ∈ ({b,c}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b,c}:Finset (Fin n)) := by simp
      rwa [← h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hab h' | exact hab h'.symm | exact hac h' | exact hac h'.symm
  · have hm : b ∈ ({x}:Finset (Fin n)) := by
      have ht : b ∈ ({b,c}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxb hm | exact hxb hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_nabG1 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a,b}:Finset (Fin n)) ∉ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : a ∈ ({x,b}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h'.symm | exact hxa h' | exact hab h' | exact hab h'.symm
  · have hm : a ∈ ({b,c}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hab h' | exact hab h'.symm | exact hac h' | exact hac h'.symm
  · have hm : c ∈ ({a,b}:Finset (Fin n)) := by
      have ht : c ∈ ({a,b,c}:Finset (Fin n)) := by simp
      rwa [← h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hac h'.symm | exact hac h' | exact hbc h'.symm | exact hbc h'
  · have hm : a ∈ ({x}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxa hm | exact hxa hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_nabG2 (n : ℕ) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a,b}:Finset (Fin n)) ∉ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h|h|h|h)
  · have hm : a ∈ ({x,c}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hxa h'.symm | exact hxa h' | exact hac h' | exact hac h'.symm
  · have hm : b ∈ ({a,c}:Finset (Fin n)) := by
      have ht : b ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hab h'.symm | exact hab h' | exact hbc h' | exact hbc h'.symm
  · have hm : c ∈ ({a,b}:Finset (Fin n)) := by
      have ht : c ∈ ({a,b,c}:Finset (Fin n)) := by simp
      rwa [← h] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h'|h' <;> first | exact hac h'.symm | exact hac h' | exact hbc h'.symm | exact hbc h'
  · have hm : a ∈ ({x}:Finset (Fin n)) := by
      have ht : a ∈ ({a,b}:Finset (Fin n)) := by simp
      rwa [h] at ht
    simp only [Finset.mem_singleton] at hm
    first | exact hxa hm | exact hxa hm.symm

private lemma op1370_cyclic_two_set_blocker_bound_sliceX (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n)))
    (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hinc : strongly_incomparable 𝒜)
    (trace0 : ∀ A ∈ 𝒜 0, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace1 : ∀ A ∈ 𝒜 1, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace2 : ∀ A ∈ 𝒜 2, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nxbG0 : ({x,b}:Finset (Fin n)) ∉ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nxaG1 : ({x,a}:Finset (Fin n)) ∉ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nxaG2 : ({x,a}:Finset (Fin n)) ∉ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (W : Finset (Fin n)) (hWC : W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ) :
    (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{x,b},{x,c},{x}}:Finset (Finset (Fin n))))
      (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))).card ≤ 3 := by
  classical
  let F1 : Finset (Finset (Fin n)) := Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{x,b},{x,c},{x}}:Finset (Finset (Fin n)))) (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))
  change F1.card ≤ 3
  have interU : ∀ S : Finset (Fin n), S ⊆ ({x,a,b,c}:Finset (Fin n)) →
      (W ∪ S) ∩ ({x,a,b,c}:Finset (Fin n)) = S := by
    intro S hSC
    ext y
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hyW | hyS, hyC⟩
      · exact absurd hyC (Finset.mem_compl.mp (hWC hyW))
      · exact hyS
    · intro hyS; exact ⟨Or.inr hyS, hSC hyS⟩
  have htrA : (W ∪ {x,a} : Finset (Fin n)) ∩ ({x,a,b,c}:Finset (Fin n)) = {x,a} :=
    interU {x,a} (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)
  have htrB : (W ∪ {x,b} : Finset (Fin n)) ∩ ({x,a,b,c}:Finset (Fin n)) = {x,b} :=
    interU {x,b} (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)
  have hsubPA : (W ∪ {x} : Finset (Fin n)) ⊆ (W ∪ {x,a} : Finset (Fin n)) := by
    intro y hy; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  have hsubPB : (W ∪ {x} : Finset (Fin n)) ⊆ (W ∪ {x,b} : Finset (Fin n)) := by
    intro y hy; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  by_contra hle
  push_neg at hle
  let K : Finset (Finset (Fin n)) := {W ∪ {x}, W ∪ {x,a}, W ∪ {x,b}, W ∪ {x,c}}
  have hFK : F1 ⊆ K := by
    intro A hA
    simp only [F1, Finset.mem_filter] at hA
    obtain ⟨⟨hAU, hAW⟩, htGX⟩ := hA
    have hAeq : A = W ∪ (A ∩ ({x,a,b,c}:Finset (Fin n))) := by
      have := Finset.sdiff_union_inter A ({x,a,b,c}:Finset (Fin n))
      rw [Finset.sdiff_eq_inter_compl, hAW] at this
      exact this.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at htGX
    rw [hAeq]
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at htGX ⊢
    rcases htGX with h|h|h|h
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; rw [h]
    · left; rw [h]
  have hKcard : K.card ≤ 4 := by
    have h1 := Finset.card_insert_le (W ∪ {x} : Finset (Fin n)) (insert (W ∪ {x,a} : Finset (Fin n)) (insert (W ∪ {x,b} : Finset (Fin n)) ({(W ∪ {x,c} : Finset (Fin n))} : Finset (Finset (Fin n)))))
    have h2 := Finset.card_insert_le (W ∪ {x,a} : Finset (Fin n)) (insert (W ∪ {x,b} : Finset (Fin n)) ({(W ∪ {x,c} : Finset (Fin n))} : Finset (Finset (Fin n))))
    have h3 := Finset.card_insert_le (W ∪ {x,b} : Finset (Fin n)) ({(W ∪ {x,c} : Finset (Fin n))} : Finset (Finset (Fin n)))
    rw [Finset.card_singleton] at h3
    change ({W ∪ {x}, W ∪ {x,a}, W ∪ {x,b}, W ∪ {x,c}} : Finset (Finset (Fin n))).card ≤ 4
    omega
  have hcardge : 4 ≤ F1.card := by omega
  have hFKle : F1.card ≤ K.card := Finset.card_le_card hFK
  have hKle : K.card ≤ F1.card := by omega
  have hKF : F1 = K := Finset.eq_of_subset_of_card_le hFK hKle
  have inU : ∀ X, X ∈ F1 → X ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 := by
    intro X hX
    simp only [F1, Finset.mem_filter] at hX
    exact hX.1.1
  have hP0U : (W ∪ {x} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K])
  have hPAU : (W ∪ {x,a} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K])
  have hPBU : (W ∪ {x,b} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K])
  simp only [Finset.mem_union] at hP0U hPAU hPBU
  rcases hP0U with hP0_01 | hP0_2
  · rcases hP0_01 with hP0_0 | hP0_1
    · have hPB0 : (W ∪ {x,b} : Finset (Fin n)) ∈ 𝒜 0 := by
        rcases hPBU with h01 | h2'
        · rcases h01 with h0 | h1
          · exact h0
          · exact absurd hsubPB (hinc 0 1 (by decide) (W ∪ {x}) hP0_0 (W ∪ {x,b}) h1)
        · exact absurd hsubPB (hinc 0 2 (by decide) (W ∪ {x}) hP0_0 (W ∪ {x,b}) h2')
      have hmem : ({x,b}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
        have htr := trace0 (W ∪ {x,b}) hPB0
        rw [htrB] at htr; exact htr
      exact nxbG0 hmem
    · have hPA1 : (W ∪ {x,a} : Finset (Fin n)) ∈ 𝒜 1 := by
        rcases hPAU with h01 | h2'
        · rcases h01 with h0 | h1
          · exact absurd hsubPA (hinc 1 0 (by decide) (W ∪ {x}) hP0_1 (W ∪ {x,a}) h0)
          · exact h1
        · exact absurd hsubPA (hinc 1 2 (by decide) (W ∪ {x}) hP0_1 (W ∪ {x,a}) h2')
      have hmem : ({x,a}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
        have htr := trace1 (W ∪ {x,a}) hPA1
        rw [htrA] at htr; exact htr
      exact nxaG1 hmem
  · have hPA2 : (W ∪ {x,a} : Finset (Fin n)) ∈ 𝒜 2 := by
      rcases hPAU with h01 | h2'
      · rcases h01 with h0 | h1
        · exact absurd hsubPA (hinc 2 0 (by decide) (W ∪ {x}) hP0_2 (W ∪ {x,a}) h0)
        · exact absurd hsubPA (hinc 2 1 (by decide) (W ∪ {x}) hP0_2 (W ∪ {x,a}) h1)
      · exact h2'
    have hmem : ({x,a}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
      have htr := trace2 (W ∪ {x,a}) hPA2
      rw [htrA] at htr; exact htr
    exact nxaG2 hmem

private lemma op1370_cyclic_two_set_blocker_bound_sliceH (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n)))
    (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hinc : strongly_incomparable 𝒜)
    (trace0 : ∀ A ∈ 𝒜 0, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace1 : ∀ A ∈ 𝒜 1, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace2 : ∀ A ∈ 𝒜 2, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nbcG0 : ({b,c}:Finset (Fin n)) ∉ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nabG1 : ({a,b}:Finset (Fin n)) ∉ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (nabG2 : ({a,b}:Finset (Fin n)) ∉ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (W : Finset (Fin n)) (hWC : W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ) :
    (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{a,b},{b,c},{a,c},{a,b,c}}:Finset (Finset (Fin n))))
      (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))).card ≤ 3 := by
  classical
  let F2 : Finset (Finset (Fin n)) := Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{a,b},{b,c},{a,c},{a,b,c}}:Finset (Finset (Fin n)))) (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))
  change F2.card ≤ 3
  have interU : ∀ S : Finset (Fin n), S ⊆ ({x,a,b,c}:Finset (Fin n)) →
      (W ∪ S) ∩ ({x,a,b,c}:Finset (Fin n)) = S := by
    intro S hSC
    ext y
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hyW | hyS, hyC⟩
      · exact absurd hyC (Finset.mem_compl.mp (hWC hyW))
      · exact hyS
    · intro hyS; exact ⟨Or.inr hyS, hSC hyS⟩
  have htrAB : (W ∪ {a,b} : Finset (Fin n)) ∩ ({x,a,b,c}:Finset (Fin n)) = {a,b} :=
    interU {a,b} (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)
  have htrBC : (W ∪ {b,c} : Finset (Fin n)) ∩ ({x,a,b,c}:Finset (Fin n)) = {b,c} :=
    interU {b,c} (by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)
  have hsubAB : (W ∪ {a,b} : Finset (Fin n)) ⊆ (W ∪ {a,b,c} : Finset (Fin n)) := by
    intro y hy; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  have hsubBC : (W ∪ {b,c} : Finset (Fin n)) ⊆ (W ∪ {a,b,c} : Finset (Fin n)) := by
    intro y hy; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  by_contra hle
  push_neg at hle
  let K2 : Finset (Finset (Fin n)) := {W ∪ {a,b}, W ∪ {b,c}, W ∪ {a,c}, W ∪ {a,b,c}}
  have hFK : F2 ⊆ K2 := by
    intro A hA
    simp only [F2, Finset.mem_filter] at hA
    obtain ⟨⟨hAU, hAW⟩, htGH⟩ := hA
    have hAeq : A = W ∪ (A ∩ ({x,a,b,c}:Finset (Fin n))) := by
      have := Finset.sdiff_union_inter A ({x,a,b,c}:Finset (Fin n))
      rw [Finset.sdiff_eq_inter_compl, hAW] at this
      exact this.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at htGH
    rw [hAeq]
    simp only [K2, Finset.mem_insert, Finset.mem_singleton] at htGH ⊢
    rcases htGH with h|h|h|h
    · left; rw [h]
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; rw [h]
  have hKcard : K2.card ≤ 4 := by
    have h1 := Finset.card_insert_le (W ∪ {a,b} : Finset (Fin n)) (insert (W ∪ {b,c} : Finset (Fin n)) (insert (W ∪ {a,c} : Finset (Fin n)) ({(W ∪ {a,b,c} : Finset (Fin n))} : Finset (Finset (Fin n)))))
    have h2 := Finset.card_insert_le (W ∪ {b,c} : Finset (Fin n)) (insert (W ∪ {a,c} : Finset (Fin n)) ({(W ∪ {a,b,c} : Finset (Fin n))} : Finset (Finset (Fin n))))
    have h3 := Finset.card_insert_le (W ∪ {a,c} : Finset (Fin n)) ({(W ∪ {a,b,c} : Finset (Fin n))} : Finset (Finset (Fin n)))
    rw [Finset.card_singleton] at h3
    change ({W ∪ {a,b}, W ∪ {b,c}, W ∪ {a,c}, W ∪ {a,b,c}} : Finset (Finset (Fin n))).card ≤ 4
    omega
  have hcardge : 4 ≤ F2.card := by omega
  have hFKle : F2.card ≤ K2.card := Finset.card_le_card hFK
  have hKle : K2.card ≤ F2.card := by omega
  have hKF : F2 = K2 := Finset.eq_of_subset_of_card_le hFK hKle
  have inU : ∀ X, X ∈ F2 → X ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 := by
    intro X hX
    simp only [F2, Finset.mem_filter] at hX
    exact hX.1.1
  have hYHU : (W ∪ {a,b,c} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K2])
  have hYabU : (W ∪ {a,b} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K2])
  have hYbcU : (W ∪ {b,c} : Finset (Fin n)) ∈ 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 :=
    inU _ (by rw [hKF]; simp [K2])
  simp only [Finset.mem_union] at hYHU hYabU hYbcU
  rcases hYHU with hYH_01 | hYH_2
  · rcases hYH_01 with hYH_0 | hYH_1
    · have hYbc0 : (W ∪ {b,c} : Finset (Fin n)) ∈ 𝒜 0 := by
        rcases hYbcU with h01 | h2'
        · rcases h01 with h0 | h1
          · exact h0
          · exact absurd hsubBC (hinc 1 0 (by decide) (W ∪ {b,c}) h1 (W ∪ {a,b,c}) hYH_0)
        · exact absurd hsubBC (hinc 2 0 (by decide) (W ∪ {b,c}) h2' (W ∪ {a,b,c}) hYH_0)
      have hmem : ({b,c}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
        have htr := trace0 (W ∪ {b,c}) hYbc0
        rw [htrBC] at htr; exact htr
      exact nbcG0 hmem
    · have hYab1 : (W ∪ {a,b} : Finset (Fin n)) ∈ 𝒜 1 := by
        rcases hYabU with h01 | h2'
        · rcases h01 with h0 | h1
          · exact absurd hsubAB (hinc 0 1 (by decide) (W ∪ {a,b}) h0 (W ∪ {a,b,c}) hYH_1)
          · exact h1
        · exact absurd hsubAB (hinc 2 1 (by decide) (W ∪ {a,b}) h2' (W ∪ {a,b,c}) hYH_1)
      have hmem : ({a,b}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
        have htr := trace1 (W ∪ {a,b}) hYab1
        rw [htrAB] at htr; exact htr
      exact nabG1 hmem
  · have hYab2 : (W ∪ {a,b} : Finset (Fin n)) ∈ 𝒜 2 := by
      rcases hYabU with h01 | h2'
      · rcases h01 with h0 | h1
        · exact absurd hsubAB (hinc 0 2 (by decide) (W ∪ {a,b}) h0 (W ∪ {a,b,c}) hYH_2)
        · exact absurd hsubAB (hinc 1 2 (by decide) (W ∪ {a,b}) h1 (W ∪ {a,b,c}) hYH_2)
      · exact h2'
    have hmem : ({a,b}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))) := by
      have htr := trace2 (W ∪ {a,b}) hYab2
      rw [htrAB] at htr; exact htr
    exact nabG2 hmem

private lemma op1370_cyclic_two_set_blocker_bound_fiber (n : ℕ) (𝒜 : Fin 3 → Finset (Finset (Fin n)))
    (x a b c : Fin n)
    (trace0 : ∀ A ∈ 𝒜 0, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace1 : ∀ A ∈ 𝒜 1, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (trace2 : ∀ A ∈ 𝒜 2, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))))
    (sliceXf : ∀ W, W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ →
      (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{x,b},{x,c},{x}}:Finset (Finset (Fin n))))
        (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))).card ≤ 3)
    (sliceHf : ∀ W, W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ →
      (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{a,b},{b,c},{a,c},{a,b,c}}:Finset (Finset (Fin n))))
        (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2))).card ≤ 3) :
    ∀ W ∈ ({x,a,b,c}:Finset (Fin n))ᶜ.powerset,
      (Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2)).card ≤ 6 := by
  classical
  intro W hW
  have hWC : W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ := Finset.mem_powerset.mp hW
  let F : Finset (Finset (Fin n)) := Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2)
  let GX : Finset (Finset (Fin n)) := {{x,a},{x,b},{x,c},{x}}
  let GH : Finset (Finset (Fin n)) := {{a,b},{b,c},{a,c},{a,b,c}}
  change F.card ≤ 6
  have hcover : ∀ A ∈ F, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX ∨ A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GH := by
    intro A hA
    simp only [F, Finset.mem_filter] at hA
    obtain ⟨hAU, hAW⟩ := hA
    simp only [Finset.mem_union] at hAU
    rcases hAU with (hA0 | hA1) | hA2
    · have h := trace0 A hA0
      simp only [GX, GH, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := trace1 A hA1
      simp only [GX, GH, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
    · have h := trace2 A hA2
      simp only [GX, GH, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      tauto
  let F1 : Finset (Finset (Fin n)) := F.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX)
  let F2 : Finset (Finset (Fin n)) := F.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GH)
  have hsplit : F.card = F1.card + (F.filter (fun A => ¬ (A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX))).card := by
    have hthis := Finset.card_filter_add_card_filter_not (s := F) (p := fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX)
    exact hthis.symm
  have hsub12 : F.filter (fun A => ¬ (A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX)) ⊆ F2 := by
    intro A hA
    simp only [Finset.mem_filter] at hA
    obtain ⟨hAF, hAnG⟩ := hA
    simp only [F2, Finset.mem_filter]
    refine ⟨hAF, ?_⟩
    rcases hcover A hAF with h | h
    · exact absurd h hAnG
    · exact h
  have hle2 : (F.filter (fun A => ¬ (A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX))).card ≤ F2.card :=
    Finset.card_le_card hsub12
  have hF1le : F1.card ≤ 3 := by
    rw [show F1 = Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GX) F from rfl]
    rw [show F = Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2) from rfl]
    rw [show GX = ({{x,a},{x,b},{x,c},{x}}:Finset (Finset (Fin n))) from rfl]
    exact sliceXf W hWC
  have hF2le : F2.card ≤ 3 := by
    rw [show F2 = Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ GH) F from rfl]
    rw [show F = Finset.filter (fun A => A ∩ ({x,a,b,c}:Finset (Fin n))ᶜ = W) (𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2) from rfl]
    rw [show GH = ({{a,b},{b,c},{a,c},{a,b,c}}:Finset (Finset (Fin n))) from rfl]
    exact sliceHf W hWC
  omega

theorem op1370_cyclic_two_set_blocker_bound (n : ℕ) (hn : 4 ≤ n) (𝒜 : Fin 3 → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜) (x a b c : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h0 : ({x,a} : Finset (Fin n)) ∈ 𝒜 0 ∧ ({x,c} : Finset (Fin n))ᶜ ∈ 𝒜 0) (h1 : ({x,b} : Finset (Fin n)) ∈ 𝒜 1 ∧ ({x,a} : Finset (Fin n))ᶜ ∈ 𝒜 1) (h2 : ({x,c} : Finset (Fin n)) ∈ 𝒜 2 ∧ ({x,b} : Finset (Fin n))ᶜ ∈ 𝒜 2) : ∑ i, (𝒜 i).card ≤ 3 * 2 ^ (n - 3) := by
  classical
  let C : Finset (Fin n) := {x,a,b,c}
  have hC : C = {x,a,b,c} := rfl
  have hCcard : C.card = 4 := by
    rw [hC]
    have h1' : x ∉ (insert a (insert b ({c}:Finset (Fin n)))) := by simp [hxa, hxb, hxc]
    have h2' : a ∉ (insert b ({c}:Finset (Fin n))) := by simp [hab, hac]
    have h3' : b ∉ ({c}:Finset (Fin n)) := by simp [hbc]
    rw [show ({x,a,b,c} : Finset (Fin n)) = insert x (insert a (insert b {c})) from rfl,
      Finset.card_insert_of_notMem h1', Finset.card_insert_of_notMem h2', Finset.card_insert_of_notMem h3', Finset.card_singleton]
  have hCcomplcard : Cᶜ.card = n - 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hCcard]
  let U : Finset (Finset (Fin n)) := 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2
  have hdisj01 : Disjoint (𝒜 0) (𝒜 1) := by
    rw [Finset.disjoint_left]; intro A hA0 hA1
    exact hinc 0 1 (by decide) A hA0 A hA1 (Finset.Subset.refl A)
  have hdisj02 : Disjoint (𝒜 0) (𝒜 2) := by
    rw [Finset.disjoint_left]; intro A hA0 hA2
    exact hinc 0 2 (by decide) A hA0 A hA2 (Finset.Subset.refl A)
  have hdisj12 : Disjoint (𝒜 1) (𝒜 2) := by
    rw [Finset.disjoint_left]; intro A hA1 hA2
    exact hinc 1 2 (by decide) A hA1 A hA2 (Finset.Subset.refl A)
  have hdisj012 : Disjoint (𝒜 0 ∪ 𝒜 1) (𝒜 2) := by
    rw [Finset.disjoint_left]; intro A hA hA2
    rcases Finset.mem_union.mp hA with hA0 | hA1
    · exact (Finset.disjoint_left.mp hdisj02) hA0 hA2
    · exact (Finset.disjoint_left.mp hdisj12) hA1 hA2
  have hsum : ∑ i, (𝒜 i).card = U.card := by
    rw [Fin.sum_univ_three, show U = 𝒜 0 ∪ 𝒜 1 ∪ 𝒜 2 from rfl,
      Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01]
  rw [hsum]
  have hmap : Set.MapsTo (fun A => A ∩ Cᶜ) (↑U) (↑(Cᶜ).powerset) := by
    intro A hA
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.inter_subset_right
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have trace0' : ∀ A ∈ 𝒜 0, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,a},{a,b},{a,b,c},{x}}:Finset (Finset (Fin n))) :=
    fun A hA => op1370_cyclic_two_set_blocker_bound_trace0 n 𝒜 hinc x a b c hxa hxb hxc hab hac hbc h1 h2 A hA
  have trace1' : ∀ A ∈ 𝒜 1, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,b},{b,c},{a,b,c},{x}}:Finset (Finset (Fin n))) :=
    fun A hA => op1370_cyclic_two_set_blocker_bound_trace1 n 𝒜 hinc x a b c hxa hxb hxc hab hac hbc h0 h2 A hA
  have trace2' : ∀ A ∈ 𝒜 2, A ∩ ({x,a,b,c}:Finset (Fin n)) ∈ ({{x,c},{a,c},{a,b,c},{x}}:Finset (Finset (Fin n))) :=
    fun A hA => op1370_cyclic_two_set_blocker_bound_trace2 n 𝒜 hinc x a b c hxa hxb hxc hab hac hbc h0 h1 A hA
  have sliceX' := fun (W : Finset (Fin n)) (hW : W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ) =>
    op1370_cyclic_two_set_blocker_bound_sliceX n 𝒜 x a b c hxa hxb hxc hab hac hbc hinc trace0' trace1' trace2'
      (op1370_cyclic_two_set_blocker_bound_nxbG0 n x a b c hxa hxb hxc hab hac hbc)
      (op1370_cyclic_two_set_blocker_bound_nxaG1 n x a b c hxa hxb hxc hab hac hbc)
      (op1370_cyclic_two_set_blocker_bound_nxaG2 n x a b c hxa hxb hxc hab hac hbc) W hW
  have sliceH' := fun (W : Finset (Fin n)) (hW : W ⊆ ({x,a,b,c}:Finset (Fin n))ᶜ) =>
    op1370_cyclic_two_set_blocker_bound_sliceH n 𝒜 x a b c hxa hxb hxc hab hac hbc hinc trace0' trace1' trace2'
      (op1370_cyclic_two_set_blocker_bound_nbcG0 n x a b c hxa hxb hxc hab hac hbc)
      (op1370_cyclic_two_set_blocker_bound_nabG1 n x a b c hxa hxb hxc hab hac hbc)
      (op1370_cyclic_two_set_blocker_bound_nabG2 n x a b c hxa hxb hxc hab hac hbc) W hW
  have hfib := op1370_cyclic_two_set_blocker_bound_fiber n 𝒜 x a b c trace0' trace1' trace2' sliceX' sliceH'
  have hfib' : ∀ W ∈ (Cᶜ).powerset, (U.filter (fun A => A ∩ Cᶜ = W)).card ≤ 6 := by
    intro W hW
    exact hfib W hW
  calc
    ∑ W ∈ (Cᶜ).powerset, (U.filter (fun A => A ∩ Cᶜ = W)).card
        ≤ ∑ W ∈ (Cᶜ).powerset, 6 := Finset.sum_le_sum hfib'
    _ = 6 * (Cᶜ).powerset.card := by rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_comm _ _
    _ = 6 * 2 ^ (Cᶜ.card) := by rw [Finset.card_powerset]
    _ = 6 * 2 ^ (n - 4) := by rw [hCcomplcard]
    _ = 3 * 2 ^ (n - 3) := by
          have hk : n - 3 = (n - 4) + 1 := by omega
          rw [hk, Nat.pow_succ]; ring
