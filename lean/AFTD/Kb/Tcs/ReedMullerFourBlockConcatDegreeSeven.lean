import AFTD.Prelude
import AFTD.Kb.Tcs.ReedMullerCode
import AFTD.Kb.Tcs.ReedMullerCodeMono
import AFTD.Kb.Tcs.FourBlockConcat
import AFTD.Kb.Tcs.FourBlockConcatReduced
import AFTD.Kb.Tcs.Monomial

/-!
# reed_muller_four_block_concat_degree_seven

Topic: information   Node: 8a94bf12168e

Provenance: formalization of a published result. Source: arXiv:2610.29807 Lemma 3.1 -- Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

Let g0 and g3 be Boolean functions on Fin 12 in the Reed-Muller code reed_muller_code 5 12, and let g1 and g2 be Boolean functions on Fin 12 in reed_muller_code 6 12. Then their four-block concatenation four_block_concat g0 g1 g2 (g1 + g2 + g3) belongs to the Reed-Muller code reed_muller_code 7 14.
-/

private lemma reed_muller_four_block_concat_degree_seven_zz_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

private lemma reed_muller_four_block_concat_degree_seven_single_not_mem {s : ℕ} (a : Fin s)
    (I : Finset (Fin s)) (ha : a ∉ I) :
    (fun x : Fin s → ZMod 2 => x a) * monomial I = monomial (insert a I) := by
  funext x
  simp [monomial, Finset.prod_insert ha]

private lemma reed_muller_four_block_concat_degree_seven_single_mem {s : ℕ} (a : Fin s)
    (I : Finset (Fin s)) (ha : a ∈ I) :
    (fun x : Fin s → ZMod 2 => x a) * monomial I = monomial I := by
  funext x
  simp only [Pi.mul_apply, monomial]
  rw [← Finset.insert_erase ha, Finset.prod_insert (Finset.notMem_erase a I)]
  rw [← mul_assoc, reed_muller_four_block_concat_degree_seven_zz_mul_self]

private lemma reed_muller_four_block_concat_degree_seven_monomial_mul {s : ℕ} (I J : Finset (Fin s)) :
    (monomial I * monomial J : (Fin s → ZMod 2) → ZMod 2) = monomial (I ∪ J) := by
  induction I using Finset.induction with
  | empty => funext x; simp [monomial]
  | insert a I ha ih =>
    rw [Finset.insert_union, ← reed_muller_four_block_concat_degree_seven_single_not_mem a I ha,
      mul_assoc, ih]
    by_cases haJ : a ∈ J
    · rw [reed_muller_four_block_concat_degree_seven_single_mem a (I ∪ J) (Finset.mem_union_right I haJ),
        Finset.insert_eq_of_mem (Finset.mem_union_right I haJ)]
    · rw [reed_muller_four_block_concat_degree_seven_single_not_mem a (I ∪ J) (by simp [ha, haJ])]

private lemma reed_muller_four_block_concat_degree_seven_monomial_mem {s r : ℕ} (T : Finset (Fin s))
    (hT : T.card ≤ r) : monomial T ∈ reed_muller_code r s :=
  Submodule.subset_span ⟨T, hT, rfl⟩

private lemma reed_muller_four_block_concat_degree_seven_mul_monomial_mem {s r : ℕ}
    (T : Finset (Fin s)) (f : (Fin s → ZMod 2) → ZMod 2) (hf : f ∈ reed_muller_code r s) :
    monomial T * f ∈ reed_muller_code (r + T.card) s := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨U, hU, rfl⟩ := hx
      rw [reed_muller_four_block_concat_degree_seven_monomial_mul]
      refine reed_muller_code_mono ?_ (reed_muller_four_block_concat_degree_seven_monomial_mem _ (le_refl _))
      have := Finset.card_union_le T U
      omega
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [show monomial T * (a • x) = a • (monomial T * x) from by
        funext v; simp [Pi.mul_apply, smul_eq_mul]; ring]
      exact Submodule.smul_mem _ a ih

private lemma reed_muller_four_block_concat_degree_seven_lift_mem {m k r : ℕ}
    {g : (Fin m → ZMod 2) → ZMod 2} (hg : g ∈ reed_muller_code r m) :
    (fun v : Fin (m + k) → ZMod 2 => g (fun i => v (Fin.castAdd k i))) ∈
      reed_muller_code r (m + k) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨U, hU, rfl⟩ := hx
      have heq : (fun v : Fin (m + k) → ZMod 2 => monomial U (fun i => v (Fin.castAdd k i)))
          = monomial (U.image (Fin.castAdd k)) := by
        funext v
        simp only [monomial]
        exact (Finset.prod_image (f := v) (g := Fin.castAdd k)
          (fun x _ y _ h => Fin.castAdd_injective m k h)).symm
      rw [heq]
      exact reed_muller_four_block_concat_degree_seven_monomial_mem _
        (by rw [Finset.card_image_of_injective _ (Fin.castAdd_injective m k)]; exact hU)
  | zero =>
      have h : (fun v : Fin (m + k) → ZMod 2 =>
          (0 : (Fin m → ZMod 2) → ZMod 2) (fun i => v (Fin.castAdd k i))) = 0 := by
        funext v; rfl
      rw [h]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      have h : (fun v : Fin (m + k) → ZMod 2 => (x + y) (fun i => v (Fin.castAdd k i)))
          = (fun v => x (fun i => v (Fin.castAdd k i)))
            + (fun v => y (fun i => v (Fin.castAdd k i))) := by funext v; rfl
      rw [h]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      have h : (fun v : Fin (m + k) → ZMod 2 => (a • x) (fun i => v (Fin.castAdd k i)))
          = a • (fun v => x (fun i => v (Fin.castAdd k i))) := by funext v; rfl
      rw [h]; exact Submodule.smul_mem _ a ih

/-- The four-block concatenation g_0 || g_1 || g_2 || (g_1 + g_2 + g_3) of functions g_0, g_3 in RM(5, 12) and g_1, g_2 in RM(6, 12) lies in RM(7, 14). -/
theorem reed_muller_four_block_concat_degree_seven
    (g0 g3 : (Fin 12 → ZMod 2) → ZMod 2) (g1 g2 : (Fin 12 → ZMod 2) → ZMod 2)
    (hg0 : g0 ∈ reed_muller_code 5 12)
    (hg3 : g3 ∈ reed_muller_code 5 12)
    (hg1 : g1 ∈ reed_muller_code 6 12)
    (hg2 : g2 ∈ reed_muller_code 6 12) :
    four_block_concat g0 g1 g2 (g1 + g2 + g3) ∈ reed_muller_code 7 14 := by
  rw [four_block_concat_reduced]
  simp only []
  let A : (Fin 14 → ZMod 2) → ZMod 2 := fun v => g0 (fun i => v (Fin.castAdd 2 i))
  let B : (Fin 14 → ZMod 2) → ZMod 2 := fun v => g1 (fun i => v (Fin.castAdd 2 i))
  let C : (Fin 14 → ZMod 2) → ZMod 2 := fun v => g2 (fun i => v (Fin.castAdd 2 i))
  let D : (Fin 14 → ZMod 2) → ZMod 2 := fun v => g3 (fun i => v (Fin.castAdd 2 i))
  have hA : A ∈ reed_muller_code 5 14 :=
    reed_muller_four_block_concat_degree_seven_lift_mem (m := 12) (k := 2) (r := 5) hg0
  have hB : B ∈ reed_muller_code 6 14 :=
    reed_muller_four_block_concat_degree_seven_lift_mem (m := 12) (k := 2) (r := 6) hg1
  have hC : C ∈ reed_muller_code 6 14 :=
    reed_muller_four_block_concat_degree_seven_lift_mem (m := 12) (k := 2) (r := 6) hg2
  have hD : D ∈ reed_muller_code 5 14 :=
    reed_muller_four_block_concat_degree_seven_lift_mem (m := 12) (k := 2) (r := 5) hg3
  have hA7 : A ∈ reed_muller_code 7 14 := reed_muller_code_mono (by norm_num) hA
  have ht1 : monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(12 : Fin 14)} : Finset (Fin 14)) A hA
    rw [Finset.card_singleton] at h
    exact reed_muller_code_mono (by norm_num) h
  have ht2 : monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(13 : Fin 14)} : Finset (Fin 14)) A hA
    rw [Finset.card_singleton] at h
    exact reed_muller_code_mono (by norm_num) h
  have ht12 : monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(12 : Fin 14), 13} : Finset (Fin 14)) A hA
    have hc : ({(12 : Fin 14), 13} : Finset (Fin 14)).card = 2 := by simp
    rw [hc] at h
    exact reed_muller_code_mono (by norm_num) h
  have ht3 : monomial ({(12 : Fin 14)} : Finset (Fin 14)) * B ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(12 : Fin 14)} : Finset (Fin 14)) B hB
    rw [Finset.card_singleton] at h
    exact reed_muller_code_mono (by norm_num) h
  have ht4 : monomial ({(13 : Fin 14)} : Finset (Fin 14)) * C ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(13 : Fin 14)} : Finset (Fin 14)) C hC
    rw [Finset.card_singleton] at h
    exact reed_muller_code_mono (by norm_num) h
  have ht5 : monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * D ∈ reed_muller_code 7 14 := by
    have h := reed_muller_four_block_concat_degree_seven_mul_monomial_mem
      ({(12 : Fin 14), 13} : Finset (Fin 14)) D hD
    have hc : ({(12 : Fin 14), 13} : Finset (Fin 14)).card = 2 := by simp
    rw [hc] at h
    exact reed_muller_code_mono (by norm_num) h
  have s1 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ hA7 ht1
  have s2 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ s1 ht2
  have s3 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ s2 ht12
  have s4 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * B ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ s3 ht3
  have s5 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * B
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * C ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ s4 ht4
  have s6 : A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * B
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * C
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * D ∈ reed_muller_code 7 14 :=
    Submodule.add_mem _ s5 ht5
  have key : (fun v : Fin (12+2) → ZMod 2 =>
      (1 + v (Fin.natAdd 12 (0 : Fin 2))) * (1 + v (Fin.natAdd 12 (1 : Fin 2)))
        * g0 (fun i => v (Fin.castAdd 2 i))
      + v (Fin.natAdd 12 (0 : Fin 2)) * g1 (fun i => v (Fin.castAdd 2 i))
      + v (Fin.natAdd 12 (1 : Fin 2)) * g2 (fun i => v (Fin.castAdd 2 i))
      + v (Fin.natAdd 12 (0 : Fin 2)) * v (Fin.natAdd 12 (1 : Fin 2))
        * g3 (fun i => v (Fin.castAdd 2 i)))
      = A + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * A
      + monomial ({(12 : Fin 14)} : Finset (Fin 14)) * B
      + monomial ({(13 : Fin 14)} : Finset (Fin 14)) * C
      + monomial ({(12 : Fin 14), 13} : Finset (Fin 14)) * D := by
    funext v
    simp [A, B, C, D, monomial]
    ring
  rw [key]
  exact s6
