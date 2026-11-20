import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BoolLobeForcesEqual

/-!
# op874_prescribed_root_double_cross_refutation

Topic: graphs   Node: 28c1c92ce609

Provenance: original. Related work: Refutes the prescribed-root double-cross conjecture using the explicit fourteen-vertex counterexample in experiments 36471 and 36475.

The following universal assertion is false. For every finite type X with decidable equality, every pair of fixed-point-free permutations p and q, and every root r, assume that any element can be reached from any other by a finite sequence of applications of p and q, and assume that every Boolean assignment b has some x with b(x)=b(p(x))=b(q(x)). Then there is a Boolean assignment b such that for every y other than r, at least one of the inequalities b(y)≠b(p(y)) or b(y)≠b(q(y)) holds, and either both b(p(r)) differs from b(p(p(r))) and b(p(r)) differs from b(q(p(r))), or both b(q(r)) differs from b(p(q(r))) and b(q(r)) differs from b(q(q(r))). The negation is witnessed by a 14-element type.
-/

theorem op874_prescribed_root_double_cross_refutation : ¬ (∀ {X : Type} [Fintype X] [DecidableEq X] (p q : Equiv.Perm X) (hfixed : ∀ x, p x ≠ x ∧ q x ≠ x) (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x flag => if flag then p x else q x) u = v) (hno : ∀ b : X → Bool, ∃ x, b x = b (p x) ∧ b x = b (q x)), ∀ r : X, ∃ b : X → Bool, (∀ x, x ≠ r → b x ≠ b (p x) ∨ b x ≠ b (q x)) ∧ ((b (p r) ≠ b (p (p r)) ∧ b (p r) ≠ b (q (p r))) ∨ (b (q r) ≠ b (p (q r)) ∧ b (q r) ≠ b (q (q r))))) := by
  intro claim
  let P (i : Fin 14) : Fin 14 := ![2,4,3,0,7,6,8,1,5,12,11,13,10,9] i
  let Q (i : Fin 14) : Fin 14 := ![1,3,9,0,7,6,8,5,4,12,11,13,2,10] i
  
  have first_lobe (b : Fin 14 → Bool)
      (h : ∀ i : Fin 14, i ≠ 0 → b i ≠ b (P i) ∨ b i ≠ b (Q i)) : b 1 = b 4 := by
    apply op874_bool_lobe_forces_equal (b 1) (b 4) (b 5) (b 6) (b 7) (b 8)
    · simpa [P,Q] using h 4 (by decide)
    · simpa [P,Q] using h 5 (by decide)
    · simpa [P,Q] using h 6 (by decide)
    · simpa [P,Q] using h 7 (by decide)
    · simpa [P,Q] using (h 8 (by decide)).symm
  
  have second_lobe (b : Fin 14 → Bool)
      (h : ∀ i : Fin 14, i ≠ 0 → b i ≠ b (P i) ∨ b i ≠ b (Q i)) : b 2 = b 9 := by
    apply op874_bool_lobe_forces_equal (b 2) (b 9) (b 10) (b 11) (b 12) (b 13)
    · simpa [P,Q] using h 9 (by decide)
    · simpa [P,Q] using h 10 (by decide)
    · simpa [P,Q] using h 11 (by decide)
    · simpa [P,Q] using (h 12 (by decide)).symm
    · simpa [P,Q] using h 13 (by decide)
  
  have no_double_cross (b : Fin 14 → Bool)
      (h : ∀ i : Fin 14, i ≠ 0 → b i ≠ b (P i) ∨ b i ≠ b (Q i)) :
      ¬ ((b (P 0) ≠ b (P (P 0)) ∧ b (P 0) ≠ b (Q (P 0))) ∨
         (b (Q 0) ≠ b (P (Q 0)) ∧ b (Q 0) ≠ b (Q (Q 0)))) := by
    have h1 := first_lobe b h
    have h2 := second_lobe b h
    simp only [P,Q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    tauto
  
  have no_even_witness (b : Fin 14 → Bool) : ∃ i, b i = b (P i) ∧ b i = b (Q i) := by
    by_contra hn
    push_neg at hn
    have h (i : Fin 14) (_ : i ≠ 0) : b i ≠ b (P i) ∨ b i ≠ b (Q i) := by
      by_cases hi : b i = b (P i)
      · exact Or.inr (hn i hi)
      · exact Or.inl hi
    have h1 := first_lobe b h
    have h2 := second_lobe b h
    have j1 := h 1 (by decide)
    have j2 := h 2 (by decide)
    have j3 := h 3 (by decide)
    have j0 := hn 0
    simp only [P,Q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at j0 j1 j2 j3
    cases e0 : b 0 <;> cases e1 : b 1 <;> cases e2 : b 2 <;> cases e3 : b 3 <;> simp_all
  
  
  
  let PE : Equiv.Perm (Fin 14) := Equiv.ofBijective P (by decide)
  let QE : Equiv.Perm (Fin 14) := Equiv.ofBijective Q (by decide)
  
  have p_nofix : ∀ i, PE i ≠ i ∧ QE i ≠ i := by decide
  
  have to_zero (v : Fin 14) : ∃ w : List Bool, w.foldl (fun x bit => if bit then PE x else QE x) v = 0 := by
    fin_cases v
    · exact ⟨[], by decide⟩
    · exact ⟨[false, true], by decide⟩
    · exact ⟨[true, true], by decide⟩
    · exact ⟨[true], by decide⟩
    · exact ⟨[true, true, false, true], by decide⟩
    · exact ⟨[true, true, false, true, true, false, true], by decide⟩
    · exact ⟨[true, false, true, true, false, true], by decide⟩
    · exact ⟨[true, false, true], by decide⟩
    · exact ⟨[false, true, true, false, true], by decide⟩
    · exact ⟨[true, false, true, true], by decide⟩
    · exact ⟨[true, true, true, true, false, true, true], by decide⟩
    · exact ⟨[true, true, true, false, true, true], by decide⟩
    · exact ⟨[false, true, true], by decide⟩
    · exact ⟨[true, true, false, true, true], by decide⟩
  
  have from_zero (v : Fin 14) : ∃ w : List Bool, w.foldl (fun x bit => if bit then PE x else QE x) 0 = v := by
    fin_cases v
    · exact ⟨[], by decide⟩
    · exact ⟨[false], by decide⟩
    · exact ⟨[true], by decide⟩
    · exact ⟨[true, true], by decide⟩
    · exact ⟨[false, true], by decide⟩
    · exact ⟨[false, true, true, false], by decide⟩
    · exact ⟨[false, true, true, false, true], by decide⟩
    · exact ⟨[false, true, true], by decide⟩
    · exact ⟨[false, true, true, false, true, true], by decide⟩
    · exact ⟨[true, false], by decide⟩
    · exact ⟨[true, false, true, true], by decide⟩
    · exact ⟨[true, false, true, true, true], by decide⟩
    · exact ⟨[true, false, true], by decide⟩
    · exact ⟨[true, false, true, true, true, true], by decide⟩
  
  have strong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then PE x else QE x) u = v := by
    intro u v
    obtain ⟨wu, hu⟩ := to_zero u
    obtain ⟨wv, hv⟩ := from_zero v
    refine ⟨wu ++ wv, ?_⟩
    simp only [List.foldl_append, hu, hv]
  
  have full_counterexample : ∃ p q : Equiv.Perm (Fin 14),
      (∀ i, p i ≠ i ∧ q i ≠ i) ∧
      (∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v) ∧
      (∀ b : Fin 14 → Bool, ∃ i, b i = b (p i) ∧ b i = b (q i)) ∧
      ¬ ∃ b : Fin 14 → Bool, (∀ i, i ≠ 0 → b i ≠ b (p i) ∨ b i ≠ b (q i)) ∧
        ((b (p 0) ≠ b (p (p 0)) ∧ b (p 0) ≠ b (q (p 0))) ∨
         (b (q 0) ≠ b (p (q 0)) ∧ b (q 0) ≠ b (q (q 0)))) := by
    refine ⟨PE, QE, p_nofix, strong, ?_, ?_⟩
    · intro b
      exact no_even_witness b
    · rintro ⟨b, hb, hd⟩
      exact no_double_cross b hb hd
  obtain ⟨p, q, hpq, hs, hn, hbad⟩ := full_counterexample
  exact hbad (claim p q hpq hs hn 0)
