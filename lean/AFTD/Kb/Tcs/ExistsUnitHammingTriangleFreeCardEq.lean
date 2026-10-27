import AFTD.Prelude
import AFTD.Kb.Tcs.UnitHammingTriangleFree

/-!
# exists_unit_hamming_triangle_free_card_eq

Topic: combinatorics   Node: ce08d8599b27

Provenance: helper lemma. arXiv:2610.32789 Section 3.1

For every integer q ≥ 2 and every integer n ≥ 1, there exists a finite set A : Finset (Fin n → Fin q) satisfying unit_hamming_triangle_free A with A.card = 2 * q ^ (n - 1).
-/

open Finset

/-- A word at Hamming distance one from another differs in exactly one coordinate. -/
private lemma pp_hd_one {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {x y : ι → β} (h : hammingDist x y = 1) :
    ∃ i, (∀ j, j ≠ i → x j = y j) ∧ x i ≠ y i := by
  have hc : ({i | x i ≠ y i} : Finset ι).card = 1 := h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hmem : ∀ j, j ∈ ({i | x i ≠ y i} : Finset ι) ↔ j = i := by
    intro j
    rw [hi]; simp
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    by_contra hne
    exact hj ((hmem j).mp (by simpa using hne))
  · have := (hmem i).mpr rfl
    simpa using this

/-- Lower bound construction: there exists a triangle-free subset of (Fin n → Fin q) of size 2 * q^(n-1). -/
theorem exists_unit_hamming_triangle_free_card_eq (n q : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∃ A : Finset (Fin n → Fin q), unit_hamming_triangle_free A ∧ A.card = 2 * q ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  haveI : NeZero q := ⟨by omega⟩
  -- the abelian group ZMod q, and the code {0,1} ⊆ ZMod q
  let e : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let S : Finset (ZMod q) := {0, 1}
  have h01 : (0 : ZMod q) ≠ 1 := by
    intro h
    have : q = 1 := ZMod.one_eq_zero_iff.mp h.symm
    omega
  have hS : S.card = 2 := by simp [S, h01]
  -- the checksum of a word
  let sigma : (Fin (m+1) → Fin q) → ZMod q := fun x => ∑ i, e (x i)
  -- the code: all words whose checksum is in {0,1}
  let A : Finset (Fin (m+1) → Fin q) := Finset.univ.filter (fun x => sigma x ∈ S)
  have sigma_update (x : Fin (m+1) → Fin q) (i : Fin (m+1)) (t : Fin q) :
      sigma (Function.update x i t) = sigma x - e (x i) + e t := by
    simp only [sigma]
    rw [Fin.sum_univ_succAbove (fun j => e (Function.update x i t j)) i]
    rw [Fin.sum_univ_succAbove (fun j => e (x j)) i]
    simp [Function.update_self, Fin.succAbove_ne]
    abel
  -- changing one coordinate always allows exactly two values inside `A`
  have fiber_card (x : Fin (m+1) → Fin q) (i : Fin (m+1)) :
      (Finset.univ.filter (fun t : Fin q => Function.update x i t ∈ A)).card = S.card := by
    let C : ZMod q := sigma x - e (x i)
    have hmem : ∀ t : Fin q, Function.update x i t ∈ A ↔ e t + C ∈ S := by
      intro t
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sigma_update]
      constructor
      · intro h; simpa [C, add_comm, add_left_comm, add_assoc] using h
      · intro h; simpa [C, add_comm, add_left_comm, add_assoc] using h
    refine Finset.card_bij (fun t _ => e t + C) ?_ ?_ ?_
    · intro t ht
      exact (hmem t).mp (by simpa using ht)
    · intro t1 _ t2 _ h
      exact e.injective (add_right_cancel h)
    · intro s hs
      refine ⟨e.symm (s - C), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply (hmem _).mpr
        rw [e.apply_symm_apply]
        have : (s - C) + C = s := by abel
        rw [this]; exact hs
      · rw [e.apply_symm_apply]; abel
  -- every fiber over the tail map has exactly two elements
  have tail_fiber_card (y : Fin m → Fin q) :
      (A.filter (fun x => Fin.tail x = y)).card = 2 := by
    haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
    let c0 : Fin q := Classical.arbitrary (Fin q)
    let x : Fin (m+1) → Fin q := Fin.cons c0 y
    have hright : (Finset.univ.filter (fun t : Fin q => Function.update x 0 t ∈ A)).card = 2 := by
      calc (Finset.univ.filter (fun t : Fin q => Function.update x 0 t ∈ A)).card = S.card :=
            fiber_card x 0
        _ = 2 := hS
    refine (Finset.card_bij (fun x' _ => x' 0) ?_ ?_ ?_).trans hright
    · intro x' hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxmem : x' ∈ A := (Finset.mem_filter.mp hx').1
      have hxtail : Fin.tail x' = y := (Finset.mem_filter.mp hx').2
      have hx'eq : x' = Fin.cons (x' 0) y := by
        rw [← hxtail]; exact (Fin.cons_self_tail x').symm
      rw [hx'eq]
      simp only [Fin.cons_zero]
      have hupd : Function.update x 0 (x' 0) = Fin.cons (x' 0) y := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simp [x]
        · intro j; simp [x, Fin.cons_succ]
      rw [hupd]
      exact hx'eq ▸ hxmem
    · intro x1 hx1 x2 hx2 h
      have hx1tail : Fin.tail x1 = y := (Finset.mem_filter.mp hx1).2
      have hx2tail : Fin.tail x2 = y := (Finset.mem_filter.mp hx2).2
      calc x1 = Fin.cons (x1 0) (Fin.tail x1) := (Fin.cons_self_tail x1).symm
        _ = Fin.cons (x2 0) (Fin.tail x2) := by rw [h, hx1tail, hx2tail]
        _ = x2 := Fin.cons_self_tail x2
    · intro t ht
      refine ⟨Function.update x 0 t, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by simpa using ht, by simp [x, Fin.tail_cons]⟩
      · simp [Function.update_self]
  have hA_card : A.card = 2 * q ^ m := by
    have step1 : A.card = ∑ y ∈ (Finset.univ : Finset (Fin m → Fin q)),
        (A.filter (fun x => Fin.tail x = y)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro x hx; simp
    rw [step1]
    have step2 : ∑ y ∈ (Finset.univ : Finset (Fin m → Fin q)),
        (A.filter (fun x => Fin.tail x = y)).card = ∑ _y : Fin m → Fin q, 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact tail_fiber_card y
    rw [step2, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, smul_eq_mul]
    ring
  refine ⟨A, ?_, hA_card⟩
  intro x y z hx hy hz hxy hyz hxz htri
  obtain ⟨h1, h2, h3⟩ := htri
  -- words at Hamming distance one inside `A` have different checksums
  have key : ∀ a b : Fin (m+1) → Fin q, a ∈ A → b ∈ A → a ≠ b →
      hammingDist a b = 1 → sigma a ≠ sigma b := by
    intro a b _ _ hab hd hsigma
    obtain ⟨i, hagree, hdiff⟩ := pp_hd_one hd
    have hai : a i = b i := by
      by_contra hne
      have hb : b = Function.update a i (b i) := by
        funext k
        by_cases hk : k = i
        · rw [hk]; simp
        · simp [hk, hagree k hk]
      rw [hb, sigma_update a i (b i)] at hsigma
      have h2' : sigma a - e (a i) + e (b i) = sigma a - e (a i) + e (a i) := by
        rw [← hsigma]; abel
      exact hne (e.injective (add_left_cancel h2').symm)
    apply hab
    funext j
    by_cases hj : j = i
    · rw [hj]; exact hai
    · exact hagree j hj
  have hS3 : ∀ v ∈ A, sigma v = 0 ∨ sigma v = 1 := by
    intro v hv
    have hmem : sigma v ∈ S := (Finset.mem_filter.mp hv).2
    simpa [S] using hmem
  have hne1 : sigma x ≠ sigma y := key x y hx hy hxy h1
  have hne2 : sigma y ≠ sigma z := key y z hy hz hyz h2
  have hne3 : sigma x ≠ sigma z := key x z hx hz hxz h3
  have hx' := hS3 x hx
  have hy' := hS3 y hy
  have hz' := hS3 z hz
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz' <;>
    simp_all
