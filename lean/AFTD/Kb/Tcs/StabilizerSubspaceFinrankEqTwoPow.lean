import AFTD.Prelude
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.TrPauliOfNeOne
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ

/-!
# stabilizer_subspace_finrank_eq_two_pow

Topic: quantum   Node: 42750f3094f8

Provenance: formalization of a published result. Source: arXiv:2610.37807 Lemma 10. Lean differs: S is given by its n-k generators (signs ±1, since -I is not in S every element squares to I), independence and -I not in S are stated together as 'no nonempty product of generators is a scalar matrix', and stab(S) is the common +1 eigenspace of the generators.

Let $k \le n$ and let $g_1, \dots, g_{n-k}$ be $n$-qubit Pauli operators $g_l = \varepsilon_l P_l$ with signs $\varepsilon_l \in \{1, -1\}$ and $P_l$ tensor products of $I, X, Y, Z$, which pairwise commute and are independent in the sense that no product of a nonempty subfamily of the $g_l$ is a scalar multiple of the identity (equivalently, the abelian group $S$ they generate has $2^{n-k}$ elements and does not contain $-I$). Then the stabilized subspace $\{\psi \in \mathbb{C}^{2^n} : g_l \psi = \psi \text{ for all } l\}$ (which equals $\{\psi : s\psi = \psi\ \forall s \in S\}$) has complex dimension $2^k$.
-/

open Matrix in
theorem pauliBasis_toMatrix_mul_exists_smul (a b : PauliBasis) :
    ∃ c : ℂ, ∃ r : PauliBasis, a.toMatrix * b.toMatrix = c • r.toMatrix := by
  cases a <;> cases b
  · exact ⟨1, .I, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .X, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .Y, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .Z, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .X, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .I, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨Complex.I, .Z, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨-Complex.I, .Y, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .Y, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨-Complex.I, .Z, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .I, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨Complex.I, .X, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .Z, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨Complex.I, .Y, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨-Complex.I, .X, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩
  · exact ⟨1, .I, by ext i j; fin_cases i <;> fin_cases j <;> simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ]⟩

open Matrix in
theorem pauliMatrix_mul_exists_smul {n : ℕ} (p q : PauliString n) :
    ∃ c : ℂ, ∃ r : PauliString n, pauliMatrix p * pauliMatrix q = c • pauliMatrix r := by
  choose cf rf hf using fun k => pauliBasis_toMatrix_mul_exists_smul (p k) (q k)
  refine ⟨∏ k, cf k, rf, ?_⟩
  ext i l
  simp only [Matrix.mul_apply, pauliMatrix, Matrix.smul_apply, smul_eq_mul]
  simp_rw [← Finset.prod_mul_distrib]
  have h1 := (Fintype.prod_sum (fun (k : Fin n) (x : Fin 2) =>
    (p k).toMatrix (i k) x * (q k).toMatrix x (l k))).symm
  rw [h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  have := congrFun (congrFun (hf k) (i k)) (l k)
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
  exact this

open Matrix in
theorem pauliMatrix_identity_string_eq_one (n : ℕ) : pauliMatrix (fun _ : Fin n => PauliBasis.I) = 1 := by
  have hI : ∀ x y : Fin 2, sigmaI x y = if x = y then 1 else 0 := by
    intro x y; fin_cases x <;> fin_cases y <;> simp [sigmaI]
  ext i j
  simp only [pauliMatrix, PauliBasis.toMatrix, Matrix.one_apply, hI]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
      by_contra h; push Not at h; exact hij (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

open Matrix in
theorem pauliMatrix_mul_self_eq_one {n : ℕ} (p : PauliString n) : pauliMatrix p * pauliMatrix p = 1 := by
  have hsq : ∀ a : PauliBasis, a.toMatrix * a.toMatrix = 1 := by
    intro a; cases a <;> (ext i j; fin_cases i <;> fin_cases j <;>
      simp [PauliBasis.toMatrix, sigmaI, sigmaX, sigmaY, sigmaZ])
  rw [← pauliMatrix_identity_string_eq_one n]
  ext i l
  simp only [Matrix.mul_apply, pauliMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum (fun (k : Fin n) (x : Fin 2) =>
    (p k).toMatrix (i k) x * (p k).toMatrix x (l k))).symm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have := congrFun (congrFun (hsq (p k)) (i k)) (l k)
  simp only [Matrix.mul_apply] at this
  rw [this]
  have hI : ∀ x y : Fin 2, sigmaI x y = if x = y then 1 else 0 := by
    intro x y; fin_cases x <;> fin_cases y <;> simp [sigmaI]
  simp [PauliBasis.toMatrix, hI, Matrix.one_apply]

theorem list_prod_map_one_add_eq_sum {R : Type*} [Ring R] (N : ℕ) (Af : Fin N → R) :
    ((List.finRange N).map (fun l => 1 + Af l)).prod =
      ∑ b : Fin N → Bool, ((List.finRange N).map (fun l => if b l then Af l else 1)).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    have ih' := ih (fun l => Af l.succ)
    simp only [Function.comp_def] at ih' ⊢
    rw [ih', ← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, if_true,
      Bool.false_eq_true, if_false, List.map_cons, List.prod_cons, List.map_map,
      Function.comp_def, one_mul]
    rw [add_mul, one_mul, Finset.mul_sum, add_comm]

theorem list_prod_map_smul_eq_pow_smul {R : Type*} [Ring R] {ι : Type*} (L : List ι) (c : ℂ) [Algebra ℂ R]
    (Af : ι → R) : (L.map (fun l => c • Af l)).prod = c ^ L.length • (L.map Af).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, smul_mul_smul_comm,
      List.length_cons, pow_succ, mul_comm]

open Matrix in
theorem stabilizer_subspace_finrank_eq_two_pow_aux (n k : ℕ) (hk : k ≤ n)
    (p : Fin (n - k) → PauliString n) (ε : Fin (n - k) → ℂ) (hε : ∀ l, ε l = 1 ∨ ε l = -1)
    (hcomm : ∀ l l', Commute (pauliMatrix (p l)) (pauliMatrix (p l')))
    (hind : ∀ b : Fin (n - k) → Bool, b ≠ (fun _ => false) → ∀ c : ℂ,
      ((List.finRange (n - k)).map (fun l => if b l then ε l • pauliMatrix (p l) else 1)).prod ≠ c • 1) :
    Module.finrank ℂ (⨅ l, LinearMap.ker (ε l • pauliOp (p l) - LinearMap.id) : Submodule ℂ (Hn n)) = 2 ^ k := by
  classical
  set G : Fin (n - k) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun l => ε l • pauliMatrix (p l) with hG
  have hε2 : ∀ l, ε l * ε l = 1 := by
    intro l; rcases hε l with h | h <;> rw [h] <;> norm_num
  have hGG : ∀ l, G l * G l = 1 := by
    intro l; simp only [hG, smul_mul_smul_comm, pauliMatrix_mul_self_eq_one, hε2, one_smul]
  have hGc : ∀ l l', Commute (G l) (G l') := fun l l' => ((hcomm l l').smul_left _).smul_right _
  set E : Fin (n - k) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun l => (1/2 : ℂ) • (1 + G l) with hE
  have hGE : ∀ l, G l * E l = E l := by
    intro l; simp only [hE, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hGG, add_comm]
  have hEE : ∀ l, E l * E l = E l := by
    intro l
    have : E l * E l = (1/2 : ℂ) • (E l + G l * E l) := by
      conv_lhs => rw [show E l = (1/2 : ℂ) • (1 + G l) from rfl]
      rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul]
    rw [this, hGE, ← two_smul ℂ (E l), smul_smul]; norm_num
  have hEc : ∀ l l', Commute (E l) (E l') := by
    intro l l'
    exact (((Commute.one_left _).add_left ((Commute.one_right _).add_right (hGc l l'))).smul_left
      _).smul_right _
  have hlist : ∀ L : List (Fin (n - k)), ((L.map E).prod * (L.map E).prod = (L.map E).prod) ∧
      ∀ v : (Fin n → Fin 2) → ℂ, ((L.map E).prod *ᵥ v = v ↔ ∀ l ∈ L, G l *ᵥ v = v) := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hc : Commute (E a) (L.map E).prod := Commute.list_prod_right _ _ (by
        intro x hx; obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; exact hEc a l)
      simp only [List.map_cons, List.prod_cons]
      set P := (L.map E).prod
      refine ⟨?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
      · calc E a * P * (E a * P) = E a * (P * E a) * P := by simp only [mul_assoc]
          _ = E a * (E a * P) * P := by rw [hc.eq]
          _ = (E a * E a) * (P * P) := by simp only [mul_assoc]
          _ = E a * P := by rw [hEE, ih1]
      · have hEv : E a *ᵥ v = v := by
          have : E a *ᵥ ((E a * P) *ᵥ v) = (E a * P) *ᵥ v := by
            rw [mulVec_mulVec, ← mul_assoc, hEE]
          rwa [hv] at this
        have hPv : P *ᵥ v = v := by
          have : P *ᵥ ((E a * P) *ᵥ v) = (E a * P) *ᵥ v := by
            rw [mulVec_mulVec, ← mul_assoc, ← hc.eq, mul_assoc, ih1]
          rwa [hv] at this
        intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · have : G l *ᵥ (E l *ᵥ v) = E l *ᵥ v := by rw [mulVec_mulVec, hGE]
          rwa [hEv] at this
        · exact (ih2 v).mp hPv l hl
      · have hPv : P *ᵥ v = v := (ih2 v).mpr (fun l hl => hv l (List.mem_cons_of_mem _ hl))
        have hEv : E a *ᵥ v = v := by
          have hGv := hv a List.mem_cons_self
          rw [hE]
          simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hGv]
          rw [← two_smul ℂ v, smul_smul]; norm_num
        rw [← mulVec_mulVec, hPv, hEv]
  set Pr := ((List.finRange (n - k)).map E).prod with hPrdef
  have hclose : ∀ (b : Fin (n - k) → Bool) (L : List (Fin (n - k))), ∃ c : ℂ, ∃ r : PauliString n,
      (L.map (fun l => if b l then G l else 1)).prod = c • pauliMatrix r := by
    intro b L
    induction L with
    | nil => exact ⟨1, fun _ => PauliBasis.I, by simp [pauliMatrix_identity_string_eq_one]⟩
    | cons a L ih =>
      obtain ⟨c, r, h⟩ := ih
      obtain ⟨c', r', h'⟩ : ∃ c' : ℂ, ∃ r' : PauliString n,
          (if b a then G a else 1) = c' • pauliMatrix r' := by
        by_cases hb : b a
        · exact ⟨ε a, p a, by simp [hb, hG]⟩
        · exact ⟨1, fun _ => PauliBasis.I, by simp [hb, pauliMatrix_identity_string_eq_one]⟩
      obtain ⟨c'', r'', h''⟩ := pauliMatrix_mul_exists_smul r' r
      refine ⟨c' * c * c'', r'', ?_⟩
      rw [List.map_cons, List.prod_cons, h, h', smul_mul_smul_comm, h'', smul_smul]
  have htr0 : ∀ b : Fin (n - k) → Bool, b ≠ (fun _ => false) →
      (((List.finRange (n - k)).map (fun l => if b l then G l else 1)).prod).trace = 0 := by
    intro b hb
    obtain ⟨c, r, h⟩ := hclose b (List.finRange (n - k))
    by_cases hr : ∃ i, r i ≠ PauliBasis.I
    · rw [h, trace_smul, tr_pauli_of_ne_one n r hr, smul_zero]
    · push Not at hr
      have hr' : r = fun _ => PauliBasis.I := funext hr
      exact absurd (by rw [h, hr', pauliMatrix_identity_string_eq_one]) (hind b hb c)
  have hPr : Pr = (1/2 : ℂ) ^ (n - k) • ∑ b : Fin (n - k) → Bool,
      ((List.finRange (n - k)).map (fun l => if b l then G l else 1)).prod := by
    rw [hPrdef, show ((List.finRange (n - k)).map E) =
      (List.finRange (n - k)).map (fun l => (1/2 : ℂ) • (1 + G l)) from rfl,
      list_prod_map_smul_eq_pow_smul, List.length_finRange, list_prod_map_one_add_eq_sum]
  have htrace : Pr.trace = 2 ^ k := by
    rw [hPr, trace_smul, trace_sum, Finset.sum_eq_single (fun _ => false)]
    · simp only [Bool.false_eq_true, if_false]
      rw [List.map_const', List.prod_replicate, one_pow, trace_one]
      simp only [Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
      have : (2 : ℂ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add]; congr 1; omega
      push_cast
      rw [this, one_div, inv_pow]; field_simp
    · intro b _ hb; exact htr0 b hb
    · simp
  have hPP : Pr * Pr = Pr := (hlist (List.finRange (n - k))).1
  have hPfix : ∀ v, Pr *ᵥ v = v ↔ ∀ l, G l *ᵥ v = v := by
    intro v
    rw [show Pr = ((List.finRange (n - k)).map E).prod from rfl, (hlist _).2 v]
    simp
  have hmemV : ∀ v : Hn n, v ∈ (⨅ l, LinearMap.ker (ε l • pauliOp (p l) - LinearMap.id) :
      Submodule ℂ (Hn n)) ↔ ∀ l, G l *ᵥ (WithLp.ofLp v) = WithLp.ofLp v := by
    intro v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun l => ?_
    have e : ε l • pauliOp (p l) v = WithLp.toLp 2 (G l *ᵥ WithLp.ofLp v) := by
      simp [pauliOp, hG, Matrix.smul_mulVec]
      rfl
    rw [e]
    constructor
    · intro h; have := congrArg WithLp.ofLp h; simpa using this
    · intro h; rw [h]
  have hproj : LinearMap.IsProj (⨅ l, LinearMap.ker (ε l • pauliOp (p l) - LinearMap.id) :
      Submodule ℂ (Hn n)) (Matrix.toEuclideanLin Pr) := by
    constructor
    · intro x
      rw [hmemV]
      have : Pr *ᵥ (Pr *ᵥ WithLp.ofLp x) = Pr *ᵥ WithLp.ofLp x := by rw [mulVec_mulVec, hPP]
      simpa [Matrix.toEuclideanLin] using (hPfix _).mp this
    · intro x hx
      rw [hmemV] at hx
      have := (hPfix (WithLp.ofLp x)).mpr hx
      apply WithLp.ofLp_injective
      simpa [Matrix.toEuclideanLin] using this
  have htr := hproj.trace
  have hlin : LinearMap.trace ℂ (Hn n) (Matrix.toEuclideanLin Pr) = Pr.trace := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun _ ℂ).toBasis, LinearMap.toMatrix_toLin]
  rw [hlin, htrace] at htr
  exact_mod_cast htr.symm

theorem stabilizer_subspace_finrank_eq_two_pow (n k : ℕ) (hk : k ≤ n)
    (p : Fin (n - k) → PauliString n) (ε : Fin (n - k) → ℂ) (hε : ∀ l, ε l = 1 ∨ ε l = -1)
    (hcomm : ∀ l l', Commute (pauliMatrix (p l)) (pauliMatrix (p l')))
    (hind : ∀ b : Fin (n - k) → Bool, b ≠ (fun _ => false) → ∀ c : ℂ,
      ((List.finRange (n - k)).map (fun l => if b l then ε l • pauliMatrix (p l) else 1)).prod ≠ c • 1) :
    Module.finrank ℂ (⨅ l, LinearMap.ker (ε l • pauliOp (p l) - LinearMap.id) : Submodule ℂ (Hn n)) = 2 ^ k := by
  exact stabilizer_subspace_finrank_eq_two_pow_aux n k hk p ε hε hcomm hind
