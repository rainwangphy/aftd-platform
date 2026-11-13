import AFTD.Prelude

/-!
# op1525_pair_coloring_profile_classification

Topic: combinatorics   Node: 8e1757258ed9

Provenance: helper lemma. The color-profile classification for the complete pair-part route to OP-1525.

If two Boolean colorings of finitely many labeled pairs have the same number of monochromatic pairs and the same total number of true vertices, one coloring can be transformed into the other by permuting the pairs and independently swapping their two vertices.
-/

open Finset Equiv

def op1525_pair_code (h : Fin 2 → Bool) : Fin 3 :=
  if h 0 = h 1 then
    if h 0 then 2 else 0
  else 1

lemma op1525_pair_code_val (h : Fin 2 → Bool) :
    (op1525_pair_code h).val = (if h 0 then 1 else 0) + (if h 1 then 1 else 0) := by
  revert h; decide

lemma op1525_pair_code_mono (h : Fin 2 → Bool) :
    (h 0 = h 1) ↔ (op1525_pair_code h = 0 ∨ op1525_pair_code h = 2) := by
  revert h; decide

lemma op1525_pair_code_exists_tau (h h' : Fin 2 → Bool) (hc : op1525_pair_code h = op1525_pair_code h') :
    ∃ b : Bool, ∀ j : Fin 2, h (j + if b then 1 else 0) = h' j := by
  revert hc; revert h h'; decide

def op1525_c_wf {I : Type*} [Fintype I] [DecidableEq I] (f : I → Fin 2 → Bool) (k : Fin 3) : ℕ :=
  ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = k)).card

lemma op1525_c_wf_total {I : Type*} [Fintype I] [DecidableEq I] (f : I → Fin 2 → Bool) :
    Fintype.card I = op1525_c_wf f 0 + op1525_c_wf f 1 + op1525_c_wf f 2 := by
  have h := @Finset.card_eq_sum_card_fiberwise I (Fin 3) _ (fun i => op1525_pair_code (f i)) univ univ (fun _ _ => mem_univ _)
  rw [Fin.sum_univ_three] at h
  exact h

lemma op1525_c_wf_mono {I : Type*} [Fintype I] [DecidableEq I] (f : I → Fin 2 → Bool) :
    ((univ : Finset I).filter (fun i => f i 0 = f i 1)).card = op1525_c_wf f 0 + op1525_c_wf f 2 := by
  have heq : ((univ : Finset I).filter (fun i => f i 0 = f i 1)) =
      ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = 0)) ∪
      ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = 2)) := by
    ext i; simp [op1525_pair_code_mono]
  have hdisj : Disjoint ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = 0))
      ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = 2)) := by
    rw [disjoint_filter]
    intro x _ h0 h2
    have : (0 : Fin 3) = 2 := h0.symm.trans h2
    revert this; decide
  rw [heq, card_union_of_disjoint hdisj]
  rfl

lemma op1525_c_wf_true {I : Type*} [Fintype I] [DecidableEq I] (f : I → Fin 2 → Bool) :
    ((univ : Finset (I × Fin 2)).filter (fun x => f x.1 x.2 = true)).card =
    op1525_c_wf f 1 + 2 * op1525_c_wf f 2 := by
  have h1 : ((univ : Finset (I × Fin 2)).filter (fun x => f x.1 x.2 = true)).card =
      ∑ x : I × Fin 2, if f x.1 x.2 = true then 1 else 0 :=
    (sum_boole (fun (x : I × Fin 2) => f x.1 x.2 = true) univ).symm
  rw [h1, ← Finset.univ_product_univ, sum_product]
  simp_rw [Fin.sum_univ_two, ← op1525_pair_code_val (f _)]
  have hfiber := @Finset.sum_fiberwise_of_maps_to I (Fin 3) ℕ _ univ univ _
    (fun i => op1525_pair_code (f i)) (fun _ _ => mem_univ _) (fun i => (op1525_pair_code (f i)).val)
  rw [← hfiber]
  rw [Fin.sum_univ_three]
  dsimp [op1525_c_wf]
  have hz : ∀ j : Fin 3, (∑ i ∈ univ with op1525_pair_code (f i) = j, (op1525_pair_code (f i)).val) =
      j.val * ((univ : Finset I).filter (fun i => op1525_pair_code (f i) = j)).card := by
    intro j
    have : (∑ i ∈ univ with op1525_pair_code (f i) = j, (op1525_pair_code (f i)).val) =
        ∑ i ∈ univ with op1525_pair_code (f i) = j, j.val := by
      apply sum_congr rfl
      intro x hx
      rw [mem_filter] at hx
      rw [hx.2]
    rw [this, sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [hz 0, hz 1, hz 2]
  omega

theorem op1525_pair_coloring_profile_classification
    {I : Type*} [DecidableEq I] [Fintype I] (f g : I → Fin 2 → Bool)
    (hmono : ((Finset.univ : Finset I).filter (fun i => f i 0 = f i 1)).card =
      ((Finset.univ : Finset I).filter (fun i => g i 0 = g i 1)).card)
    (htrue : ((Finset.univ : Finset (I × Fin 2)).filter (fun x => f x.1 x.2 = true)).card =
      ((Finset.univ : Finset (I × Fin 2)).filter (fun x => g x.1 x.2 = true)).card) :
    ∃ σ : Equiv.Perm I, ∃ τ : I → Bool, ∀ i : I, ∀ j : Fin 2,
      f (σ i) (j + if τ i then 1 else 0) = g i j := by
  have h_tot_f := op1525_c_wf_total f
  have h_tot_g := op1525_c_wf_total g
  have h_mono_f := op1525_c_wf_mono f
  have h_mono_g := op1525_c_wf_mono g
  have h_true_f := op1525_c_wf_true f
  have h_true_g := op1525_c_wf_true g
  rw [h_mono_f, h_mono_g] at hmono
  rw [h_true_f, h_true_g] at htrue
  have hc0 : op1525_c_wf g 0 = op1525_c_wf f 0 := by omega
  have hc1 : op1525_c_wf g 1 = op1525_c_wf f 1 := by omega
  have hc2 : op1525_c_wf g 2 = op1525_c_wf f 2 := by omega
  have hcard : ∀ c : Fin 3, Fintype.card {i : I // op1525_pair_code (g i) = c} =
      Fintype.card {i : I // op1525_pair_code (f i) = c} := by
    intro c
    rw [Fintype.subtype_card (univ.filter (fun i => op1525_pair_code (g i) = c)) (fun x => by simp)]
    rw [Fintype.subtype_card (univ.filter (fun i => op1525_pair_code (f i) = c)) (fun x => by simp)]
    fin_cases c <;> assumption
  let e (c : Fin 3) : {i : I // op1525_pair_code (g i) = c} ≃ {i : I // op1525_pair_code (f i) = c} :=
    Classical.choice (Fintype.card_eq.mp (hcard c))
  let σ : Equiv.Perm I := (sigmaFiberEquiv (fun i => op1525_pair_code (g i))).symm.trans
    ((sigmaCongrRight e).trans (sigmaFiberEquiv (fun i => op1525_pair_code (f i))))
  have hσ : ∀ i : I, op1525_pair_code (f (σ i)) = op1525_pair_code (g i) := by
    intro i
    dsimp [σ]
    exact (Classical.choice (Fintype.card_eq.mp (hcard (op1525_pair_code (g i)))) ⟨i, rfl⟩).2
  have hτ : ∀ i : I, ∃ b : Bool, ∀ j : Fin 2, f (σ i) (j + if b then 1 else 0) = g i j := by
    intro i
    exact op1525_pair_code_exists_tau (f (σ i)) (g i) (hσ i)
  choose τ hτ using hτ
  exact ⟨σ, τ, hτ⟩
