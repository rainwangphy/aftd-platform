import AFTD.Prelude
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.ReLUHiddenLayer
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.ReluEncodeHiddenLayer3
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeVec3
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# relu_network3_encode_injective

Topic: np_completeness   Node: 98d0c221ed5e

Provenance: helper lemma. Sanity lemma for relu_network3_encode, serving OP-75 (arXiv:2610.06092, Remark 5.15).

Sanity check of the encoding: distinct width-3 ReLU networks have distinct Bool encodings.
-/

theorem relu_encode_digits_prefix (l l' : List ℕ) (hl : ∀ d ∈ l, d < 2) (hl' : ∀ d ∈ l', d < 2)
    (x y : List Bool)
    (h : l.flatMap (fun d => [true, decide (d = 1)]) ++ false :: x =
      l'.flatMap (fun d => [true, decide (d = 1)]) ++ false :: y) : l = l' ∧ x = y := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using h
    | cons d t => simp at h
  | cons d t ih =>
    cases l' with
    | nil => simp at h
    | cons d' t' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq, true_and,
        decide_eq_decide] at h
      obtain ⟨h1, h2⟩ := h
      have hd := hl d (by simp)
      have hd' := hl' d' (by simp)
      have e : d = d' := by omega
      obtain ⟨e1, e2⟩ := ih t' (fun z hz => hl z (by simp [hz])) (fun z hz => hl' z (by simp [hz])) h2
      exact ⟨by rw [e, e1], e2⟩

theorem relu_encode_nat_prefix (a b : ℕ) (x y : List Bool)
    (h : relu_encode_nat a ++ x = relu_encode_nat b ++ y) : a = b ∧ x = y := by
  unfold relu_encode_nat at h
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨e1, e2⟩ := relu_encode_digits_prefix _ _
    (fun d hd => Nat.digits_lt_base (by norm_num) hd)
    (fun d hd => Nat.digits_lt_base (by norm_num) hd) x y h
  exact ⟨Nat.digits_inj_iff.mp e1, e2⟩

theorem relu_encode_int_prefix (a b : ℤ) (x y : List Bool)
    (h : relu_encode_int a ++ x = relu_encode_int b ++ y) : a = b ∧ x = y := by
  unfold relu_encode_int at h
  simp only [List.cons_append, List.cons.injEq, decide_eq_decide] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := relu_encode_nat_prefix _ _ _ _ h2
  exact ⟨by omega, e2⟩

theorem relu_encode_rat_prefix (a b : ℚ) (x y : List Bool)
    (h : relu_encode_rat a ++ x = relu_encode_rat b ++ y) : a = b ∧ x = y := by
  unfold relu_encode_rat at h
  simp only [List.append_assoc] at h
  obtain ⟨e1, h2⟩ := relu_encode_int_prefix _ _ _ _ h
  obtain ⟨e2, e3⟩ := relu_encode_nat_prefix _ _ _ _ h2
  exact ⟨Rat.ext e1 e2, e3⟩

theorem relu_encode_vec3_prefix (a b : Fin 3 → ℚ) (x y : List Bool)
    (h : relu_encode_vec3 a ++ x = relu_encode_vec3 b ++ y) : a = b ∧ x = y := by
  unfold relu_encode_vec3 at h
  simp only [List.append_assoc] at h
  obtain ⟨e0, h1⟩ := relu_encode_rat_prefix _ _ _ _ h
  obtain ⟨e1, h2⟩ := relu_encode_rat_prefix _ _ _ _ h1
  obtain ⟨e2, e3⟩ := relu_encode_rat_prefix _ _ _ _ h2
  refine ⟨?_, e3⟩
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem relu_encode_hidden_layer3_prefix (a b : ReLUHiddenLayer 3) (x y : List Bool)
    (h : relu_encode_hidden_layer3 a ++ x = relu_encode_hidden_layer3 b ++ y) : a = b ∧ x = y := by
  unfold relu_encode_hidden_layer3 at h
  simp only [List.append_assoc] at h
  obtain ⟨e0, h1⟩ := relu_encode_vec3_prefix _ _ _ _ h
  obtain ⟨e1, h2⟩ := relu_encode_vec3_prefix _ _ _ _ h1
  obtain ⟨e2, h3⟩ := relu_encode_vec3_prefix _ _ _ _ h2
  obtain ⟨e3, e4⟩ := relu_encode_vec3_prefix _ _ _ _ h3
  refine ⟨?_, e4⟩
  cases a with
  | mk w c =>
    cases b with
    | mk w' c' =>
      simp only at e0 e1 e2 e3
      have : w = w' := by
        funext i
        fin_cases i
        · exact e0
        · exact e1
        · exact e2
      rw [this, e3]

theorem relu_encode_layers_prefix (l l' : List (ReLUHiddenLayer 3)) (x y : List Bool)
    (h : l.flatMap (fun z => true :: relu_encode_hidden_layer3 z) ++ false :: x =
      l'.flatMap (fun z => true :: relu_encode_hidden_layer3 z) ++ false :: y) : l = l' ∧ x = y := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using h
    | cons d t => simp at h
  | cons d t ih =>
    cases l' with
    | nil => simp at h
    | cons d' t' =>
      simp only [List.flatMap_cons, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨e1, h2⟩ := relu_encode_hidden_layer3_prefix _ _ _ _ h
      obtain ⟨e2, e3⟩ := ih t' h2
      exact ⟨by rw [e1, e2], e3⟩

theorem relu_network3_encode_injective : Function.Injective relu_network3_encode := by
  intro a b h
  have h' : relu_network3_encode a ++ [] = relu_network3_encode b ++ [] := by rw [h]
  unfold relu_network3_encode at h'
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h'
  obtain ⟨e0, h1⟩ := relu_encode_vec3_prefix _ _ _ _ h'
  obtain ⟨e1, h2⟩ := relu_encode_vec3_prefix _ _ _ _ h1
  obtain ⟨e2, h3⟩ := relu_encode_layers_prefix _ _ _ _ h2
  obtain ⟨e3, h4⟩ := relu_encode_vec3_prefix _ _ _ _ h3
  obtain ⟨e4, -⟩ := relu_encode_rat_prefix _ _ _ _ h4
  cases a; cases b; simp_all
