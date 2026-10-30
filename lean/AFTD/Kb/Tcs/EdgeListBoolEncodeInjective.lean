import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListBoolEncode

/-!
# edge_list_bool_encode_injective

Topic: np_completeness   Node: fb0e8535fee4

Provenance: helper lemma. Sanity check of edge_list_bool_encode (the encoding is uniquely decodable), for arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs)

The unary encoding edge_list_bool_encode of edge lists as Bool words is injective: different edge lists get different words.
-/

private def edge_list_bool_encode_injective_code (e : ℕ × ℕ) : List Bool :=
  List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

private theorem edge_list_bool_encode_injective_append_assoc (a b c : List Bool) :
    (a ++ b) ++ c = a ++ (b ++ c) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem edge_list_bool_encode_injective_prefix_rep (a b : ℕ) (u v : List Bool)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simpa using h
      | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
      cases b with
      | zero => simp [List.replicate_succ] at h
      | succ b =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
          obtain ⟨-, h'⟩ := h
          obtain ⟨e1, e2⟩ := ih b h'
          exact ⟨by simp [e1], e2⟩

private theorem edge_list_bool_encode_injective_code_prefix (e₁ e₂ : ℕ × ℕ) (x y : List Bool)
    (h : edge_list_bool_encode_injective_code e₁ ++ x
        = edge_list_bool_encode_injective_code e₂ ++ y) :
    e₁ = e₂ ∧ x = y := by
  simp only [edge_list_bool_encode_injective_code, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := edge_list_bool_encode_injective_prefix_rep e₁.1 e₂.1 _ _ h
  have h2' : (List.replicate e₁.2 true ++ [false]) ++ x
      = (List.replicate e₂.2 true ++ [false]) ++ y := h2
  rw [edge_list_bool_encode_injective_append_assoc,
    edge_list_bool_encode_injective_append_assoc,
    List.singleton_append, List.singleton_append] at h2'
  obtain ⟨h3, h4⟩ := edge_list_bool_encode_injective_prefix_rep e₁.2 e₂.2 x y h2'
  exact ⟨Prod.ext h1 h3, h4⟩

private theorem edge_list_bool_encode_injective_cons (a : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    edge_list_bool_encode (a :: l)
      = edge_list_bool_encode_injective_code a ++ edge_list_bool_encode l := by
  simp [edge_list_bool_encode, edge_list_bool_encode_injective_code, List.flatMap]

theorem edge_list_bool_encode_injective : Function.Injective edge_list_bool_encode := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => rfl
      | cons b l₂ => simp [edge_list_bool_encode, List.flatMap] at h
  | cons a l₁ ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp [edge_list_bool_encode, List.flatMap] at h
      | cons b l₂ =>
          rw [edge_list_bool_encode_injective_cons,
            edge_list_bool_encode_injective_cons] at h
          obtain ⟨rfl, h'⟩ := edge_list_bool_encode_injective_code_prefix a b _ _ h
          exact congrArg (List.cons a) (ih h')
