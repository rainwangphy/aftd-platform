import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling

/-!
# simple_graph_path_radio_three_seven_extremal_unique

Topic: graphs   Node: 6cfabae340b4

Provenance: helper lemma. Base case m = 1 of simple_graph_path_radio_three_four_mul_add_three_extremal_unique.

The case m = 1: the only (1,3)-radio labelings of P_7 with labels in [0, 6] are 4,1,6,3,0,5,2 and its mirror image.
-/

set_option maxHeartbeats 1000000 in
lemma simple_graph_path_radio_three_seven_extremal_unique_adj_fin {n : ℕ} (i : Fin n)
    (h : i.val + 1 < n) :
    (SimpleGraph.pathGraph n).Adj i ⟨i.val + 1, h⟩ := by
  rw [SimpleGraph.pathGraph_adj]
  exact Or.inl rfl

lemma simple_graph_path_radio_three_seven_extremal_unique_dist_le_succ {n : ℕ} {i j w : Fin n}
    (h : (SimpleGraph.pathGraph n).Adj j w) :
    (SimpleGraph.pathGraph n).dist i w ≤ (SimpleGraph.pathGraph n).dist i j + 1 := by
  have key : (SimpleGraph.pathGraph n).dist i w = (SimpleGraph.pathGraph n).dist i j ∨
      (SimpleGraph.pathGraph n).dist i w = (SimpleGraph.pathGraph n).dist i j + 1 ∨
      (SimpleGraph.pathGraph n).dist i w = (SimpleGraph.pathGraph n).dist i j - 1 :=
    SimpleGraph.Adj.diff_dist_adj h
  omega

lemma simple_graph_path_radio_three_seven_extremal_unique_dist_le_add {n : ℕ} (i : Fin n) :
    ∀ (k : ℕ) (h : i.val + k < n), (SimpleGraph.pathGraph n).dist i ⟨i.val + k, h⟩ ≤ k := by
  intro k
  induction k with
  | zero =>
    intro h
    have hh : (⟨i.val + 0, h⟩ : Fin n) = i := by ext; simp
    rw [hh, SimpleGraph.dist_self]
  | succ k ih =>
    intro h
    have h' : i.val + k < n := by omega
    have hadj : (SimpleGraph.pathGraph n).Adj ⟨i.val + k, h'⟩ ⟨i.val + (k + 1), h⟩ :=
      simple_graph_path_radio_three_seven_extremal_unique_adj_fin ⟨i.val + k, h'⟩
        (by show i.val + k + 1 < n; omega)
    have hstep := simple_graph_path_radio_three_seven_extremal_unique_dist_le_succ (i := i) hadj
    have hih := ih h'
    omega

lemma simple_graph_path_radio_three_seven_extremal_unique_dist_le_abs {n : ℕ} (u v : Fin n) :
    (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| := by
  rcases le_total u.val v.val with h | h
  · have h1 : (SimpleGraph.pathGraph n).dist u v ≤ v.val - u.val := by
      have hbound := simple_graph_path_radio_three_seven_extremal_unique_dist_le_add u
        (v.val - u.val) (by omega)
      have hv : (⟨u.val + (v.val - u.val), (by omega)⟩ : Fin n) = v := by
        apply Fin.ext
        show u.val + (v.val - u.val) = v.val
        omega
      rwa [hv] at hbound
    have h3 : |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| = ((v.val - u.val : ℕ) : ℤ) := by
      rw [abs_of_nonpos] <;> omega
    calc (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ ((v.val - u.val : ℕ) : ℤ) := by
          exact_mod_cast h1
      _ = |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| := h3.symm
  · have h1 : (SimpleGraph.pathGraph n).dist u v ≤ u.val - v.val := by
      have hbound := simple_graph_path_radio_three_seven_extremal_unique_dist_le_add v
        (u.val - v.val) (by omega)
      have hv : (⟨v.val + (u.val - v.val), (by omega)⟩ : Fin n) = u := by
        apply Fin.ext
        show v.val + (u.val - v.val) = u.val
        omega
      rw [hv, SimpleGraph.dist_comm] at hbound
      exact hbound
    have h3 : |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| = ((u.val - v.val : ℕ) : ℤ) := by
      rw [abs_of_nonneg] <;> omega
    calc (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ ((u.val - v.val : ℕ) : ℤ) := by
          exact_mod_cast h1
      _ = |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| := h3.symm

lemma simple_graph_path_radio_three_seven_extremal_unique_nat_abs_int_ge {p q c : ℕ}
    (h : (c : ℤ) ≤ |(p : ℤ) - (q : ℤ)|) : p + c ≤ q ∨ q + c ≤ p := by
  rcases le_abs.mp h with h' | h' <;> omega

lemma simple_graph_path_radio_three_seven_extremal_unique_nat_abs_int_ne {p q : ℕ}
    (h : (1 : ℤ) ≤ |(p : ℤ) - (q : ℤ)|) : p ≠ q := by
  rcases simple_graph_path_radio_three_seven_extremal_unique_nat_abs_int_ge (c := 1) h with
    h' | h' <;> omega

lemma simple_graph_path_radio_three_seven_extremal_unique_disj {n : ℕ} {u v : Fin n}
    {p q D : ℕ} (hD4 : D ≤ 4)
    (hD : (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ (D : ℤ))
    (hcon : (4 : ℤ) - (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ |(p : ℤ) - (q : ℤ)|) :
    p + (4 - D) ≤ q ∨ q + (4 - D) ≤ p := by
  have hcast : ((4 - D : ℕ) : ℤ) = 4 - (D : ℤ) := by
    rw [Nat.cast_sub hD4]; norm_num
  apply simple_graph_path_radio_three_seven_extremal_unique_nat_abs_int_ge
  rw [hcast]
  omega

lemma simple_graph_path_radio_three_seven_extremal_unique_ne {n : ℕ} {u v : Fin n}
    {p q D : ℕ} (hD3 : D ≤ 3)
    (hD : (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ (D : ℤ))
    (hcon : (4 : ℤ) - (((SimpleGraph.pathGraph n).dist u v : ℕ) : ℤ) ≤ |(p : ℤ) - (q : ℤ)|) :
    p ≠ q :=
  simple_graph_path_radio_three_seven_extremal_unique_nat_abs_int_ne (by omega)

set_option maxHeartbeats 2000000 in
lemma simple_graph_path_radio_three_seven_extremal_unique_core (x0 x1 x2 x3 x4 x5 x6 : ℕ)
    (b0 : x0 ≤ 6) (b1 : x1 ≤ 6) (b2 : x2 ≤ 6) (b3 : x3 ≤ 6) (b4 : x4 ≤ 6)
    (b5 : x5 ≤ 6) (b6 : x6 ≤ 6)
    (h01 : x0 + 3 ≤ x1 ∨ x1 + 3 ≤ x0) (h12 : x1 + 3 ≤ x2 ∨ x2 + 3 ≤ x1)
    (h23 : x2 + 3 ≤ x3 ∨ x3 + 3 ≤ x2) (h34 : x3 + 3 ≤ x4 ∨ x4 + 3 ≤ x3)
    (h45 : x4 + 3 ≤ x5 ∨ x5 + 3 ≤ x4) (h56 : x5 + 3 ≤ x6 ∨ x6 + 3 ≤ x5)
    (h02 : x0 + 2 ≤ x2 ∨ x2 + 2 ≤ x0) (h13 : x1 + 2 ≤ x3 ∨ x3 + 2 ≤ x1)
    (h24 : x2 + 2 ≤ x4 ∨ x4 + 2 ≤ x2) (h35 : x3 + 2 ≤ x5 ∨ x5 + 2 ≤ x3)
    (h46 : x4 + 2 ≤ x6 ∨ x6 + 2 ≤ x4)
    (h03 : x0 ≠ x3) (h14 : x1 ≠ x4) (h25 : x2 ≠ x5) (h36 : x3 ≠ x6) :
    (x0 = 4 ∧ x1 = 1 ∧ x2 = 6 ∧ x3 = 3 ∧ x4 = 0 ∧ x5 = 5 ∧ x6 = 2) ∨
    (x0 = 2 ∧ x1 = 5 ∧ x2 = 0 ∧ x3 = 3 ∧ x4 = 6 ∧ x5 = 1 ∧ x6 = 4) := by
  rcases h01 with h01 | h01 <;> rcases h12 with h12 | h12 <;>
    rcases h23 with h23 | h23 <;> rcases h34 with h34 | h34 <;>
    rcases h45 with h45 | h45 <;> rcases h56 with h56 | h56
  all_goals
    first
      | (exfalso; omega)
      | exact Or.inl (by omega)
      | exact Or.inr (by omega)

theorem simple_graph_path_radio_three_seven_extremal_unique (f : Fin 7 → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph 7) 1 3 f)
    (hb : ∀ v, ∀ a ∈ f v, a ≤ 6) :
    f = ![{4}, {1}, {6}, {3}, {0}, {5}, {2}] ∨ f = ![{2}, {5}, {0}, {3}, {6}, {1}, {4}] := by
  obtain ⟨hcard, hradio⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x : Fin 7 → ℕ, ∀ v, f v = {x v} := by
    choose y hy using fun v => Finset.card_eq_one.mp (hcard v)
    exact ⟨y, hy⟩
  have hx6 : ∀ v, x v ≤ 6 := by
    intro v
    exact hb v (x v) (by rw [hx v]; exact Finset.mem_singleton_self (x v))
  have hcon : ∀ i j : Fin 7, i ≠ j →
      (4 : ℤ) - (((SimpleGraph.pathGraph 7).dist i j : ℕ) : ℤ) ≤ |(x i : ℤ) - (x j : ℤ)| := by
    intro i j hij
    have hne : (i, x i) ≠ (j, x j) := fun h => hij (congrArg Prod.fst h)
    have h := hradio i j (x i) (by rw [hx i]; exact Finset.mem_singleton_self _)
      (x j) (by rw [hx j]; exact Finset.mem_singleton_self _) hne
    simpa using h
  have d : ∀ (i j : Fin 7) (D : ℕ), |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| = (D : ℤ) →
      (((SimpleGraph.pathGraph 7).dist i j : ℕ) : ℤ) ≤ (D : ℤ) := by
    intro i j D hD
    have h := simple_graph_path_radio_three_seven_extremal_unique_dist_le_abs (n := 7) i j
    omega
  have h01 : x 0 + 3 ≤ x 1 ∨ x 1 + 3 ≤ x 0 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 0 1 1 (by norm_num)) (hcon 0 1 (by decide))
  have h12 : x 1 + 3 ≤ x 2 ∨ x 2 + 3 ≤ x 1 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 1 2 1 (by norm_num)) (hcon 1 2 (by decide))
  have h23 : x 2 + 3 ≤ x 3 ∨ x 3 + 3 ≤ x 2 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 2 3 1 (by norm_num)) (hcon 2 3 (by decide))
  have h34 : x 3 + 3 ≤ x 4 ∨ x 4 + 3 ≤ x 3 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 3 4 1 (by norm_num)) (hcon 3 4 (by decide))
  have h45 : x 4 + 3 ≤ x 5 ∨ x 5 + 3 ≤ x 4 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 4 5 1 (by norm_num)) (hcon 4 5 (by decide))
  have h56 : x 5 + 3 ≤ x 6 ∨ x 6 + 3 ≤ x 5 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 1) (by norm_num)
      (d 5 6 1 (by norm_num)) (hcon 5 6 (by decide))
  have h02 : x 0 + 2 ≤ x 2 ∨ x 2 + 2 ≤ x 0 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 2) (by norm_num)
      (d 0 2 2 (by norm_num)) (hcon 0 2 (by decide))
  have h13 : x 1 + 2 ≤ x 3 ∨ x 3 + 2 ≤ x 1 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 2) (by norm_num)
      (d 1 3 2 (by norm_num)) (hcon 1 3 (by decide))
  have h24 : x 2 + 2 ≤ x 4 ∨ x 4 + 2 ≤ x 2 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 2) (by norm_num)
      (d 2 4 2 (by norm_num)) (hcon 2 4 (by decide))
  have h35 : x 3 + 2 ≤ x 5 ∨ x 5 + 2 ≤ x 3 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 2) (by norm_num)
      (d 3 5 2 (by norm_num)) (hcon 3 5 (by decide))
  have h46 : x 4 + 2 ≤ x 6 ∨ x 6 + 2 ≤ x 4 :=
    simple_graph_path_radio_three_seven_extremal_unique_disj (D := 2) (by norm_num)
      (d 4 6 2 (by norm_num)) (hcon 4 6 (by decide))
  have h03 : x 0 ≠ x 3 :=
    simple_graph_path_radio_three_seven_extremal_unique_ne (D := 3) (by norm_num)
      (d 0 3 3 (by norm_num)) (hcon 0 3 (by decide))
  have h14 : x 1 ≠ x 4 :=
    simple_graph_path_radio_three_seven_extremal_unique_ne (D := 3) (by norm_num)
      (d 1 4 3 (by norm_num)) (hcon 1 4 (by decide))
  have h25 : x 2 ≠ x 5 :=
    simple_graph_path_radio_three_seven_extremal_unique_ne (D := 3) (by norm_num)
      (d 2 5 3 (by norm_num)) (hcon 2 5 (by decide))
  have h36 : x 3 ≠ x 6 :=
    simple_graph_path_radio_three_seven_extremal_unique_ne (D := 3) (by norm_num)
      (d 3 6 3 (by norm_num)) (hcon 3 6 (by decide))
  rcases simple_graph_path_radio_three_seven_extremal_unique_core (x 0) (x 1) (x 2) (x 3) (x 4)
    (x 5) (x 6) (hx6 0) (hx6 1) (hx6 2) (hx6 3) (hx6 4) (hx6 5) (hx6 6)
    h01 h12 h23 h34 h45 h56 h02 h13 h24 h35 h46 h03 h14 h25 h36 with
    ⟨e0, e1, e2, e3, e4, e5, e6⟩ | ⟨e0, e1, e2, e3, e4, e5, e6⟩
  · left
    funext v
    rw [hx v]
    fin_cases v <;> simp [e0, e1, e2, e3, e4, e5, e6]
  · right
    funext v
    rw [hx v]
    fin_cases v <;> simp [e0, e1, e2, e3, e4, e5, e6]
