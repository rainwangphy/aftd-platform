import AFTD.Prelude
import AFTD.Kb.Tcs.Trianglefree24Graph

/-!
# trianglefree24_graph_two_vertex_deletions_strong

Topic: graphs   Node: 2445057945ae

Provenance: helper lemma. Experiments 12544 and 12547; every remaining ordered pair has a directed path of length at most four.

Deleting any two vertices from the explicit 24-vertex digraph leaves it strongly connected; the two specified vertices may coincide.
-/

lemma trianglefree24_graph_adj_iff (x y : Fin 24) :
    trianglefree24_graph.Adj x y ↔ (y - x).val ∈ ({1, 4, 5, 9, 13, 17, 21} : Finset ℕ) := by
  have h : (x y : Fin 24) → ((y.val + 24 - x.val) % 24) = (y - x).val := by
    decide
  exact iff_of_eq (congrArg (· ∈ ({1, 4, 5, 9, 13, 17, 21} : Finset ℕ)) (h x y))

lemma trianglefree24_graph_adj_add (x y c : Fin 24) :
    trianglefree24_graph.Adj (x + c) (y + c) ↔ trianglefree24_graph.Adj x y := by
  rw [trianglefree24_graph_adj_iff, trianglefree24_graph_adj_iff]
  have : (y + c) - (x + c) = y - x := by omega
  rw [this]

def trianglefree24_R (a b x y : Fin 24) : Prop :=
  x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ trianglefree24_graph.Adj x y

lemma trianglefree24_R_add (a b u x y : Fin 24) (h : trianglefree24_R (a - u) (b - u) x y) :
    trianglefree24_R a b (x + u) (y + u) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro heq; apply h1; omega
  · intro heq; apply h2; omega
  · intro heq; apply h3; omega
  · intro heq; apply h4; omega
  · rwa [trianglefree24_graph_adj_add]

lemma trianglefree24_reflTransGen_add (a b u : Fin 24) {x y : Fin 24}
    (h : Relation.ReflTransGen (trianglefree24_R (a - u) (b - u)) x y) :
    Relation.ReflTransGen (trianglefree24_R a b) (x + u) (y + u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (trianglefree24_R_add a b u _ _ hstep)

lemma trianglefree24_R_comm (a b x y : Fin 24) :
    trianglefree24_R a b x y ↔ trianglefree24_R b a x y := by
  dsimp [trianglefree24_R]
  tauto

lemma trianglefree24_reflTransGen_comm (a b : Fin 24) {x y : Fin 24}
    (h : Relation.ReflTransGen (trianglefree24_R b a) x y) :
    Relation.ReflTransGen (trianglefree24_R a b) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih ((trianglefree24_R_comm a b _ _).mpr hstep)

def trianglefree24_adj_b (x y : Fin 24) : Bool :=
  let d := (y.val + 24 - x.val) % 24
  d == 1 || d == 4 || d == 5 || d == 9 || d == 13 || d == 17 || d == 21

lemma trianglefree24_adj_b_iff (x y : Fin 24) :
    trianglefree24_adj_b x y = true ↔ trianglefree24_graph.Adj x y := by
  dsimp [trianglefree24_adj_b, trianglefree24_graph]
  simp only [Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton]
  tauto

def trianglefree24_step_b (a b : Fin 24) (s : Fin 24 → Bool) (y : Fin 24) : Bool :=
  s y || (y != a && y != b && ((List.finRange 24).any fun x => s x && trianglefree24_adj_b x y))

lemma trianglefree24_step_b_sound (a b : Fin 24) (s : Fin 24 → Bool)
    (hs : ∀ y, s y = true → Relation.ReflTransGen (trianglefree24_R a b) 0 y ∧ y ≠ a ∧ y ≠ b)
    (y : Fin 24) (hy : trianglefree24_step_b a b s y = true) :
    Relation.ReflTransGen (trianglefree24_R a b) 0 y ∧ y ≠ a ∧ y ≠ b := by
  dsimp [trianglefree24_step_b] at hy
  rw [Bool.or_eq_true] at hy
  rcases hy with h | h
  · exact hs y h
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with ⟨⟨hya, hyb⟩, hx⟩
    rw [List.any_eq_true] at hx
    rcases hx with ⟨x, _, hx⟩
    simp only [Bool.and_eq_true] at hx
    rcases hx with ⟨hsx, hadj⟩
    rcases hs x hsx with ⟨hreach, hxa, hxb⟩
    rw [trianglefree24_adj_b_iff] at hadj
    have hR : trianglefree24_R a b x y := ⟨hxa, hxb, hya, hyb, hadj⟩
    exact ⟨Relation.ReflTransGen.tail hreach hR, hya, hyb⟩

def trianglefree24_reach4 (a b : Fin 24) : Fin 24 → Bool :=
  let s0 := fun (x : Fin 24) => x == 0
  let s1 := trianglefree24_step_b a b s0
  let s2 := trianglefree24_step_b a b s1
  let s3 := trianglefree24_step_b a b s2
  trianglefree24_step_b a b s3

lemma trianglefree24_reach4_sound (a b : Fin 24) (ha : 0 ≠ a) (hb : 0 ≠ b) (y : Fin 24)
    (hy : trianglefree24_reach4 a b y = true) :
    Relation.ReflTransGen (trianglefree24_R a b) 0 y := by
  have hs0 : ∀ y, (y == 0) = true →
      Relation.ReflTransGen (trianglefree24_R a b) 0 y ∧ y ≠ a ∧ y ≠ b := by
    intro y hy0
    have : y = 0 := beq_iff_eq.mp hy0
    subst this
    exact ⟨Relation.ReflTransGen.refl, ha, hb⟩
  have hs1 := trianglefree24_step_b_sound a b (fun x => x == 0) hs0
  have hs2 := trianglefree24_step_b_sound a b (trianglefree24_step_b a b (fun x => x == 0)) hs1
  have hs3 := trianglefree24_step_b_sound a b _ hs2
  have hs4 := trianglefree24_step_b_sound a b _ hs3
  exact (hs4 y hy).1

def trianglefree24_check_all_symm : Bool :=
  (List.finRange 24).all fun a =>
    (List.finRange 24).all fun b =>
      (a == 0 || b == 0 || b < a) ||
      (let s := trianglefree24_reach4 a b
       (List.finRange 24).all fun v => v == a || v == b || s v)

theorem trianglefree24_check_all_symm_true : trianglefree24_check_all_symm = true := by
  decide

lemma trianglefree24_reach4_of_le (a b v : Fin 24) (ha : 0 ≠ a) (hb : 0 ≠ b) (hab : a ≤ b)
    (hva : v ≠ a) (hvb : v ≠ b) : trianglefree24_reach4 a b v = true := by
  have h := trianglefree24_check_all_symm_true
  rw [trianglefree24_check_all_symm, List.all_eq_true] at h
  have ha_mem := List.mem_finRange a
  have hb_mem := List.mem_finRange b
  have hv_mem := List.mem_finRange v
  have h1 := h a ha_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 b hb_mem
  simp only [Bool.or_eq_true] at h2
  rcases h2 with ((h_a0 | h_b0) | h_ba) | hall
  · rw [beq_iff_eq] at h_a0; exact False.elim (ha h_a0.symm)
  · rw [beq_iff_eq] at h_b0; exact False.elim (hb h_b0.symm)
  · have : b < a := of_decide_eq_true h_ba; omega
  · rw [List.all_eq_true] at hall
    have hv := hall v hv_mem
    simp only [Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with (hva' | hvb') | hreach
    · exact False.elim (hva hva')
    · exact False.elim (hvb hvb')
    · exact hreach

lemma trianglefree24_reach_zero (a b v : Fin 24) (ha : 0 ≠ a) (hb : 0 ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) :
    Relation.ReflTransGen (trianglefree24_R a b) 0 v := by
  rcases le_total a b with hab | hba
  · have hreach := trianglefree24_reach4_of_le a b v ha hb hab hva hvb
    exact trianglefree24_reach4_sound a b ha hb v hreach
  · have hreach := trianglefree24_reach4_of_le b a v hb ha hba hvb hva
    have hpath := trianglefree24_reach4_sound b a hb ha v hreach
    exact trianglefree24_reflTransGen_comm a b hpath

theorem trianglefree24_graph_two_vertex_deletions_strong :
    ∀ a b u v : Fin 24, u ≠ a → u ≠ b → v ≠ a → v ≠ b →
      Relation.ReflTransGen (fun x y => x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
        trianglefree24_graph.Adj x y) u v := by
  intro a b u v hua hub hva hvb
  have ha' : 0 ≠ a - u := by intro h; apply hua; omega
  have hb' : 0 ≠ b - u := by intro h; apply hub; omega
  have hva' : v - u ≠ a - u := by intro h; apply hva; omega
  have hvb' : v - u ≠ b - u := by intro h; apply hvb; omega
  have hpath := trianglefree24_reach_zero (a - u) (b - u) (v - u) ha' hb' hva' hvb'
  have htrans := trianglefree24_reflTransGen_add a b u hpath
  have hu : (0 : Fin 24) + u = u := by omega
  have hv : (v - u) + u = v := by omega
  have hgoal : (fun x y => x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ trianglefree24_graph.Adj x y) =
      trianglefree24_R a b := rfl
  rw [hgoal]
  rwa [hu, hv] at htrans
