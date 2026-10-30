import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsKStrong
import AFTD.Kb.Tcs.DigraphIsSemicompleteMultipartite
import AFTD.Kb.Tcs.DigraphIsUnilaterallyTwoLinked
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_exists_four_strong_semicomplete_multipartite_not_unilaterally_two_linked_eight

Topic: graphs   Node: 8226c8ff6e1d

Provenance: formalization of a published result. Source: arXiv:2610.36895 Proposition 5.2

There exists a finite type V with exactly 8 elements and a digraph D on V such that D is 4-strong, semicomplete multipartite, and not unilaterally 2-linked.
-/

/-- Arcs of the 8-vertex digraph: A = {0,1}, B = {2,3}, X = {4,5}, Y = {6,7}. -/
def link393_adj (i j : Fin 8) : Bool :=
  let a := i.val; let b := j.val
  -- A ↔ B
  ((a < 2 && 2 ≤ b && b < 4) || (2 ≤ a && a < 4 && b < 2)) ||
  -- A → X, X → B, B → Y, Y → A
  (a < 2 && (b == 4 || b == 5)) || ((a == 4 || a == 5) && 2 ≤ b && b < 4) ||
  (2 ≤ a && a < 4 && 6 ≤ b) || (6 ≤ a && b < 2) ||
  -- inside X and Y
  (a == 4 && b == 5) || (a == 5 && b == 4) || (a == 6 && b == 7) || (a == 7 && b == 6) ||
  -- the 4-cycle 4 → 6 → 5 → 7 → 4
  (a == 4 && b == 6) || (a == 6 && b == 5) || (a == 5 && b == 7) || (a == 7 && b == 4)

def link393_digraph : Digraph (Fin 8) := ⟨fun i j => link393_adj i j = true⟩

instance : DecidableRel link393_digraph.Adj := fun i j => inferInstanceAs (Decidable (link393_adj i j = true))

/-- Depth-first search for a path from the last vertex of `path` (stored reversed) to `v`. -/
def link393_dfs (blocked : Fin 8 → Bool) (v : Fin 8) : ℕ → List (Fin 8) → Option (List (Fin 8))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, x :: rest =>
    if x = v then some (x :: rest).reverse else
    (List.finRange 8).foldl (fun acc y =>
      match acc with
      | some p => some p
      | none =>
        if link393_adj x y && !blocked y && !((x :: rest).contains y) then
          link393_dfs blocked v fuel (y :: x :: rest)
        else none) none

def link393_path_ok (p : List (Fin 8)) (u v : Fin 8) (s : Finset (Fin 8)) : Bool :=
  decide (p.IsChain link393_digraph.Adj) && decide p.Nodup && decide (p.head? = some u) &&
    decide (p.getLast? = some v) && p.all (fun x => decide (x ∉ s))

theorem link393_strong_check : ∀ s : Finset (Fin 8), s.card < 4 → ∀ u v : Fin 8, u ∉ s → v ∉ s → u ≠ v →
    (match link393_dfs (fun x => decide (x ∈ s)) v 9 [u] with
     | some p => link393_path_ok p u v s
     | none => false) = true := by
  decide +kernel

theorem link393_k_strong : digraph_is_k_strong link393_digraph 4 := by
  refine ⟨by simp, fun s hs u v hu hv huv => ?_⟩
  have h := link393_strong_check s hs u v hu hv huv
  split at h
  · rename_i p _
    simp only [link393_path_ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨p, ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩, h.2⟩
  · exact absurd h (by simp)

theorem link393_semicomplete_multipartite : digraph_is_semicomplete_multipartite link393_digraph := by
  refine ⟨by decide, ⟨fun x y z => ?_⟩⟩
  simp only [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, link393_digraph]
  revert x y z
  decide

/-- A chain that starts inside `S` and ends outside it has an arc leaving `S`. -/
theorem link393_chain_exit {V : Type*} (R : V → V → Prop) (S : V → Prop) :
    ∀ (l : List V), l.IsChain R → ∀ a, l.head? = some a → S a → ∀ b, l.getLast? = some b → ¬ S b →
      ∃ x y, x ∈ l ∧ y ∈ l ∧ R x y ∧ S x ∧ ¬ S y := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x t ih =>
    intro hc a ha hSa b hb hSb
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hb
      subst hb; exact absurd hSa hSb
    | cons y t' =>
      rw [List.isChain_cons_cons] at hc
      by_cases hy : S y
      · obtain ⟨x', y', hx', hy', hR, hS1, hS2⟩ :=
          ih hc.2 y (by simp) hy b (by simpa using hb) hSb
        exact ⟨x', y', List.mem_cons_of_mem _ hx', List.mem_cons_of_mem _ hy', hR, hS1, hS2⟩
      · exact ⟨x, y, by simp, by simp, hc.1, hSa, hy⟩

theorem link393_exit_pair (p : List (Fin 8)) (hc : p.IsChain link393_digraph.Adj) (a b : Fin 8)
    (S : Fin 8 → Prop) [DecidablePred S] (ha : p.head? = some a) (hb : p.getLast? = some b)
    (hSa : S a) (hSb : ¬ S b) (f1 f2 : Fin 8) (hf1 : f1 ∉ p) (hf2 : f2 ∉ p) (c1 d1 c2 d2 : Fin 8)
    (key : ∀ x y : Fin 8, S x → ¬ S y → link393_adj x y = true → y ≠ f1 → y ≠ f2 →
      (x = c1 ∧ y = d1) ∨ (x = c2 ∧ y = d2)) :
    (c1 ∈ p ∧ d1 ∈ p) ∨ (c2 ∈ p ∧ d2 ∈ p) := by
  obtain ⟨x, y, hx, hy, hR, hS, hnS⟩ := link393_chain_exit _ S p hc a ha hSa b hb hSb
  have h1 : y ≠ f1 := by rintro rfl; exact hf1 hy
  have h2 : y ≠ f2 := by rintro rfl; exact hf2 hy
  rcases key x y hS hnS hR h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩

theorem link393_not_two_linked : ¬ digraph_is_unilaterally_two_linked link393_digraph := by
  intro h
  obtain ⟨p1, p2, h1, h2, hdisj⟩ := h 0 1 2 3 (by decide)
  have m1 : (0 : Fin 8) ∈ p1 ∧ (1 : Fin 8) ∈ p1 := by
    rcases h1 with ⟨_, _, hh, hl⟩ | ⟨_, _, hh, hl⟩
    · exact ⟨List.mem_of_mem_head? hh, List.mem_of_mem_getLast? hl⟩
    · exact ⟨List.mem_of_mem_getLast? hl, List.mem_of_mem_head? hh⟩
  have m2 : (2 : Fin 8) ∈ p2 ∧ (3 : Fin 8) ∈ p2 := by
    rcases h2 with ⟨_, _, hh, hl⟩ | ⟨_, _, hh, hl⟩
    · exact ⟨List.mem_of_mem_head? hh, List.mem_of_mem_getLast? hl⟩
    · exact ⟨List.mem_of_mem_getLast? hl, List.mem_of_mem_head? hh⟩
  have n2 : (2 : Fin 8) ∉ p1 := fun hm => hdisj hm m2.1
  have n3 : (3 : Fin 8) ∉ p1 := fun hm => hdisj hm m2.2
  have n0 : (0 : Fin 8) ∉ p2 := fun hm => hdisj m1.1 hm
  have n1 : (1 : Fin 8) ∉ p2 := fun hm => hdisj m1.2 hm
  have e1 : ((4 : Fin 8) ∈ p1 ∧ (6 : Fin 8) ∈ p1) ∨ ((5 : Fin 8) ∈ p1 ∧ (7 : Fin 8) ∈ p1) := by
    rcases h1 with ⟨hc, _, hh, hl⟩ | ⟨hc, _, hh, hl⟩
    · exact link393_exit_pair p1 hc 0 1 (fun v => v = 0 ∨ v = 4 ∨ v = 5) hh hl (by decide)
        (by decide) 2 3 n2 n3 4 6 5 7 (by decide)
    · exact link393_exit_pair p1 hc 1 0 (fun v => v = 1 ∨ v = 4 ∨ v = 5) hh hl (by decide)
        (by decide) 2 3 n2 n3 4 6 5 7 (by decide)
  have e2 : ((6 : Fin 8) ∈ p2 ∧ (5 : Fin 8) ∈ p2) ∨ ((7 : Fin 8) ∈ p2 ∧ (4 : Fin 8) ∈ p2) := by
    rcases h2 with ⟨hc, _, hh, hl⟩ | ⟨hc, _, hh, hl⟩
    · exact link393_exit_pair p2 hc 2 3 (fun v => v = 2 ∨ v = 6 ∨ v = 7) hh hl (by decide)
        (by decide) 0 1 n0 n1 6 5 7 4 (by decide)
    · exact link393_exit_pair p2 hc 3 2 (fun v => v = 3 ∨ v = 6 ∨ v = 7) hh hl (by decide)
        (by decide) 0 1 n0 n1 6 5 7 4 (by decide)
  rcases e1 with ⟨h4, h6⟩ | ⟨h5, h7⟩ <;> rcases e2 with ⟨h6', h5'⟩ | ⟨h7', h4'⟩
  · exact hdisj h6 h6'
  · exact hdisj h4 h4'
  · exact hdisj h5 h5'
  · exact hdisj h7 h7'

/-- Proposition 5.2 of arXiv:2610.36895: there exists an 8-vertex 4-strong semicomplete multipartite digraph that is not unilaterally 2-linked. -/
theorem digraph_exists_four_strong_semicomplete_multipartite_not_unilaterally_two_linked_eight :
    ∃ (V : Type) (_ : Fintype V), Fintype.card V = 8 ∧
      ∃ (D : Digraph V), digraph_is_k_strong D 4 ∧
        digraph_is_semicomplete_multipartite D ∧
        ¬ digraph_is_unilaterally_two_linked D :=
  ⟨Fin 8, inferInstance, by simp, link393_digraph, link393_k_strong,
    link393_semicomplete_multipartite, link393_not_two_linked⟩
