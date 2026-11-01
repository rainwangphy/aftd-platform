import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough
import AFTD.Kb.Tcs.DigraphReverseArc
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_reverse_arc_through_root_endpoint_eq

Topic: graphs   Node: 16f5a0577963

Provenance: helper lemma. step towards tournament_reverse_arc_arborescence_count_lt

In a tournament T with arc u → v, the number of arborescences rooted at v using u → v equals the number of arborescences of reverse(T, u, v) rooted at u using v → u, via the canonical bijection exchanging root and parent pointer on {u, v}.
-/

lemma tournament_reverse_arc_iter_ge {α : Type*} (f : α → α) (x : α) (h : f x = x) {a b : ℕ} (hab : a ≤ b)
    {w : α} (hw : f^[a] w = x) : f^[b] w = x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_comm, Function.iterate_add_apply, hw, Function.iterate_fixed h k]

lemma tournament_reverse_arc_iter_eq_or_eq_u {n : ℕ} (p : Fin n → Fin n) (u v : Fin n)
    (w : Fin n) (k : ℕ) :
    let p' : Fin n → Fin n := fun x => if x = u then u else if x = v then u else p x
    p'^[k] w = p^[k] w ∨ p'^[k] w = u := by
  intro p'
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    cases ih with
    | inr h =>
      right
      have hp'u : p' u = u := by simp [p']
      rw [h, hp'u]
    | inl h =>
      rw [h]
      dsimp [p']
      split_ifs with h1 h2
      · right; rfl
      · right; rfl
      · left; rfl

lemma tournament_reverse_arc_iter_mul_cycle {α : Type*} (f : α → α) (x : α) (d : ℕ) (h : f^[d] x = x) (m : ℕ) :
    f^[m * d] x = x := by
  induction m with
  | zero => rw [Nat.zero_mul, Function.iterate_zero_apply]
  | succ m ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, h, ih]

lemma tournament_reverse_arc_iter_reach_root_lt_aux {n : ℕ} (p : Fin n → Fin n) (v : Fin n)
    (hpv : p v = v) (hpn : ∀ w, p^[n] w = v) (w : Fin n)
    (a b : ℕ) (hlt : a < b) (hble : b ≤ n) (heq : p^[b] w = p^[a] w) :
    ∃ c < n, p^[c] w = v := by
  let d := b - a
  have hdpos : 0 < d := Nat.sub_pos_of_lt hlt
  have hba : b = d + a := by omega
  have hfeq' : p^[d] (p^[a] w) = p^[a] w := by
    have h1 : p^[d + a] w = p^[a] w := by rwa [← hba]
    rwa [Function.iterate_add_apply] at h1
  have hcycle : p^[n * d] (p^[a] w) = p^[a] w := tournament_reverse_arc_iter_mul_cycle p (p^[a] w) d hfeq' n
  have hnd : n * d = (d - 1) * n + n := by
    calc n * d = n * ((d - 1) + 1) := by rw [Nat.sub_add_cancel hdpos]
    _ = n * (d - 1) + n * 1 := Nat.left_distrib n (d - 1) 1
    _ = (d - 1) * n + n := by rw [Nat.mul_comm n (d - 1), Nat.mul_one]
  have hreach : p^[n * d] (p^[a] w) = v := by
    rw [hnd, Function.iterate_add_apply, hpn, Function.iterate_fixed hpv]
  have hpav : p^[a] w = v := hcycle.symm.trans hreach
  exact ⟨a, lt_of_lt_of_le hlt hble, hpav⟩

lemma tournament_reverse_arc_iter_reach_root_lt {n : ℕ} (p : Fin n → Fin n) (v : Fin n)
    (hpv : p v = v) (hpn : ∀ w, p^[n] w = v) (w : Fin n) :
    ∃ a < n, p^[a] w = v := by
  let f : Fin (n + 1) → Fin n := fun i => p^[i.val] w
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp only [Fintype.card_fin, Nat.lt_succ_self]
  have hninj := Fintype.not_injective_of_card_lt f hcard
  simp only [Function.Injective, not_forall] at hninj
  rcases hninj with ⟨i, j, hfeq, hne⟩
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hlt | hgt
  · exact tournament_reverse_arc_iter_reach_root_lt_aux p v hpv hpn w i.val j.val hlt (Nat.le_of_lt_succ j.isLt) hfeq.symm
  · exact tournament_reverse_arc_iter_reach_root_lt_aux p v hpv hpn w j.val i.val hgt (Nat.le_of_lt_succ i.isLt) hfeq

lemma tournament_reverse_arc_p'_iter_n_eq_u {n : ℕ} (p : Fin n → Fin n) (u v : Fin n)
    (hpv : p v = v) (hpn : ∀ w, p^[n] w = v) (w : Fin n) :
    let p' : Fin n → Fin n := fun x => if x = u then u else if x = v then u else p x
    p'^[n] w = u := by
  intro p'
  have hp'u : p' u = u := by simp [p']
  have hp'v : p' v = u := by
    dsimp [p']
    split_ifs with h1 h2
    · rfl
    · rfl
    · exfalso; exact h2 rfl
  rcases tournament_reverse_arc_iter_reach_root_lt p v hpv hpn w with ⟨a, han, hpa⟩
  have hor := tournament_reverse_arc_iter_eq_or_eq_u p u v w a
  change p'^[a] w = p^[a] w ∨ p'^[a] w = u at hor
  rcases hor with h1 | h2
  · have hp'a1 : p'^[a + 1] w = u := by
      rw [Function.iterate_succ_apply', h1, hpa, hp'v]
    exact tournament_reverse_arc_iter_ge p' u hp'u (Nat.succ_le_of_lt han) hp'a1
  · exact tournament_reverse_arc_iter_ge p' u hp'u (le_of_lt han) h2

/-- In a tournament T with arc u → v, the number of arborescences rooted at v using u → v equals the number of arborescences of T' = reverse(T, u, v) rooted at u using v → u. -/
theorem tournament_reverse_arc_through_root_endpoint_eq {n : ℕ} (T : Digraph (Fin n))
    [DecidableRel T.Adj] (hT : digraph_is_tournament T) (u v : Fin n) (huv : T.Adj u v) :
    digraph_arborescence_count_at_through T v u v =
      digraph_arborescence_count_at_through (digraph_reverse_arc T u v) u v u := by
  have hne : u ≠ v := fun h => hT.1 v (h ▸ huv)
  rw [digraph_arborescence_count_at_through, digraph_arborescence_count_at_through]
  let s : Finset (Fin n → Fin n) := Finset.univ.filter (fun p =>
    p v = v ∧ (∀ w, w ≠ v → T.Adj w (p w)) ∧ (∀ w, p^[n] w = v) ∧ p u = v)
  let t : Finset (Fin n → Fin n) := Finset.univ.filter (fun q =>
    q u = u ∧ (∀ w, w ≠ u → (digraph_reverse_arc T u v).Adj w (q w)) ∧ (∀ w, q^[n] w = u) ∧ q v = u)
  change s.card = t.card
  let f : (Fin n → Fin n) → (Fin n → Fin n) := fun p x => if x = u then u else if x = v then u else p x
  let g : (Fin n → Fin n) → (Fin n → Fin n) := fun q x => if x = v then v else if x = u then v else q x
  have hfg : ∀ p ∈ s, g (f p) = p := by
    intro p hp
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    ext x
    dsimp [f, g]
    by_cases hx_v : x = v
    · rw [hx_v, if_pos rfl, hp.1]
    · rw [if_neg hx_v]
      by_cases hx_u : x = u
      · rw [hx_u, if_pos rfl, hp.2.2.2]
      · rw [if_neg hx_u, if_neg hx_u, if_neg hx_v]
  have hgf : ∀ q ∈ t, f (g q) = q := by
    intro q hq
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    ext x
    dsimp [f, g]
    by_cases hx_u : x = u
    · rw [hx_u, if_pos rfl, hq.1]
    · rw [if_neg hx_u]
      by_cases hx_v : x = v
      · rw [hx_v, if_pos rfl, hq.2.2.2]
      · rw [if_neg hx_v, if_neg hx_v, if_neg hx_u]
  have hfst : ∀ p ∈ s, f p ∈ t := by
    intro p hp
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [f]; rw [if_pos rfl]
    · intro w hw
      by_cases hwv : w = v
      · rw [hwv]
        have hfpv : f p v = u := by dsimp [f]; rw [if_neg (Ne.symm hne), if_pos rfl]
        rw [hfpv]
        rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
        exact huv
      · have hfpw : f p w = p w := by dsimp [f]; rw [if_neg hw, if_neg hwv]
        rw [hfpw]
        have hcond : ¬ (w = u ∧ p w = v ∨ w = v ∧ p w = u) := by
          intro | Or.inl h => exact hw h.1 | Or.inr h => exact hwv h.1
        rw [if_neg hcond]
        exact hp.2.1 w hwv
    · intro w
      exact tournament_reverse_arc_p'_iter_n_eq_u p u v hp.1 hp.2.2.1 w
    · dsimp [f]; rw [if_neg (Ne.symm hne), if_pos rfl]
  have hgts : ∀ q ∈ t, g q ∈ s := by
    intro q hq
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [g]; rw [if_pos rfl]
    · intro w hw
      by_cases hwu : w = u
      · rw [hwu]
        have hgqu : g q u = v := by dsimp [g]; rw [if_neg hne, if_pos rfl]
        rw [hgqu]
        exact huv
      · have hgqw : g q w = q w := by dsimp [g]; rw [if_neg hw, if_neg hwu]
        rw [hgqw]
        have hqadj := hq.2.1 w hwu
        have hcond : ¬ (w = u ∧ q w = v ∨ w = v ∧ q w = u) := by
          intro | Or.inl h => exact hwu h.1 | Or.inr h => exact hw h.1
        rwa [if_neg hcond] at hqadj
    · intro w
      exact tournament_reverse_arc_p'_iter_n_eq_u q v u hq.1 hq.2.2.1 w
    · dsimp [g]; rw [if_neg hne, if_pos rfl]
  exact Finset.card_bij' (fun p hp => f p) (fun q hq => g q)
    hfst hgts (fun p hp => hfg p hp) (fun q hq => hgf q hq)
