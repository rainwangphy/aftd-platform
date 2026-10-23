import AFTD.Prelude
import AFTD.Kb.Tcs.OrientationOutDegreeLeDegree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.Potential

/-!
# additive_coloring_bound_by_degree

Topic: graphs   Node: 9bc522cd3e3a

Provenance: formalization of a published result. Source: arXiv:2610.30174 Theorem 2.1

Let G = (V, E) be a finite simple graph, and let a : V → ℕ assign a positive integer to each vertex. Then there exists an additive coloring f : V → ℕ satisfying a(v) ≤ f(v) ≤ a(v) + deg(v) for every vertex v, meaning f assigns positive integers and adjacent vertices have different neighborhood sums.
-/

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Out-degree of `v` in the arc set `A`. -/
def additive_coloring_bound_by_degree_oDeg (A : Finset (V × V)) (v : V) : ℕ :=
  (A.filter (fun p => p.1 = v)).card

/-- The integer value `a v` plus the out-degree of `v` in the arc set `A`. -/
def additive_coloring_bound_by_degree_fz (a : V → ℕ) (A : Finset (V × V)) (v : V) : ℤ :=
  (a v : ℤ) + (additive_coloring_bound_by_degree_oDeg A v : ℤ)

/-- The difference function supported at `u` and `v`. -/
def additive_coloring_bound_by_degree_delta (u v : V) : V → ℤ :=
  fun x => if x = v then 1 else if x = u then -1 else 0

/-- The potential `∑_{xy ∈ A} f x * f y`. -/
def additive_coloring_bound_by_degree_pot (a : V → ℕ) (A : Finset (V × V)) : ℤ :=
  ∑ p ∈ A, additive_coloring_bound_by_degree_fz a A p.1 * additive_coloring_bound_by_degree_fz a A p.2

/-- Sum of `f` over the out-neighbours of `v`. -/
def additive_coloring_bound_by_degree_outSum (a : V → ℕ) (A : Finset (V × V)) (v : V) : ℤ :=
  ∑ p ∈ A.filter (fun p => p.1 = v), additive_coloring_bound_by_degree_fz a A p.2

/-- Sum of `f` over the in-neighbours of `v`. -/
def additive_coloring_bound_by_degree_inSum (a : V → ℕ) (A : Finset (V × V)) (v : V) : ℤ :=
  ∑ p ∈ A.filter (fun p => p.2 = v), additive_coloring_bound_by_degree_fz a A p.1

/-- A `Finset` of ordered pairs forms an orientation of `G`. -/
def additive_coloring_bound_by_degree_isO (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) : Prop :=
  (∀ p ∈ A, G.Adj p.1 p.2) ∧ (∀ u v, G.Adj u v → ((u,v) ∈ A ↔ (v,u) ∉ A))

/-- The neighbour sum of `f` in `G` at `v`. -/
def additive_coloring_bound_by_degree_nbSum (G : SimpleGraph V) [DecidableRel G.Adj] (a : V → ℕ)
    (A : Finset (V × V)) (v : V) : ℤ :=
  ∑ w ∈ G.neighborFinset v, additive_coloring_bound_by_degree_fz a A w

lemma additive_coloring_bound_by_degree_sum_filter_fst {M : Type*} [AddCommMonoid M]
    (A : Finset (V × V)) (v : V) (g : V → M) :
    ∑ p ∈ A.filter (fun p => p.1 = v), g p.2
      = ∑ w ∈ (Finset.univ.filter (fun w => (v,w) ∈ A)), g w := by
  apply Finset.sum_bij (fun p _ => p.2)
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; rw [← hp.2]; exact hp.1
  · intro p hp q hq hpq; simp only [Finset.mem_filter] at hp hq; cases p; cases q; simp_all
  · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨(v,w), by simp [hw], rfl⟩
  · intro p hp; rfl

lemma additive_coloring_bound_by_degree_sum_filter_snd {M : Type*} [AddCommMonoid M]
    (A : Finset (V × V)) (v : V) (g : V → M) :
    ∑ p ∈ A.filter (fun p => p.2 = v), g p.1
      = ∑ w ∈ (Finset.univ.filter (fun w => (w,v) ∈ A)), g w := by
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; rw [← hp.2]; exact hp.1
  · intro p hp q hq hpq; simp only [Finset.mem_filter] at hp hq; cases p; cases q; simp_all
  · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨(w,v), by simp [hw], rfl⟩
  · intro p hp; rfl

lemma additive_coloring_bound_by_degree_oDeg_rev_u (A : Finset (V × V)) {u v : V} (huv : u ≠ v)
    (hu : (u,v) ∈ A) :
    additive_coloring_bound_by_degree_oDeg (insert (v,u) (A.erase (u,v))) u
      = additive_coloring_bound_by_degree_oDeg A u - 1 := by
  unfold additive_coloring_bound_by_degree_oDeg
  have h1 : ((insert (v,u) (A.erase (u,v))).filter (fun p => p.1 = u))
      = (A.filter (fun p => p.1 = u)).erase (u,v) := by
    rw [Finset.filter_insert, if_neg (Ne.symm huv), Finset.filter_erase]
  rw [h1, Finset.card_erase_of_mem]
  exact Finset.mem_filter.mpr ⟨hu, rfl⟩

lemma additive_coloring_bound_by_degree_oDeg_rev_v (A : Finset (V × V)) {u v : V} (huv : u ≠ v)
    (hv : (v,u) ∉ A) :
    additive_coloring_bound_by_degree_oDeg (insert (v,u) (A.erase (u,v))) v
      = additive_coloring_bound_by_degree_oDeg A v + 1 := by
  unfold additive_coloring_bound_by_degree_oDeg
  have h1 : ((insert (v,u) (A.erase (u,v))).filter (fun p => p.1 = v))
      = insert (v,u) (A.filter (fun p => p.1 = v)) := by
    rw [Finset.filter_insert, if_pos rfl, Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter]; rintro ⟨-, h⟩; exact huv h
  rw [h1, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter]; rintro ⟨h, -⟩; exact hv h

lemma additive_coloring_bound_by_degree_oDeg_rev_other (A : Finset (V × V)) {u v x : V}
    (hx1 : x ≠ u) (hx2 : x ≠ v) :
    additive_coloring_bound_by_degree_oDeg (insert (v,u) (A.erase (u,v))) x
      = additive_coloring_bound_by_degree_oDeg A x := by
  unfold additive_coloring_bound_by_degree_oDeg
  have h1 : ((insert (v,u) (A.erase (u,v))).filter (fun p => p.1 = x))
      = (A.filter (fun p => p.1 = x)) := by
    rw [Finset.filter_insert, if_neg (Ne.symm hx2), Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter]; rintro ⟨-, h⟩; exact hx1 h.symm
  rw [h1]

lemma additive_coloring_bound_by_degree_fz_rev (a : V → ℕ) {A : Finset (V × V)} {u v : V}
    (huv : u ≠ v) (hu : (u,v) ∈ A) (hv : (v,u) ∉ A) (x : V) :
    additive_coloring_bound_by_degree_fz a (insert (v,u) (A.erase (u,v))) x
      = additive_coloring_bound_by_degree_fz a A x + additive_coloring_bound_by_degree_delta u v x := by
  unfold additive_coloring_bound_by_degree_fz additive_coloring_bound_by_degree_delta
  by_cases hx1 : x = u
  · rw [hx1, additive_coloring_bound_by_degree_oDeg_rev_u A huv hu]
    have hle : 1 ≤ additive_coloring_bound_by_degree_oDeg A u := by
      unfold additive_coloring_bound_by_degree_oDeg
      exact Finset.card_pos.mpr ⟨(u,v), Finset.mem_filter.mpr ⟨hu, rfl⟩⟩
    rw [Nat.cast_sub hle]; simp only [huv, if_true, ite_false]; ring
  · by_cases hx2 : x = v
    · rw [hx2, additive_coloring_bound_by_degree_oDeg_rev_v A huv hv]
      simp only [ite_true]; push_cast; ring
    · rw [additive_coloring_bound_by_degree_oDeg_rev_other A hx1 hx2]
      simp only [hx1, hx2, if_false]; ring

lemma additive_coloring_bound_by_degree_T1_eq (a : V → ℕ) (A : Finset (V × V)) {u v : V}
    (huv : u ≠ v) :
    ∑ p ∈ A, additive_coloring_bound_by_degree_fz a A p.1 * additive_coloring_bound_by_degree_delta u v p.2
      = additive_coloring_bound_by_degree_inSum a A v - additive_coloring_bound_by_degree_inSum a A u := by
  have hpt : ∀ p ∈ A, additive_coloring_bound_by_degree_fz a A p.1 * additive_coloring_bound_by_degree_delta u v p.2
      = (if p.2 = v then additive_coloring_bound_by_degree_fz a A p.1 else 0)
        - (if p.2 = u then additive_coloring_bound_by_degree_fz a A p.1 else 0) := by
    intro p hp; simp only [additive_coloring_bound_by_degree_delta]
    by_cases h1 : p.2 = v
    · by_cases h2 : p.2 = u
      · exact absurd (h2.symm.trans h1) huv
      · simp only [if_pos h1, if_neg h2]; ring
    · by_cases h2 : p.2 = u
      · simp only [if_neg h1, if_pos h2]; ring
      · simp only [if_neg h1, if_neg h2]; ring
  calc ∑ p ∈ A, additive_coloring_bound_by_degree_fz a A p.1 * additive_coloring_bound_by_degree_delta u v p.2
      = ∑ p ∈ A, ((if p.2 = v then additive_coloring_bound_by_degree_fz a A p.1 else 0)
          - (if p.2 = u then additive_coloring_bound_by_degree_fz a A p.1 else 0)) :=
          Finset.sum_congr rfl hpt
    _ = (∑ p ∈ A, (if p.2 = v then additive_coloring_bound_by_degree_fz a A p.1 else 0))
          - (∑ p ∈ A, (if p.2 = u then additive_coloring_bound_by_degree_fz a A p.1 else 0)) :=
          Finset.sum_sub_distrib _ _
    _ = additive_coloring_bound_by_degree_inSum a A v - additive_coloring_bound_by_degree_inSum a A u := by
          congr 1
          · unfold additive_coloring_bound_by_degree_inSum; rw [Finset.sum_filter]
          · unfold additive_coloring_bound_by_degree_inSum; rw [Finset.sum_filter]

lemma additive_coloring_bound_by_degree_T2_eq (a : V → ℕ) (A : Finset (V × V)) {u v : V}
    (huv : u ≠ v) :
    ∑ p ∈ A, additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_fz a A p.2
      = additive_coloring_bound_by_degree_outSum a A v - additive_coloring_bound_by_degree_outSum a A u := by
  have hpt : ∀ p ∈ A, additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_fz a A p.2
      = (if p.1 = v then additive_coloring_bound_by_degree_fz a A p.2 else 0)
        - (if p.1 = u then additive_coloring_bound_by_degree_fz a A p.2 else 0) := by
    intro p hp; simp only [additive_coloring_bound_by_degree_delta]
    by_cases h1 : p.1 = v
    · by_cases h2 : p.1 = u
      · exact absurd (h2.symm.trans h1) huv
      · simp only [if_pos h1, if_neg h2]; ring
    · by_cases h2 : p.1 = u
      · simp only [if_neg h1, if_pos h2]; ring
      · simp only [if_neg h1, if_neg h2]; ring
  calc ∑ p ∈ A, additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_fz a A p.2
      = ∑ p ∈ A, ((if p.1 = v then additive_coloring_bound_by_degree_fz a A p.2 else 0)
          - (if p.1 = u then additive_coloring_bound_by_degree_fz a A p.2 else 0)) :=
          Finset.sum_congr rfl hpt
    _ = (∑ p ∈ A, (if p.1 = v then additive_coloring_bound_by_degree_fz a A p.2 else 0))
          - (∑ p ∈ A, (if p.1 = u then additive_coloring_bound_by_degree_fz a A p.2 else 0)) :=
          Finset.sum_sub_distrib _ _
    _ = additive_coloring_bound_by_degree_outSum a A v - additive_coloring_bound_by_degree_outSum a A u := by
          congr 1
          · unfold additive_coloring_bound_by_degree_outSum; rw [Finset.sum_filter]
          · unfold additive_coloring_bound_by_degree_outSum; rw [Finset.sum_filter]

lemma additive_coloring_bound_by_degree_T3_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) {u v : V} (huv : u ≠ v) (hu : (u,v) ∈ A) (hv : (v,u) ∉ A)
    (hloop : ∀ p ∈ A, G.Adj p.1 p.2) :
    ∑ p ∈ A, additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_delta u v p.2 = -1 := by
  rw [Finset.sum_eq_single_of_mem (u,v) hu]
  · simp [additive_coloring_bound_by_degree_delta, huv]
  · intro p hp hpne
    by_cases h1 : p.1 = u
    · have hp2v : ¬ (p.2 = v) := by intro h; exact hpne (Prod.ext h1 h)
      have hp2u : ¬ (p.2 = u) := by
        intro h; have hh := hloop p hp; rw [h1, h] at hh; exact G.irrefl hh
      have d1 : additive_coloring_bound_by_degree_delta u v p.1 = -1 := by
        simp [additive_coloring_bound_by_degree_delta, h1, huv]
      have d2 : additive_coloring_bound_by_degree_delta u v p.2 = 0 := by
        simp [additive_coloring_bound_by_degree_delta, hp2v, hp2u]
      rw [d1, d2]; ring
    · by_cases h2 : p.1 = v
      · have hp2u : ¬ (p.2 = u) := by
          intro h; have hpeq : p = (v,u) := Prod.ext h2 h; rw [hpeq] at hp; exact hv hp
        have hp2v : ¬ (p.2 = v) := by
          intro h; have hh := hloop p hp; rw [h2, h] at hh; exact G.irrefl hh
        have d1 : additive_coloring_bound_by_degree_delta u v p.1 = 1 := by
          simp [additive_coloring_bound_by_degree_delta, h2]
        have d2 : additive_coloring_bound_by_degree_delta u v p.2 = 0 := by
          simp [additive_coloring_bound_by_degree_delta, hp2v, hp2u]
        rw [d1, d2]; ring
      · have d1 : additive_coloring_bound_by_degree_delta u v p.1 = 0 := by
          simp [additive_coloring_bound_by_degree_delta, h1, h2]
        rw [d1]; ring

lemma additive_coloring_bound_by_degree_pot_rev (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℕ) {A : Finset (V × V)} {u v : V} (huv : u ≠ v) (hu : (u,v) ∈ A)
    (hv : (v,u) ∉ A) (hloop : ∀ p ∈ A, G.Adj p.1 p.2) :
    additive_coloring_bound_by_degree_pot a (insert (v,u) (A.erase (u,v))) - additive_coloring_bound_by_degree_pot a A
      = additive_coloring_bound_by_degree_outSum a A v - additive_coloring_bound_by_degree_outSum a A u
        + additive_coloring_bound_by_degree_inSum a A v - additive_coloring_bound_by_degree_inSum a A u - 1 := by
  have hsum : additive_coloring_bound_by_degree_pot a (insert (v,u) (A.erase (u,v)))
      = ∑ p ∈ A, additive_coloring_bound_by_degree_fz a (insert (v,u) (A.erase (u,v))) p.1
          * additive_coloring_bound_by_degree_fz a (insert (v,u) (A.erase (u,v))) p.2 := by
    unfold additive_coloring_bound_by_degree_pot
    rw [Finset.sum_insert]
    · have h := Finset.sum_erase_add (s := A)
        (f := fun p : V × V => additive_coloring_bound_by_degree_fz a (insert (v,u) (A.erase (u,v))) p.1
          * additive_coloring_bound_by_degree_fz a (insert (v,u) (A.erase (u,v))) p.2) hu
      rw [← h, add_comm]; congr 1; rw [mul_comm]
    · simp only [Finset.mem_erase]; rintro ⟨-, hA⟩; exact hv hA
  have key : additive_coloring_bound_by_degree_pot a (insert (v,u) (A.erase (u,v))) - additive_coloring_bound_by_degree_pot a A
      = ∑ p ∈ A, (additive_coloring_bound_by_degree_fz a A p.1 * additive_coloring_bound_by_degree_delta u v p.2
          + additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_fz a A p.2
          + additive_coloring_bound_by_degree_delta u v p.1 * additive_coloring_bound_by_degree_delta u v p.2) := by
    rw [hsum]; unfold additive_coloring_bound_by_degree_pot; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [additive_coloring_bound_by_degree_fz_rev a huv hu hv p.1,
        additive_coloring_bound_by_degree_fz_rev a huv hu hv p.2]
    ring
  rw [key, Finset.sum_add_distrib, Finset.sum_add_distrib,
    additive_coloring_bound_by_degree_T1_eq a A huv, additive_coloring_bound_by_degree_T2_eq a A huv,
    additive_coloring_bound_by_degree_T3_eq G A huv hu hv hloop]
  ring

lemma additive_coloring_bound_by_degree_isO_rev (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (hO : additive_coloring_bound_by_degree_isO G A) {u v : V}
    (huv : u ≠ v) (hu : (u,v) ∈ A) (hv : (v,u) ∉ A) :
    additive_coloring_bound_by_degree_isO G (insert (v,u) (A.erase (u,v))) := by
  have memB : ∀ a b : V, (a,b) ∈ insert (v,u) (A.erase (u,v)) ↔
      ((a,b) = (v,u) ∨ ((a,b) ∈ A ∧ (a,b) ≠ (u,v))) := by
    intro a b; rw [Finset.mem_insert, Finset.mem_erase]; tauto
  constructor
  · intro p hp
    rw [memB] at hp
    rcases hp with hp | ⟨hpA, -⟩
    · obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
      rw [hp1, hp2]; exact (G.adj_comm u v).mp (hO.1 (u,v) hu)
    · exact hO.1 p hpA
  · intro x y hxy
    rw [memB x y, memB y x]
    by_cases h1 : (x,y) = (u,v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1; simp [huv]
    · by_cases h2 : (y,x) = (u,v)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; simp [huv]
      · have hxy_ne_vu : (x,y) ≠ (v,u) := by
          intro h; apply h2; obtain ⟨a,b⟩ := Prod.mk.inj h; rw [b, a]
        have hyx_ne_vu : (y,x) ≠ (v,u) := by
          intro h; apply h1; obtain ⟨a,b⟩ := Prod.mk.inj h; rw [b, a]
        constructor
        · rintro (h | ⟨hA, -⟩)
          · exact absurd h hxy_ne_vu
          · intro hyxB
            rcases hyxB with h | ⟨hyxA, -⟩
            · exact absurd h hyx_ne_vu
            · exact ((hO.2 x y hxy).mp hA) hyxA
        · intro hyxB
          have hQ : ¬ (y,x) ∈ A := fun hQ => hyxB (Or.inr ⟨hQ, h2⟩)
          exact Or.inr ⟨(hO.2 x y hxy).mpr hQ, h1⟩

lemma additive_coloring_bound_by_degree_exists_isO (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A : Finset (V × V), additive_coloring_bound_by_degree_isO G A := by
  let e := Fintype.equivFin V
  refine ⟨Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ e p.1 < e p.2), ?_, ?_⟩
  · intro p hp; simp only [Finset.mem_filter] at hp; exact hp.2.1
  · intro u v huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have huv' : G.Adj v u := (G.adj_comm u v).mp huv
    have hne : e u ≠ e v := by intro h; exact (G.ne_of_adj huv) (e.injective h)
    simp only [huv, huv', true_and]
    constructor
    · intro h; exact not_lt.mpr (le_of_lt h)
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) hne

lemma additive_coloring_bound_by_degree_nbSum_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℕ) {A : Finset (V × V)} (hO : additive_coloring_bound_by_degree_isO G A) (v : V) :
    additive_coloring_bound_by_degree_nbSum G a A v
      = additive_coloring_bound_by_degree_outSum a A v + additive_coloring_bound_by_degree_inSum a A v := by
  unfold additive_coloring_bound_by_degree_nbSum
  have hnf : G.neighborFinset v = Finset.univ.filter (fun w => G.Adj v w) := by
    ext w; rw [SimpleGraph.mem_neighborFinset]; simp
  rw [hnf, Finset.sum_filter]
  have ho : additive_coloring_bound_by_degree_outSum a A v
      = ∑ w ∈ Finset.univ, if (v,w) ∈ A then additive_coloring_bound_by_degree_fz a A w else 0 := by
    unfold additive_coloring_bound_by_degree_outSum
    rw [additive_coloring_bound_by_degree_sum_filter_fst A v (additive_coloring_bound_by_degree_fz a A),
      Finset.sum_filter]
  have hi : additive_coloring_bound_by_degree_inSum a A v
      = ∑ w ∈ Finset.univ, if (w,v) ∈ A then additive_coloring_bound_by_degree_fz a A w else 0 := by
    unfold additive_coloring_bound_by_degree_inSum
    rw [additive_coloring_bound_by_degree_sum_filter_snd A v (additive_coloring_bound_by_degree_fz a A),
      Finset.sum_filter]
  rw [ho, hi, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hadj : G.Adj v w
  · have hiff := hO.2 v w hadj
    by_cases hvw : (v,w) ∈ A
    · have hwv : (w,v) ∉ A := hiff.mp hvw; simp [hadj, hvw, hwv]
    · have hwv : (w,v) ∈ A := by by_contra h; exact hvw (hiff.mpr h)
      simp [hadj, hvw, hwv]
  · have hvw : (v,w) ∉ A := by intro h; exact hadj (hO.1 (v,w) h)
    have hwv : (w,v) ∉ A := by intro h; exact hadj ((G.adj_comm w v).mp (hO.1 (w,v) h))
    simp [hadj, hvw, hwv]

lemma additive_coloring_bound_by_degree_oDeg_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (V × V)) (hO : additive_coloring_bound_by_degree_isO G A) (v : V) :
    additive_coloring_bound_by_degree_oDeg A v ≤ G.degree v := by
  unfold additive_coloring_bound_by_degree_oDeg
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (f := fun p : V × V => p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_coe] at hp ⊢
    rw [SimpleGraph.mem_neighborFinset]
    have := hO.1 p hp.1
    rwa [hp.2] at this
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_coe] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq

end

/-- Every finite simple graph with vertex weights a_v ≥ 1 admits an additive coloring with labels between a_v and a_v + deg(v). -/
theorem additive_coloring_bound_by_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (ha : ∀ v, 0 < a v) :
    ∃ f : V → ℕ, (∀ v, 0 < f v) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w) ∧
      (∀ v, a v ≤ f v ∧ f v ≤ a v + G.degree v) := by
  haveI hdec : DecidablePred (fun A : Finset (V × V) => additive_coloring_bound_by_degree_isO G A) :=
    fun A => by unfold additive_coloring_bound_by_degree_isO; infer_instance
  obtain ⟨A, hAmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun A : Finset (V × V) => additive_coloring_bound_by_degree_isO G A))
    (additive_coloring_bound_by_degree_pot a) (by
      obtain ⟨B, hB⟩ := additive_coloring_bound_by_degree_exists_isO G
      exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ B, hB⟩⟩)
  have hAO : A ∈ Finset.univ.filter (fun A : Finset (V × V) => additive_coloring_bound_by_degree_isO G A) :=
    hAmin.1
  have hmin := hAmin.2
  have hO : additive_coloring_bound_by_degree_isO G A := (Finset.mem_filter.mp hAO).2
  have nmem : ∀ B : Finset (V × V), additive_coloring_bound_by_degree_isO G B →
      additive_coloring_bound_by_degree_pot a A ≤ additive_coloring_bound_by_degree_pot a B :=
    fun B hB => hmin B (Finset.mem_filter.mpr ⟨Finset.mem_univ B, hB⟩)
  have nbSum_cast : ∀ u, additive_coloring_bound_by_degree_nbSum G a A u
      = ((∑ w ∈ G.neighborFinset u, (a w + additive_coloring_bound_by_degree_oDeg A w) : ℕ) : ℤ) := by
    intro u
    unfold additive_coloring_bound_by_degree_nbSum
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [additive_coloring_bound_by_degree_fz]
    push_cast
    ring
  have harc : ∀ x y : V, (x,y) ∈ A →
      additive_coloring_bound_by_degree_nbSum G a A x < additive_coloring_bound_by_degree_nbSum G a A y := by
    intro x y hxy
    have hxyne : x ≠ y := G.ne_of_adj (hO.1 (x,y) hxy)
    have hyx : (y,x) ∉ A := (hO.2 x y (hO.1 (x,y) hxy)).mp hxy
    have hBO : additive_coloring_bound_by_degree_isO G (insert (y,x) (A.erase (x,y))) :=
      additive_coloring_bound_by_degree_isO_rev G A hO hxyne hxy hyx
    have hle : additive_coloring_bound_by_degree_pot a A
        ≤ additive_coloring_bound_by_degree_pot a (insert (y,x) (A.erase (x,y))) := nmem _ hBO
    have hpr := additive_coloring_bound_by_degree_pot_rev G a hxyne hxy hyx hO.1
    have hnonneg : 0 ≤ additive_coloring_bound_by_degree_pot a (insert (y,x) (A.erase (x,y)))
        - additive_coloring_bound_by_degree_pot a A := by linarith
    rw [hpr] at hnonneg
    have hx := additive_coloring_bound_by_degree_nbSum_eq G a hO x
    have hy := additive_coloring_bound_by_degree_nbSum_eq G a hO y
    have heq : additive_coloring_bound_by_degree_nbSum G a A y - additive_coloring_bound_by_degree_nbSum G a A x - 1
        = additive_coloring_bound_by_degree_outSum a A y - additive_coloring_bound_by_degree_outSum a A x
          + additive_coloring_bound_by_degree_inSum a A y - additive_coloring_bound_by_degree_inSum a A x - 1 := by
      rw [hy, hx]; ring
    rw [← heq] at hnonneg
    linarith
  refine ⟨fun v => a v + additive_coloring_bound_by_degree_oDeg A v, ?_, ?_, ?_⟩
  · intro v; show 0 < a v + additive_coloring_bound_by_degree_oDeg A v; have := ha v; omega
  · intro u v huv
    have hiff := hO.2 u v huv
    by_cases huvA : (u,v) ∈ A
    · have hlt := harc u v huvA
      intro heq
      have hcast : additive_coloring_bound_by_degree_nbSum G a A u
          = additive_coloring_bound_by_degree_nbSum G a A v := by
        rw [nbSum_cast u, nbSum_cast v, heq]
      exact (ne_of_lt hlt) hcast
    · have hvuA : (v,u) ∈ A := by by_contra h; exact huvA (hiff.mpr h)
      have hlt := harc v u hvuA
      intro heq
      have hcast : additive_coloring_bound_by_degree_nbSum G a A u
          = additive_coloring_bound_by_degree_nbSum G a A v := by
        rw [nbSum_cast u, nbSum_cast v, heq]
      exact (ne_of_lt hlt).symm hcast
  · intro v
    refine ⟨?_, ?_⟩
    · show a v ≤ a v + additive_coloring_bound_by_degree_oDeg A v; omega
    · show a v + additive_coloring_bound_by_degree_oDeg A v ≤ a v + G.degree v
      have := additive_coloring_bound_by_degree_oDeg_le_degree G A hO v; omega
