import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaxHypercubeCoil
import AFTD.Kb.Tcs.HypercubeDegreeCount
import AFTD.Kb.Tcs.HypercubeDisjointSquaresCount
import AFTD.Kb.Tcs.IsHypercubeSquare
import AFTD.Kb.Tcs.HypercubeCoil
import AFTD.Kb.Tcs.SimpleGraphHypercube
import AFTD.Kb.Tcs.G

/-!
# hypercube_max_coil_disjoint_squares_pos

Topic: combinatorics   Node: 9bd7b1d9d2a5

Provenance: helper lemma. arXiv:2610.36461 Corollary 3

For n ≥ 13, if S is a maximum coil in Q_n with degree count y_0 > 0, then the number F_5 of squares disjoint from S is strictly positive.
-/

def hmc363_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update x i (!x i)

theorem hmc363_flip_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : hmc363_flip (hmc363_flip x i) i = x := by
  funext t; simp only [hmc363_flip, Function.update_apply]; split_ifs <;> simp_all

theorem hmc363_flip_comm {n : ℕ} (x : Fin n → Bool) (i j : Fin n) :
    hmc363_flip (hmc363_flip x i) j = hmc363_flip (hmc363_flip x j) i := by
  by_cases hij : i = j
  · subst hij; rfl
  funext t
  simp only [hmc363_flip, Function.update_apply]
  by_cases hti : t = i
  · subst hti; simp [hij]
  · by_cases htj : t = j
    · subst htj; simp [hti, Ne.symm hij]
    · simp [hti, htj]

theorem hmc363_adj_iff {n : ℕ} (x y : Fin n → Bool) :
    (simple_graph_hypercube n).Adj x y ↔ x ≠ y ∧ ∃! k, x k ≠ y k := by
  unfold simple_graph_hypercube
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · obtain ⟨k, hk, hu⟩ := h
      exact ⟨hne, k, fun e => hk e.symm, fun t ht => hu t (fun e => ht e.symm)⟩
  · rintro ⟨hne, h⟩; exact ⟨hne, Or.inl h⟩

theorem hmc363_adj_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (simple_graph_hypercube n).Adj x (hmc363_flip x i) := by
  rw [hmc363_adj_iff]
  refine ⟨fun e => ?_, i, by simp [hmc363_flip], fun t ht => ?_⟩
  · have := congrFun e i; simp [hmc363_flip] at this
  · by_contra hti; exact ht (by simp [hmc363_flip, Function.update_apply, hti])

theorem hmc363_not_adj_double {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    ¬ (simple_graph_hypercube n).Adj x (hmc363_flip (hmc363_flip x i) j) := by
  rw [hmc363_adj_iff]
  rintro ⟨-, k, -, hu⟩
  have hi := hu i (by simp [hmc363_flip, Function.update_apply, hij])
  have hj := hu j (by simp [hmc363_flip, Function.update_apply, hij, Ne.symm hij])
  exact hij (hi.trans hj.symm)

theorem hmc363_eq_flip_of_adj {n : ℕ} {x y : Fin n → Bool} (h : (simple_graph_hypercube n).Adj x y) :
    ∃ k, y = hmc363_flip x k := by
  rw [hmc363_adj_iff] at h
  obtain ⟨-, k, hk, hu⟩ := h
  refine ⟨k, funext fun t => ?_⟩
  by_cases htk : t = k
  · subst htk; simp only [hmc363_flip, Function.update_self]
    cases hx : x t <;> cases hy : y t <;> simp_all
  · simp only [hmc363_flip, Function.update_apply, htk, if_false]
    by_contra hne; exact htk (hu t (Ne.symm hne))

/-- A vertex of a cycle has a neighbour, and no three distinct neighbours. -/
theorem hmc363_cycle_nbrs {α : Type*} (H : SimpleGraph α) (m : ℕ) (f : H ≃g SimpleGraph.cycleGraph (m + 3))
    (v : α) : (∃ w, H.Adj v w) ∧ ∀ a b c, H.Adj v a → H.Adj v b → H.Adj v c → a = b ∨ a = c ∨ b = c := by
  have key : ∀ a, H.Adj v a → f a = f v - 1 ∨ f a = f v + 1 := by
    intro a ha
    have h' : (SimpleGraph.cycleGraph (m + 1 + 2)).Adj (f v) (f a) := f.map_adj_iff.mpr ha
    have : f a ∈ (SimpleGraph.cycleGraph (m + 1 + 2)).neighborSet (f v) := h'
    rw [SimpleGraph.cycleGraph_neighborSet] at this
    simpa using this
  refine ⟨⟨f.symm (f v + 1), ?_⟩, fun a b c ha hb hc => ?_⟩
  · rw [← f.map_adj_iff, RelIso.apply_symm_apply]
    show (SimpleGraph.cycleGraph (m + 1 + 2)).Adj _ _
    rw [SimpleGraph.cycleGraph_adj]; right; simp
  · rcases key a ha with h1 | h1 <;> rcases key b hb with h2 | h2 <;> rcases key c hc with h3 | h3
    all_goals first
      | exact Or.inl (f.injective (h1.trans h2.symm))
      | exact Or.inr (Or.inl (f.injective (h1.trans h3.symm)))
      | exact Or.inr (Or.inr (f.injective (h2.trans h3.symm)))

theorem hmc363_coil_nbrs {n : ℕ} {S : Finset (Fin n → Bool)} (hcoil : hypercube_coil n S)
    {x : Fin n → Bool} (hx : x ∈ S) :
    (∃ y ∈ S, (simple_graph_hypercube n).Adj x y) ∧
      ∀ a b c, a ∈ S → b ∈ S → c ∈ S → (simple_graph_hypercube n).Adj x a →
        (simple_graph_hypercube n).Adj x b → (simple_graph_hypercube n).Adj x c → a = b ∨ a = c ∨ b = c := by
  obtain ⟨h4, ⟨f⟩⟩ := hcoil
  have hm : S.card = (S.card - 3) + 3 := by omega
  rw [hm] at f
  obtain ⟨⟨⟨y, hy⟩, hxy⟩, h2⟩ := hmc363_cycle_nbrs _ _ f ⟨x, hx⟩
  refine ⟨⟨y, hy, hxy⟩, fun a b c ha hb hc hxa hxb hxc => ?_⟩
  rcases h2 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hxa hxb hxc with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

theorem hmc363_flip_ne {n : ℕ} (z : Fin n → Bool) {p q : Fin n} (hpq : p ≠ q) :
    hmc363_flip z p ≠ hmc363_flip z q := by
  intro h
  have := congrFun h p
  simp [hmc363_flip, Function.update_apply, hpq] at this

def hmc363_pt {n : ℕ} (v : Fin n → Bool) (i j : Fin n) : Fin 4 → (Fin n → Bool) :=
  ![v, hmc363_flip v i, hmc363_flip (hmc363_flip v i) j, hmc363_flip v j]

theorem hmc363_pt_adj_iff {n : ℕ} (v : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) (a b : Fin 4) :
    (simple_graph_hypercube n).Adj (hmc363_pt v i j a) (hmc363_pt v i j b) ↔
      (SimpleGraph.cycleGraph 4).Adj a b := by
  have h01 := hmc363_adj_flip v i
  have h12 := hmc363_adj_flip (hmc363_flip v i) j
  have h23 : (simple_graph_hypercube n).Adj (hmc363_flip (hmc363_flip v i) j) (hmc363_flip v j) := by
    rw [hmc363_flip_comm]; exact (hmc363_adj_flip (hmc363_flip v j) i).symm
  have h30 := (hmc363_adj_flip v j).symm
  have h02 := hmc363_not_adj_double v hij
  have h13 : ¬ (simple_graph_hypercube n).Adj (hmc363_flip v i) (hmc363_flip v j) := by
    have := hmc363_not_adj_double (hmc363_flip v i) hij
    rwa [hmc363_flip_flip] at this
  have h10 := h01.symm
  have h21 := h12.symm
  have h32 := h23.symm
  have h03 := h30.symm
  have h20 : ¬ (simple_graph_hypercube n).Adj _ _ := fun h => h02 h.symm
  have h31 : ¬ (simple_graph_hypercube n).Adj _ _ := fun h => h13 h.symm
  fin_cases a <;> fin_cases b <;>
    simp [hmc363_pt, SimpleGraph.cycleGraph_adj', h01, h12, h23, h30, h02, h13, h10, h21, h32, h03, h20, h31] <;> decide

open scoped Classical in
/-- A maximum coil with y_0 > 0 has at least one disjoint square. -/
theorem hypercube_max_coil_disjoint_squares_pos (n : ℕ) (hn : 13 ≤ n) (S : Finset (Fin n → Bool))
    (hS : is_max_hypercube_coil n S) (hy0 : 0 < hypercube_degree_count n S 0) :
    0 < hypercube_disjoint_squares_count n S := by
  by_contra hF
  unfold hypercube_degree_count at hy0
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hy0
  rw [Finset.mem_filter, Finset.mem_sdiff] at hx
  have hxS : x ∉ S := hx.1.2
  have hN : ∀ y, (simple_graph_hypercube n).Adj x y → y ∉ S := by
    intro y hy hyS
    have h0 := Finset.card_eq_zero.mp hx.2
    rw [Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 y (by simp [hy, hyS])
  have step2 : ∀ i j : Fin n, i ≠ j → hmc363_flip (hmc363_flip x i) j ∈ S := by
    intro i j hij
    by_contra hnot
    apply hF
    have hinj : Function.Injective (hmc363_pt x i j) := by
      intro a b hab
      have hi := congrFun hab i
      have hj := congrFun hab j
      fin_cases a <;> fin_cases b <;>
        simp [hmc363_pt, hmc363_flip, Function.update_apply, hij, Ne.symm hij] at hi hj ⊢
    unfold hypercube_disjoint_squares_count
    apply Finset.card_pos.mpr
    refine ⟨Finset.univ.image (hmc363_pt x i j), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj]; simp
    · let e : Fin 4 ≃ ↥((Finset.univ.image (hmc363_pt x i j) : Finset _) : Set (Fin n → Bool)) :=
        Equiv.ofBijective (fun k => ⟨hmc363_pt x i j k, by simp⟩)
          ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun ⟨y, hy⟩ => by
            simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
            obtain ⟨k, rfl⟩ := hy
            exact ⟨k, rfl⟩⟩
      exact ⟨(⟨e, fun {a b} => hmc363_pt_adj_iff x hij a b⟩ :
        SimpleGraph.cycleGraph 4 ≃g (simple_graph_hypercube n).induce _).symm⟩
    · rw [Finset.disjoint_left]
      intro a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      fin_cases k
      · exact hxS
      · exact hN _ (hmc363_adj_flip x i)
      · exact hnot
      · exact hN _ (hmc363_adj_flip x j)
  have hi0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  set i : Fin n := ⟨0, by omega⟩
  set j : Fin n := ⟨1, by omega⟩
  obtain ⟨z, hzS, hyz⟩ := (hmc363_coil_nbrs hS.1 (step2 i j hi0)).1
  obtain ⟨k, rfl⟩ := hmc363_eq_flip_of_adj hyz
  have hki : k ≠ i := by
    rintro rfl
    apply hN _ (hmc363_adj_flip x j)
    rwa [hmc363_flip_comm (hmc363_flip x i) j i, hmc363_flip_flip] at hzS
  have hkj : k ≠ j := by
    rintro rfl
    apply hN _ (hmc363_adj_flip x i)
    rwa [hmc363_flip_flip] at hzS
  set z := hmc363_flip (hmc363_flip (hmc363_flip x i) j) k with hz
  have ha : hmc363_flip z k ∈ S := by rw [hz, hmc363_flip_flip]; exact step2 i j hi0
  have hb : hmc363_flip z i ∈ S := by
    rw [hz, hmc363_flip_comm (hmc363_flip (hmc363_flip x i) j) k i,
      hmc363_flip_comm (hmc363_flip x i) j i, hmc363_flip_flip]
    exact step2 j k (Ne.symm hkj)
  have hc : hmc363_flip z j ∈ S := by
    rw [hz, hmc363_flip_comm (hmc363_flip (hmc363_flip x i) j) k j, hmc363_flip_flip]
    exact step2 i k (Ne.symm hki)
  rcases (hmc363_coil_nbrs hS.1 hzS).2 _ _ _ ha hb hc (hmc363_adj_flip z k) (hmc363_adj_flip z i)
      (hmc363_adj_flip z j) with h | h | h
  · exact hmc363_flip_ne z hki h
  · exact hmc363_flip_ne z hkj h
  · exact hmc363_flip_ne z hi0 h
