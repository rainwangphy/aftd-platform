import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeGraph

/-!
# c4_free_hypercube_three_face_star_roots_card_le_one

Topic: graphs   Node: 08e6c5622e53

Provenance: formalization of a published result. Source: arXiv:2611.27284 (The four-cycle extremal number of the seven-cube), Lemma 2.2 (star capacity), first claim: each coordinate 3-face contains at most one full three-star rooted on a given parity side.

Let G be a subgraph of the n-dimensional hypercube Q_n (vertices {0,1}^n, adjacent at Hamming distance 1) containing no copy of the 4-cycle C_4. Fix three distinct coordinates i, j, k and a vertex w, and consider the coordinate 3-face F of vertices agreeing with w outside {i, j, k}. Fix a parity p (the number of coordinates equal to 1, mod 2). Then at most one vertex v of F of parity p is the root of a full three-star in F, that is, is G-adjacent to every vertex of F adjacent to v in Q_n.
-/

def c4hf_flip {n : ℕ} (a : Fin n → Bool) (c : Fin n) : Fin n → Bool :=
  fun l => if l = c then !a l else a l

theorem c4hf_adj_flip {n : ℕ} (a : Fin n → Bool) (c : Fin n) :
    (hypercube_graph n).Adj a (c4hf_flip a c) := by
  show hammingDist a (c4hf_flip a c) = 1
  unfold hammingDist
  have : (Finset.univ.filter fun l => a l ≠ c4hf_flip a c l) = {c} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, c4hf_flip]
    by_cases h : l = c
    · simp [h]
    · simp [h]
  rw [this, Finset.card_singleton]

theorem c4hf_flip_comm {n : ℕ} (a : Fin n → Bool) (c d : Fin n) (h : c ≠ d) :
    c4hf_flip (c4hf_flip a c) d = c4hf_flip (c4hf_flip a d) c := by
  funext l
  simp only [c4hf_flip]
  by_cases h1 : l = c <;> by_cases h2 : l = d <;> simp_all

theorem c4hf_parity_flip {n : ℕ} (a : Fin n → Bool) (c : Fin n) :
    (Finset.univ.filter fun l => c4hf_flip a c l = true).card % 2 ≠
      (Finset.univ.filter fun l => a l = true).card % 2 := by
  rw [Finset.card_filter, Finset.card_filter,
    Fintype.sum_eq_add_sum_compl c, Fintype.sum_eq_add_sum_compl c]
  have hrest : ∑ l ∈ ({c}ᶜ : Finset (Fin n)), (if c4hf_flip a c l = true then 1 else 0) =
      ∑ l ∈ ({c}ᶜ : Finset (Fin n)), (if a l = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    have : l ≠ c := by simpa using hl
    simp [c4hf_flip, this]
  rw [hrest]
  simp only [c4hf_flip, if_pos rfl]
  cases a c <;> simp <;> omega

open Classical in
theorem c4_free_hypercube_three_face_star_roots_card_le_one (n : ℕ)
    (G : SimpleGraph (Fin n → Bool)) (hG : G ≤ hypercube_graph n)
    (hC4 : (SimpleGraph.cycleGraph 4).Free G) (p : ℕ)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (w : Fin n → Bool) :
    (Finset.univ.filter fun v : Fin n → Bool =>
      (∀ l, l ≠ i → l ≠ j → l ≠ k → v l = w l) ∧
      (Finset.univ.filter fun l => v l = true).card % 2 = p ∧
      ∀ u : Fin n → Bool, (∀ l, l ≠ i → l ≠ j → l ≠ k → u l = w l) →
        (hypercube_graph n).Adj v u → G.Adj v u).card ≤ 1 := by
  have hji := hij.symm
  have hki := hik.symm
  have hkj := hjk.symm
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨haF, hap, har⟩ := ha
  obtain ⟨hbF, hbp, hbr⟩ := hb
  by_contra hab
  have hflipF : ∀ u : Fin n → Bool, (∀ l, l ≠ i → l ≠ j → l ≠ k → u l = w l) →
      ∀ c, (c = i ∨ c = j ∨ c = k) →
        (∀ l, l ≠ i → l ≠ j → l ≠ k → c4hf_flip u c l = w l) := by
    intro u hu c hc l h1 h2 h3
    have : l ≠ c := by rintro rfl; rcases hc with h | h | h <;> contradiction
    simp only [c4hf_flip, if_neg this]
    exact hu l h1 h2 h3
  have key : ∀ c d, c ≠ d → (c = i ∨ c = j ∨ c = k) → (d = i ∨ d = j ∨ d = k) →
      b = c4hf_flip (c4hf_flip a c) d → False := by
    intro c d hcd hc hd hb'
    have hxa : G.Adj a (c4hf_flip a c) :=
      har _ (hflipF a haF c hc) (c4hf_adj_flip a c)
    have hya : G.Adj a (c4hf_flip a d) :=
      har _ (hflipF a haF d hd) (c4hf_adj_flip a d)
    have hbx : G.Adj b (c4hf_flip a c) := by
      apply hbr _ (hflipF a haF c hc)
      rw [hb']
      exact (c4hf_adj_flip _ d).symm
    have hby : G.Adj b (c4hf_flip a d) := by
      apply hbr _ (hflipF a haF d hd)
      rw [hb', c4hf_flip_comm a c d hcd]
      exact (c4hf_adj_flip _ c).symm
    have hxy : c4hf_flip a c ≠ c4hf_flip a d := by
      intro h
      have := congrFun h c
      simp [c4hf_flip, hcd] at this
    have hxa' := hxa.ne
    have hya' := hya.ne
    have hbx' := hbx.ne
    have hby' := hby.ne
    apply hC4
    refine ⟨⟨⟨![a, c4hf_flip a c, b, c4hf_flip a d], ?_⟩, ?_⟩⟩
    · intro u v huv
      rw [SimpleGraph.cycleGraph_adj] at huv
      fin_cases u <;> fin_cases v <;> simp at huv <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val, Fin.isValue] <;>
        first
          | exact hxa | exact hxa.symm | exact hya | exact hya.symm
          | exact hbx | exact hbx.symm | exact hby | exact hby.symm
          | (exfalso; revert huv; decide)
    · intro u v huv
      change ![a, c4hf_flip a c, b, c4hf_flip a d] u =
        ![a, c4hf_flip a c, b, c4hf_flip a d] v at huv
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at huv <;>
        first
          | rfl
          | exact absurd huv hxa' | exact absurd huv.symm hxa'
          | exact absurd huv hya' | exact absurd huv.symm hya'
          | exact absurd huv hbx' | exact absurd huv.symm hbx'
          | exact absurd huv hby' | exact absurd huv.symm hby'
          | exact absurd huv hab | exact absurd huv.symm hab
          | exact absurd huv hxy | exact absurd huv.symm hxy
  have hout : ∀ l, l ≠ i → l ≠ j → l ≠ k → b l = a l :=
    fun l h1 h2 h3 => (hbF l h1 h2 h3).trans (haF l h1 h2 h3).symm
  have hpar1 : ∀ c, b = c4hf_flip a c → False := by
    intro c h
    exact c4hf_parity_flip a c (by rw [← h, hbp, hap])
  have hpar3 : b = c4hf_flip (c4hf_flip (c4hf_flip a i) j) k → False := by
    intro h
    have h1 := c4hf_parity_flip a i
    have h2 := c4hf_parity_flip (c4hf_flip a i) j
    have h3 := c4hf_parity_flip (c4hf_flip (c4hf_flip a i) j) k
    rw [← h, hbp] at h3
    rw [hap] at h1
    omega
  have bnot : ∀ x y : Bool, x ≠ y → x = !y := by decide
  by_cases ei : b i = a i <;> by_cases ej : b j = a j <;> by_cases ek : b k = a k
  · apply hab; funext l
    by_cases h1 : l = i
    · rw [h1, ei]
    by_cases h2 : l = j
    · rw [h2, ej]
    by_cases h3 : l = k
    · rw [h3, ek]
    exact (hout l h1 h2 h3).symm
  all_goals (try replace ei := bnot _ _ ei)
  all_goals (try replace ej := bnot _ _ ej)
  all_goals (try replace ek := bnot _ _ ek)
  all_goals
    first
    | (apply hpar1 i; funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply hpar1 j; funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply hpar1 k; funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply hpar3; funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply key i j hij (Or.inl rfl) (Or.inr (Or.inl rfl)); funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply key i k hik (Or.inl rfl) (Or.inr (Or.inr rfl)); funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
    | (apply key j k hjk (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)); funext l; simp only [c4hf_flip]; rcases eq_or_ne l i with h1 | h1; (rw [h1]; simp [ei, hij, hik, hji, hki]); rcases eq_or_ne l j with h2 | h2; (rw [h2]; simp [ej, hij, hjk, hji, hkj]); rcases eq_or_ne l k with h3 | h3; (rw [h3]; simp [ek, hik, hjk, hki, hkj]); simp [h1, h2, h3, hout l h1 h2 h3])
