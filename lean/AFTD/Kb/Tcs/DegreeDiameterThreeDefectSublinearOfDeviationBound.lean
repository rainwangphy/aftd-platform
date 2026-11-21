import AFTD.Prelude
import AFTD.Kb.Tcs.MooreBound
import AFTD.Kb.Tcs.CardLeMooreBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# degree_diameter_three_defect_sublinear_of_deviation_bound

Topic: graphs   Node: 1e4968a0c172

Provenance: helper lemma. arXiv:2611.26037, proof of Theorem 1.3 from Theorem 3.1 via Proposition 2.3(b)

Reduction of the diameter-3 defect bound to the deviation theorem: for d ≥ 3, if every finite nonempty d-regular graph satisfies d < (√8 r + 2)^2 whenever every row of C = A^3 + A^2 - 2(d-1)A - (d-1)I - J has absolute sum at most r, then every finite connected graph of maximum degree at most d and diameter at most 3 has fewer than m(d,3) - (√d - 2)/√8 vertices.
-/

/-- BFS from a root `v0`: a connected graph of maximum degree `d` and diameter at most `k`
has at most `1 + deg(v0) * ∑_{i<k} (d-1)^i` vertices. -/
theorem ddt3_card_le_root_degree (d k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hdiam : G.diam ≤ k) (hdeg : G.maxDegree ≤ d)
    (v0 : V) : Fintype.card V ≤ 1 + G.degree v0 * ∑ i ∈ Finset.range k, (d - 1) ^ i := by
  classical
  have : Nonempty V := ⟨v0⟩
  have hdist_le : ∀ v : V, G.dist v0 v ≤ k := fun v =>
    (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp hconn)).trans hdiam
  have hex : ∀ w : V, 1 ≤ G.dist v0 w → ∃ u : V, G.Adj u w ∧ G.dist v0 u = G.dist v0 w - 1 := by
    intro w hw
    obtain ⟨p, -, hp_len⟩ := hconn.exists_path_of_dist v0 w
    refine ⟨p.getVert (G.dist v0 w - 1), ?_, ?_⟩
    · have h1 : G.dist v0 w - 1 < p.length := by omega
      have hadj := p.adj_getVert_succ h1
      have h2 : p.getVert (G.dist v0 w - 1 + 1) = w := by
        rw [Nat.sub_add_cancel hw, ← hp_len, p.getVert_length]
      rwa [h2] at hadj
    · have h2 : (p.take (G.dist v0 w - 1)).length
          = G.dist v0 (p.getVert (G.dist v0 w - 1)) :=
        SimpleGraph.length_eq_dist_of_subwalk hp_len (p.isSubwalk_take _)
      rw [← h2, SimpleGraph.Walk.take_length, hp_len, min_eq_left (by omega)]
  let par : V → V := fun w =>
    if h : ∃ u : V, G.Adj u w ∧ G.dist v0 u = G.dist v0 w - 1 then Classical.choose h else w
  have par_spec : ∀ w : V, 1 ≤ G.dist v0 w →
      G.Adj (par w) w ∧ G.dist v0 (par w) = G.dist v0 w - 1 := by
    intro w hw
    have h := hex w hw
    have hpar : par w = Classical.choose h := by simp only [par, dif_pos h]
    rw [hpar]
    exact Classical.choose_spec h
  set L : ℕ → Finset V := fun i => Finset.univ.filter (fun v => G.dist v0 v = i) with hL
  have memL : ∀ (i : ℕ) (v : V), v ∈ L i ↔ G.dist v0 v = i := by
    intro i v; rw [hL]; simp
  have hL0 : L 0 = {v0} := by
    ext v; rw [memL]; simp [SimpleGraph.Connected.dist_eq_zero_iff hconn, eq_comm]
  have himage : ∀ j : ℕ, (Finset.image par (L (j+1))) ⊆ L j := by
    intro j b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [memL] at ha ⊢
    have hpos : 1 ≤ G.dist v0 a := by omega
    have := (par_spec a hpos).2
    omega
  have hfib0 : ∀ b : V, b ∈ L 0 →
      (Finset.filter (fun a => par a = b) (L 1)).card ≤ G.degree v0 := by
    intro b hb
    rw [hL0, Finset.mem_singleton] at hb
    have hsub : Finset.filter (fun a => par a = b) (L 1) ⊆ G.neighborFinset b := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨ha1, ha2⟩ := ha
      rw [SimpleGraph.mem_neighborFinset]
      rw [memL] at ha1
      have hpos : 1 ≤ G.dist v0 a := by omega
      have := (par_spec a hpos).1
      rwa [ha2] at this
    calc (Finset.filter (fun a => par a = b) (L 1)).card
        ≤ (G.neighborFinset b).card := Finset.card_le_card hsub
      _ = G.degree b := SimpleGraph.card_neighborFinset_eq_degree G b
      _ = G.degree v0 := by rw [hb]
  have hfib : ∀ (j : ℕ), 1 ≤ j → ∀ b : V, b ∈ L j →
      (Finset.filter (fun a => par a = b) (L (j+1))).card ≤ d - 1 := by
    intro j hj b hb
    have hbdist : G.dist v0 b = j := (memL j b).mp hb
    obtain ⟨hadj, hdist⟩ := par_spec b (by omega)
    have hsub : Finset.filter (fun a => par a = b) (L (j+1)) ⊆
        (G.neighborFinset b).erase (par b) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨halayer, hapar⟩ := ha
      rw [memL] at halayer
      have hpos : 1 ≤ G.dist v0 a := by omega
      have hadja : G.Adj (par a) a := (par_spec a hpos).1
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hEq
        have h1 : G.dist v0 a = G.dist v0 b - 1 := by rw [hEq]; exact hdist
        omega
      · rw [SimpleGraph.mem_neighborFinset]
        rwa [hapar] at hadja
    calc (Finset.filter (fun a => par a = b) (L (j+1))).card
        ≤ ((G.neighborFinset b).erase (par b)).card := Finset.card_le_card hsub
      _ = (G.neighborFinset b).card - 1 := Finset.card_erase_of_mem (by
            rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm)
      _ = G.degree b - 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ d - 1 := by
          have h1 := SimpleGraph.degree_le_maxDegree G b
          omega
  have hstep : ∀ (j : ℕ), 1 ≤ j → (L (j+1)).card ≤ (d - 1) * (L j).card := by
    intro j hj
    refine le_trans (Finset.card_le_mul_card_image (f := par) (L (j+1)) (d - 1) ?_) ?_
    · intro b hb
      exact hfib j hj b (himage j hb)
    · exact Nat.mul_le_mul_left _ (Finset.card_le_card (himage j))
  have hlayer : ∀ i : ℕ, (L (i+1)).card ≤ G.degree v0 * (d - 1)^i := by
    intro i
    induction i with
    | zero =>
        have h1 : (L 1).card ≤ G.degree v0 * (Finset.image par (L 1)).card :=
          Finset.card_le_mul_card_image (f := par) (L 1) (G.degree v0)
            (fun b hb => hfib0 b (himage 0 hb))
        have h2 : (Finset.image par (L 1)).card ≤ 1 := by
          calc (Finset.image par (L 1)).card ≤ (L 0).card := Finset.card_le_card (himage 0)
            _ = 1 := by rw [hL0]; simp
        calc (L (0+1)).card = (L 1).card := rfl
          _ ≤ G.degree v0 * (Finset.image par (L 1)).card := h1
          _ ≤ G.degree v0 * 1 := Nat.mul_le_mul_left _ h2
          _ = G.degree v0 * (d - 1)^0 := by simp
    | succ i ih =>
        calc (L (i+1+1)).card ≤ (d - 1) * (L (i+1)).card := hstep (i+1) (by omega)
          _ ≤ (d - 1) * (G.degree v0 * (d - 1)^i) := Nat.mul_le_mul_left _ ih
          _ = G.degree v0 * (d - 1)^(i+1) := by rw [pow_succ]; ring
  have hsum_le : ∑ i ∈ Finset.range k, (L (i+1)).card
      ≤ G.degree v0 * ∑ i ∈ Finset.range k, (d - 1)^i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hlayer i)
  have hcover : ∀ v ∈ (Finset.univ : Finset V), G.dist v0 v ∈ Finset.range (k+1) :=
    fun v _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hdist_le v))
  have hcard : Fintype.card V = ∑ i ∈ Finset.range (k+1), (L i).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
      (t := Finset.range (k+1)) (f := fun v : V => G.dist v0 v) hcover
    simpa [hL] using h
  rw [hcard, Finset.sum_range_succ']
  rw [hL0, Finset.card_singleton]
  have := hsum_le
  omega

/-- Row sums of `M * A` for a `d`-regular graph. -/
theorem ddt3_rowsum_mul_adj {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hreg : G.IsRegularOfDegree d) (M : Matrix V V ℤ) (u : V) :
    ∑ v, (M * G.adjMatrix ℤ) u v = (d : ℤ) * ∑ v, M u v := by
  simp only [Matrix.mul_apply, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hsum : ∑ v, (if G.Adj b v then (1 : ℤ) else 0) = d := by
    rw [Finset.sum_boole]
    have : (Finset.univ.filter (fun v => G.Adj b v)) = G.neighborFinset b := by
      ext v; simp
    rw [this, SimpleGraph.card_neighborFinset_eq_degree, hreg b]
  rw [← Finset.mul_sum, hsum]
  ring

theorem degree_diameter_three_defect_sublinear_of_deviation_bound (d : ℕ) (hd : 3 ≤ d)
    (h31 : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Nonempty W → H.IsRegularOfDegree d → ∀ r : ℝ,
      (∀ u : W, ((∑ v : W, |((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2
          - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ - ((d : ℤ) - 1) • (1 : Matrix W W ℤ)
          - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v| : ℤ) : ℝ) ≤ r) →
      (d : ℝ) < (Real.sqrt 8 * r + 2) ^ 2)
    (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdiam : G.diam ≤ 3) (hdeg : G.maxDegree ≤ d) :
    (Fintype.card V : ℝ) < (moore_bound d 3 : ℝ) - (Real.sqrt (d : ℝ) - 2) / Real.sqrt 8 := by
  classical
  obtain ⟨v0⟩ := hconn.2
  have : Nonempty V := ⟨v0⟩
  set n := Fintype.card V with hn
  set S := ∑ i ∈ Finset.range 3, (d - 1) ^ i with hS
  have hm : moore_bound d 3 = 1 + d * S := rfl
  have hnm : n ≤ moore_bound d 3 := card_le_moore_bound d 3 V G hconn hdiam hdeg
  have hS_eq : S = 1 + (d - 1) + (d - 1) ^ 2 := by
    rw [hS]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  have h8pos : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have h8ge1 : 1 ≤ Real.sqrt 8 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hsd0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  -- reduce to a bound on the defect f = m - n
  suffices hf : (Real.sqrt (d : ℝ) - 2) / Real.sqrt 8 < (moore_bound d 3 : ℝ) - n by linarith
  by_cases hbig : n + S ≤ moore_bound d 3
  · -- large defect
    have hdS : d ≤ S := by
      rw [hS_eq]
      omega
    have hcast : ((d : ℕ) : ℝ) ≤ (moore_bound d 3 : ℝ) - n := by
      have : d + n ≤ moore_bound d 3 := by omega
      have : ((d + n : ℕ) : ℝ) ≤ (moore_bound d 3 : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hsqd : Real.sqrt (d : ℝ) ≤ d := by
      have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      have h2 : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
      have h3 : 1 ≤ Real.sqrt (d : ℝ) := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
      nlinarith
    have hf0' : (0 : ℝ) ≤ (moore_bound d 3 : ℝ) - n := le_trans (Nat.cast_nonneg d) hcast
    have hm8 := mul_le_mul_of_nonneg_left h8ge1 hf0'
    rw [div_lt_iff₀ h8pos]
    linarith
  · -- small defect: G is d-regular
    push_neg at hbig
    have hreg : G.IsRegularOfDegree d := by
      intro v
      have hle : G.degree v ≤ d := (G.degree_le_maxDegree v).trans hdeg
      by_contra hne
      have hlt : G.degree v ≤ d - 1 := by omega
      have hc := ddt3_card_le_root_degree d 3 V G hconn hdiam hdeg v
      rw [← hS, ← hn] at hc
      have h1 : G.degree v * S ≤ (d - 1) * S := Nat.mul_le_mul_right _ hlt
      have h2 : (d - 1) * S + S = d * S := by
        have : d = (d - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      omega
    set A := G.adjMatrix ℤ with hA
    set C : Matrix V V ℤ := A ^ 3 + A ^ 2 - (2 * ((d : ℤ) - 1)) • A
      - ((d : ℤ) - 1) • (1 : Matrix V V ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) with hC
    have hA_nonneg : ∀ u v, 0 ≤ A u v := by
      intro u v; rw [hA, SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
    have hA2 : ∀ u v, (A ^ 2) u v = ∑ w, A u w * A w v := by
      intro u v; rw [pow_two, Matrix.mul_apply]
    have hA2_nonneg : ∀ u v, 0 ≤ (A ^ 2) u v := by
      intro u v; rw [hA2]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (hA_nonneg u w) (hA_nonneg w v))
    have hA3 : ∀ u v, (A ^ 3) u v = ∑ w ∈ G.neighborFinset v, (A ^ 2) u w := by
      intro u v
      rw [show A ^ 3 = A ^ 2 * A from pow_succ A 2, hA, SimpleGraph.mul_adjMatrix_apply]
    have hA3_nonneg : ∀ u v, 0 ≤ (A ^ 3) u v := by
      intro u v; rw [hA3]; exact Finset.sum_nonneg (fun w _ => hA2_nonneg u w)
    have hA2_ge : ∀ u w v, G.Adj u w → G.Adj w v → 1 ≤ (A ^ 2) u v := by
      intro u w v huw hwv
      rw [hA2]
      have : A u w * A w v = 1 := by
        rw [hA, SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply, if_pos huw, if_pos hwv]
        norm_num
      rw [← this]
      exact Finset.single_le_sum (f := fun x => A u x * A x v)
        (fun x _ => mul_nonneg (hA_nonneg u x) (hA_nonneg x v)) (Finset.mem_univ w)
    have hA2_self : ∀ u, (A ^ 2) u u = d := by
      intro u
      rw [pow_two, hA, SimpleGraph.adjMatrix_mul_self_apply_self, hreg u]
    have hA3_ge : ∀ u w x v, G.Adj u w → G.Adj w x → G.Adj x v → 1 ≤ (A ^ 3) u v := by
      intro u w x v h1 h2 h3
      rw [hA3]
      have hx : x ∈ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]; exact h3.symm
      calc (1 : ℤ) ≤ (A ^ 2) u x := hA2_ge u w x h1 h2
        _ ≤ ∑ w ∈ G.neighborFinset v, (A ^ 2) u w :=
          Finset.single_le_sum (f := fun y => (A ^ 2) u y) (fun y _ => hA2_nonneg u y) hx
    have hA3_adj : ∀ u v, G.Adj u v → 2 * (d : ℤ) - 1 ≤ (A ^ 3) u v := by
      intro u v huv
      rw [hA3]
      have hu : u ∈ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]; exact huv.symm
      rw [← Finset.add_sum_erase _ _ hu, hA2_self]
      have hrest : ((d : ℤ) - 1) ≤ ∑ w ∈ (G.neighborFinset v).erase u, (A ^ 2) u w := by
        have hcard : ((G.neighborFinset v).erase u).card = d - 1 := by
          rw [Finset.card_erase_of_mem hu, SimpleGraph.card_neighborFinset_eq_degree, hreg v]
        have : ∑ w ∈ (G.neighborFinset v).erase u, (1 : ℤ) ≤
            ∑ w ∈ (G.neighborFinset v).erase u, (A ^ 2) u w := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
          exact hA2_ge u v w huv hw.2
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at this
        have hd1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hd1] at this
        exact this
      linarith
    have hdistle : ∀ u v, G.dist u v ≤ 3 := fun u v =>
      (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp hconn)).trans hdiam
    have hC_nonneg : ∀ u v, 0 ≤ C u v := by
      intro u v
      have hCuv : C u v = (A ^ 3) u v + (A ^ 2) u v - 2 * ((d : ℤ) - 1) * A u v
          - ((d : ℤ) - 1) * (if u = v then 1 else 0) - 1 := by
        rw [hC]
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.of_apply, smul_eq_mul]
      rw [hCuv]
      obtain ⟨p, hp⟩ := (hconn.preconnected u v).exists_walk_length_eq_dist
      have hle := hdistle u v
      by_cases huv : u = v
      · subst huv
        have h0 : A u u = 0 := by rw [hA, SimpleGraph.adjMatrix_apply]; simp
        rw [h0, hA2_self, if_pos rfl]
        have := hA3_nonneg u u
        linarith
      have h1 : A u v = if G.Adj u v then 1 else 0 := by rw [hA, SimpleGraph.adjMatrix_apply]
      by_cases hadj : G.Adj u v
      · rw [h1, if_pos hadj, if_neg huv]
        have := hA3_adj u v hadj
        have := hA2_nonneg u v
        linarith
      rw [h1, if_neg hadj, if_neg huv]
      have hd0 : G.dist u v ≠ 0 := by
        intro h0
        exact huv ((hconn.dist_eq_zero_iff).mp h0)
      have hd1 : G.dist u v ≠ 1 := by
        intro h1'; exact hadj (SimpleGraph.dist_eq_one_iff_adj.mp h1')
      have h2or3 : G.dist u v = 2 ∨ G.dist u v = 3 := by omega
      rcases h2or3 with h2 | h3
      · have hlen : p.length = 2 := by rw [hp, h2]
        have a1 := p.adj_getVert_succ (i := 0) (by omega)
        have a2 := p.adj_getVert_succ (i := 1) (by omega)
        simp only [SimpleGraph.Walk.getVert_zero, zero_add] at a1
        have e2 : p.getVert 2 = v := by rw [← hlen, p.getVert_length]
        rw [show 1 + 1 = 2 from rfl, e2] at a2
        have := hA2_ge u _ v a1 a2
        have := hA3_nonneg u v
        linarith
      · have hlen : p.length = 3 := by rw [hp, h3]
        have a1 := p.adj_getVert_succ (i := 0) (by omega)
        have a2 := p.adj_getVert_succ (i := 1) (by omega)
        have a3 := p.adj_getVert_succ (i := 2) (by omega)
        simp only [SimpleGraph.Walk.getVert_zero, zero_add] at a1
        rw [show 1 + 1 = 2 from rfl] at a2
        have e3 : p.getVert 3 = v := by rw [← hlen, p.getVert_length]
        rw [show 2 + 1 = 3 from rfl, e3] at a3
        have := hA3_ge u _ _ v a1 a2 a3
        have := hA2_nonneg u v
        linarith
    -- row sums of C
    have hrowA : ∀ u, ∑ v, A u v = d := by
      intro u
      have := ddt3_rowsum_mul_adj G d hreg 1 u
      rw [one_mul] at this
      rw [this]; simp [Matrix.one_apply]
    have hrowA2 : ∀ u, ∑ v, (A ^ 2) u v = (d : ℤ) ^ 2 := by
      intro u
      rw [pow_two, hA, ddt3_rowsum_mul_adj G d hreg, ← hA, hrowA u]; ring
    have hrowA3 : ∀ u, ∑ v, (A ^ 3) u v = (d : ℤ) ^ 3 := by
      intro u
      rw [show A ^ 3 = A ^ 2 * A from pow_succ A 2, hA, ddt3_rowsum_mul_adj G d hreg, ← hA,
        hrowA2 u]
      ring
    have hmZ : ((moore_bound d 3 : ℕ) : ℤ) = (d : ℤ) ^ 3 - (d : ℤ) ^ 2 + d + 1 := by
      rw [hm, hS_eq]
      push_cast [Nat.cast_sub (show 1 ≤ d by omega)]
      ring
    have hrowC : ∀ u, ∑ v, C u v = (moore_bound d 3 : ℤ) - n := by
      intro u
      have hCuv : ∀ v, C u v = (A ^ 3) u v + (A ^ 2) u v - 2 * ((d : ℤ) - 1) * A u v
          - ((d : ℤ) - 1) * (if u = v then 1 else 0) - 1 := by
        intro v
        rw [hC]
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.of_apply, smul_eq_mul]
      simp only [hCuv, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hrowA3, hrowA2, hrowA, Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const,
        Finset.card_univ, ← hn, nsmul_eq_mul, mul_one, hmZ, ↓reduceIte]
      ring
    have hr : ∀ u, ((∑ v, |C u v| : ℤ) : ℝ) ≤ (moore_bound d 3 : ℝ) - n := by
      intro u
      have : ∑ v, |C u v| = ∑ v, C u v :=
        Finset.sum_congr rfl (fun v _ => abs_of_nonneg (hC_nonneg u v))
      rw [this, hrowC u]
      exact le_of_eq (by norm_cast)
    have key := h31 V G ⟨v0⟩ hreg ((moore_bound d 3 : ℝ) - n) hr
    have hf0 : (0 : ℝ) ≤ (moore_bound d 3 : ℝ) - n := by
      have : (n : ℝ) ≤ moore_bound d 3 := by exact_mod_cast hnm
      linarith
    have hpos : 0 ≤ Real.sqrt 8 * ((moore_bound d 3 : ℝ) - n) + 2 := by
      have := mul_nonneg h8pos.le hf0
      linarith
    have hsq : Real.sqrt (d : ℝ) < Real.sqrt 8 * ((moore_bound d 3 : ℝ) - n) + 2 := by
      rw [← Real.sqrt_sq hpos]
      exact Real.sqrt_lt_sqrt (by positivity) key
    rw [div_lt_iff₀ h8pos]
    linarith
