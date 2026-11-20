import AFTD.Prelude
import AFTD.Kb.Tcs.MooreBound

/-!
# card_le_moore_bound

Topic: graphs   Node: 88140ce649ba

Provenance: formalization of a published result. Source: arXiv:2611.26037 Sec. 1

Every finite connected simple graph with maximum degree at most d and diameter at most k has at most m(d, k) vertices.
-/

private lemma card_le_moore_bound_dist_le_diam (V : Type) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hconn : G.Connected) (u v : V) : G.dist u v ≤ G.diam :=
  SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp hconn)

/-- The classical Moore bound: every finite connected simple graph of maximum degree at most d and diameter at most k has at most m(d, k) vertices. -/
theorem card_le_moore_bound (d k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hdiam : G.diam ≤ k) (hdeg : G.maxDegree ≤ d) : Fintype.card V ≤ moore_bound d k := by
  classical
  obtain ⟨v0⟩ := hconn.2
  have hdist_le : ∀ v : V, G.dist v0 v ≤ k := fun v =>
    (@card_le_moore_bound_dist_le_diam V _ ⟨v0⟩ G hconn v0 v).trans hdiam
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
  have hfib0 : ∀ b : V, b ∈ L 0 → (Finset.filter (fun a => par a = b) (L 1)).card ≤ d := by
    intro b hb
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
      _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G b
      _ ≤ d := hdeg
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
  have hlayer : ∀ i : ℕ, (L (i+1)).card ≤ d * (d - 1)^i := by
    intro i
    induction i with
    | zero =>
        have h1 : (L 1).card ≤ d * (Finset.image par (L 1)).card :=
          Finset.card_le_mul_card_image (f := par) (L 1) d (fun b hb => hfib0 b (himage 0 hb))
        have h2 : (Finset.image par (L 1)).card ≤ 1 := by
          calc (Finset.image par (L 1)).card ≤ (L 0).card := Finset.card_le_card (himage 0)
            _ = 1 := by rw [hL0]; simp
        calc (L (0+1)).card = (L 1).card := rfl
          _ ≤ d * (Finset.image par (L 1)).card := h1
          _ ≤ d * 1 := Nat.mul_le_mul_left _ h2
          _ = d * (d - 1)^0 := by simp
    | succ i ih =>
        calc (L (i+1+1)).card ≤ (d - 1) * (L (i+1)).card := hstep (i+1) (by omega)
          _ ≤ (d - 1) * (d * (d - 1)^i) := Nat.mul_le_mul_left _ ih
          _ = d * (d - 1)^(i+1) := by rw [pow_succ]; ring
  have hsum_le : ∑ i ∈ Finset.range k, (L (i+1)).card ≤ d * ∑ i ∈ Finset.range k, (d - 1)^i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hlayer i)
  have hcover : ∀ v ∈ (Finset.univ : Finset V), G.dist v0 v ∈ Finset.range (k+1) :=
    fun v _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hdist_le v))
  have hcard : Fintype.card V = ∑ i ∈ Finset.range (k+1), (L i).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset V))
      (t := Finset.range (k+1)) (f := fun v : V => G.dist v0 v) hcover
    simpa [hL] using h
  rw [hcard, Finset.sum_range_succ']
  calc (∑ i ∈ Finset.range k, (L (i + 1)).card) + (L 0).card
      ≤ d * (∑ i ∈ Finset.range k, (d - 1)^i) + 1 := by
        rw [hL0, Finset.card_singleton]
        exact Nat.add_le_add_right hsum_le 1
    _ = moore_bound d k := by rw [moore_bound, Nat.add_comm]
