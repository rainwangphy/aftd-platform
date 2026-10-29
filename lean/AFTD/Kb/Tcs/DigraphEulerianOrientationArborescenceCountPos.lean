import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsEulerianOrientation
import AFTD.Kb.Tcs.DigraphArborescenceCountAt
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_eulerian_orientation_arborescence_count_pos

Topic: graphs   Node: 326ac85774e4

Provenance: helper lemma. step towards three_connected_plane_eulerian_minimizer_is_alternating

An Eulerian orientation D of a finite connected simple graph is strongly connected, so for every root r it has at least one spanning arborescence directed towards r: a_r(D) > 0.
-/

private theorem digraph_eulerian_orientation_arborescence_count_pos_flux {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (hbal : ∀ v, (Finset.univ.filter (fun w => D.Adj v w)).card = (Finset.univ.filter (fun w => D.Adj w v)).card)
    (S : Finset (Fin n)) :
    (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), (if D.Adj v w then 1 else 0))
      = ∑ w ∈ (Finset.univ \ S), ∑ v ∈ S, (if D.Adj w v then 1 else 0) := by
  set f : Fin n → Fin n → ℕ := fun a b => if D.Adj a b then 1 else 0 with hf
  have hcard : ∀ v, ∑ w ∈ Finset.univ, f v w = ∑ w ∈ Finset.univ, f w v := by
    intro v
    simp only [hf]
    rw [← Finset.card_filter (fun w => D.Adj v w), ← Finset.card_filter (fun w => D.Adj w v)]
    exact hbal v
  have h1 : (∑ v ∈ S, ∑ w ∈ Finset.univ, f v w) = (∑ v ∈ S, ∑ w ∈ Finset.univ, f w v) :=
    Finset.sum_congr rfl (fun v _ => hcard v)
  have hA : (∑ v ∈ S, ∑ w ∈ Finset.univ, f v w) =
      (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), f v w) + (∑ v ∈ S, ∑ w ∈ S, f v w) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hB : (∑ v ∈ S, ∑ w ∈ Finset.univ, f w v) =
      (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), f w v) + (∑ v ∈ S, ∑ w ∈ S, f w v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hcomm : (∑ v ∈ S, ∑ w ∈ S, f v w) = (∑ v ∈ S, ∑ w ∈ S, f w v) := by
    rw [Finset.sum_comm]
  have hout : (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), f v w)
      = (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), f w v) := by
    rw [hA, hB, hcomm] at h1
    omega
  rw [hout, Finset.sum_comm]

private theorem digraph_eulerian_orientation_arborescence_count_pos_strong {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (hG : G.Connected) (hD : digraph_is_eulerian_orientation G D) (r : Fin n) :
    ∀ v, Relation.ReflTransGen D.Adj v r := by
  classical
  obtain ⟨hori, hbal⟩ := hD
  rw [is_graph_orientation] at hori
  obtain ⟨hori1, -⟩ := hori
  let S : Finset (Fin n) := Finset.univ.filter (fun v => Relation.ReflTransGen D.Adj v r)
  have hmemS : ∀ v, v ∈ S ↔ Relation.ReflTransGen D.Adj v r := by
    intro v; simp [S]
  have hNoIn : ∀ w ∈ Finset.univ \ S, ∀ v ∈ S, ¬ D.Adj w v := by
    intro w hw v hv hadj
    have hwS : w ∈ S := (hmemS w).mpr (Relation.ReflTransGen.head hadj ((hmemS v).mp hv))
    exact (Finset.mem_sdiff.mp hw).2 hwS
  have hflux := digraph_eulerian_orientation_arborescence_count_pos_flux D hbal S
  have hzeroR : (∑ w ∈ (Finset.univ \ S), ∑ v ∈ S, (if D.Adj w v then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    apply Finset.sum_eq_zero
    intro v hv
    rw [if_neg (hNoIn w hw v hv)]
  have hzeroL : (∑ v ∈ S, ∑ w ∈ (Finset.univ \ S), (if D.Adj v w then 1 else 0)) = 0 := by
    rw [hflux, hzeroR]
  have hNoOut : ∀ v ∈ S, ∀ w ∈ Finset.univ \ S, ¬ D.Adj v w := by
    intro v hv w hw hadj
    have h1 : (∑ w ∈ (Finset.univ \ S), (if D.Adj v w then 1 else 0)) = 0 :=
      Finset.sum_eq_zero_iff.mp hzeroL v hv
    have h2 : (if D.Adj v w then 1 else 0) = 0 := Finset.sum_eq_zero_iff.mp h1 w hw
    rw [if_pos hadj] at h2
    exact Nat.one_ne_zero h2
  have hclosure : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S := by
    intro a ha b hab
    rcases (hori1 a b).mpr hab with hab' | hba
    · by_contra hb
      exact hNoOut a ha b (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩) hab'
    · by_contra hb
      exact hNoIn b (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩) a ha hba
  have hRT : ∀ a b, Relation.ReflTransGen G.Adj a b → a ∈ S → b ∈ S := by
    intro a b h
    induction h with
    | refl => exact fun h => h
    | tail _ hbc ih => exact fun ha => hclosure _ (ih ha) _ hbc
  intro v
  rw [← hmemS]
  apply hRT r v
  · rw [← SimpleGraph.reachable_eq_reflTransGen]; exact hG.preconnected r v
  · exact (hmemS r).mpr Relation.ReflTransGen.refl

private def digraph_eulerian_orientation_arborescence_count_pos_reachK {V : Type*} (R : V → V → Prop) :
    ℕ → V → V → Prop
  | 0 => fun a b => a = b
  | k + 1 => fun a b => ∃ c, R a c ∧ digraph_eulerian_orientation_arborescence_count_pos_reachK R k c b

private lemma digraph_eulerian_orientation_arborescence_count_pos_reachK_succ_iff {V : Type*} {R : V → V → Prop}
    {k : ℕ} {a b : V} :
    digraph_eulerian_orientation_arborescence_count_pos_reachK R (k+1) a b ↔
      ∃ c, R a c ∧ digraph_eulerian_orientation_arborescence_count_pos_reachK R k c b := Iff.rfl

private lemma digraph_eulerian_orientation_arborescence_count_pos_reachK_snoc {V : Type*} {R : V → V → Prop} :
    ∀ {k : ℕ} {a b c : V},
      digraph_eulerian_orientation_arborescence_count_pos_reachK R k a b → R b c →
      digraph_eulerian_orientation_arborescence_count_pos_reachK R (k+1) a c
  | 0, a, b, c, hab, hbc => by
      simp only [digraph_eulerian_orientation_arborescence_count_pos_reachK] at hab ⊢
      subst hab
      exact ⟨c, hbc, rfl⟩
  | k+1, a, b, c, hab, hbc => by
      rw [digraph_eulerian_orientation_arborescence_count_pos_reachK_succ_iff] at hab ⊢
      obtain ⟨u, hau, hub⟩ := hab
      exact ⟨u, hau, digraph_eulerian_orientation_arborescence_count_pos_reachK_snoc hub hbc⟩

private lemma digraph_eulerian_orientation_arborescence_count_pos_exists_reachK {V : Type*} {R : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen R a b) :
    ∃ k, digraph_eulerian_orientation_arborescence_count_pos_reachK R k a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k+1, digraph_eulerian_orientation_arborescence_count_pos_reachK_snoc hk hbc⟩

private noncomputable def digraph_eulerian_orientation_arborescence_count_pos_layer {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ j ≤ k, digraph_eulerian_orientation_arborescence_count_pos_reachK D.Adj j v r)

private noncomputable def digraph_eulerian_orientation_arborescence_count_pos_newLayer {n : ℕ}
    (D : Digraph (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ u ∈ S, D.Adj v u)

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_mem {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) (k : ℕ) (v : Fin n) :
    v ∈ digraph_eulerian_orientation_arborescence_count_pos_layer D r k ↔
      ∃ j ≤ k, digraph_eulerian_orientation_arborescence_count_pos_reachK D.Adj j v r := by
  classical
  simp [digraph_eulerian_orientation_arborescence_count_pos_layer]

private lemma digraph_eulerian_orientation_arborescence_count_pos_newLayer_mem {n : ℕ}
    (D : Digraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    v ∈ digraph_eulerian_orientation_arborescence_count_pos_newLayer D S ↔ ∃ u ∈ S, D.Adj v u := by
  classical
  simp [digraph_eulerian_orientation_arborescence_count_pos_newLayer]

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_zero {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) :
    digraph_eulerian_orientation_arborescence_count_pos_layer D r 0 = {r} := by
  classical
  ext v
  rw [digraph_eulerian_orientation_arborescence_count_pos_layer_mem]
  simp only [Nat.le_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, hk⟩
    subst hj
    simpa [digraph_eulerian_orientation_arborescence_count_pos_reachK] using hk
  · rintro rfl
    exact ⟨0, rfl, rfl⟩

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_mono {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) (k : ℕ) :
    digraph_eulerian_orientation_arborescence_count_pos_layer D r k ⊆
      digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1) := by
  classical
  intro v hv
  rw [digraph_eulerian_orientation_arborescence_count_pos_layer_mem] at hv ⊢
  obtain ⟨j, hj, hk⟩ := hv
  exact ⟨j, Nat.le_succ_of_le hj, hk⟩

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_step {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) (k : ℕ) :
    digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1) =
      digraph_eulerian_orientation_arborescence_count_pos_layer D r k ∪
        digraph_eulerian_orientation_arborescence_count_pos_newLayer D
          (digraph_eulerian_orientation_arborescence_count_pos_layer D r k) := by
  classical
  ext v
  simp only [digraph_eulerian_orientation_arborescence_count_pos_layer_mem,
    digraph_eulerian_orientation_arborescence_count_pos_newLayer_mem, Finset.mem_union]
  constructor
  · rintro ⟨j, hj, hk⟩
    rcases Nat.lt_or_ge j (k+1) with hlt | hge
    · left; exact ⟨j, Nat.lt_succ_iff.mp hlt, hk⟩
    · right
      have hj' : j = k+1 := by omega
      subst hj'
      rw [digraph_eulerian_orientation_arborescence_count_pos_reachK_succ_iff] at hk
      obtain ⟨u, hvu, huk⟩ := hk
      exact ⟨u, ⟨k, le_refl k, huk⟩, hvu⟩
  · rintro (⟨j, hj, hk⟩ | ⟨u, hu, hvu⟩)
    · exact ⟨j, Nat.le_trans hj (Nat.le_succ k), hk⟩
    · obtain ⟨j, hj, huk⟩ := hu
      exact ⟨j+1, by omega, by
        rw [digraph_eulerian_orientation_arborescence_count_pos_reachK_succ_iff]
        exact ⟨u, hvu, huk⟩⟩

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_mono_iter {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) :
    ∀ {j k : ℕ}, j ≤ k →
      digraph_eulerian_orientation_arborescence_count_pos_layer D r j ⊆
        digraph_eulerian_orientation_arborescence_count_pos_layer D r k := by
  intro j k hjk
  induction hjk with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact Finset.Subset.trans ih (digraph_eulerian_orientation_arborescence_count_pos_layer_mono D r _)

private lemma digraph_eulerian_orientation_arborescence_count_pos_layer_stab {n : ℕ}
    (D : Digraph (Fin n)) (r : Fin n) {k : ℕ}
    (hk : digraph_eulerian_orientation_arborescence_count_pos_layer D r k =
      digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1)) :
    ∀ m, digraph_eulerian_orientation_arborescence_count_pos_layer D r (k + m) =
      digraph_eulerian_orientation_arborescence_count_pos_layer D r k := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show k + (m+1) = (k+m)+1 by omega,
        digraph_eulerian_orientation_arborescence_count_pos_layer_step, ih]
      have h1 : digraph_eulerian_orientation_arborescence_count_pos_newLayer D
          (digraph_eulerian_orientation_arborescence_count_pos_layer D r k) ⊆
          digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1) := by
        rw [digraph_eulerian_orientation_arborescence_count_pos_layer_step]
        exact Finset.subset_union_right
      rw [← hk] at h1
      exact Finset.union_eq_left.mpr h1

/-- A connected graph with an Eulerian orientation has a positive number of arborescences towards every root. -/
theorem digraph_eulerian_orientation_arborescence_count_pos {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (hG : G.Connected) (hD : digraph_is_eulerian_orientation G D) (r : Fin n) :
    0 < digraph_arborescence_count_at D r := by
  classical
  have hstrong : ∀ v, Relation.ReflTransGen D.Adj v r :=
    digraph_eulerian_orientation_arborescence_count_pos_strong G D hG hD r
  have huniv : ∀ v, ∃ k, v ∈ digraph_eulerian_orientation_arborescence_count_pos_layer D r k := by
    intro v
    obtain ⟨k, hk⟩ := digraph_eulerian_orientation_arborescence_count_pos_exists_reachK (hstrong v)
    exact ⟨k, (digraph_eulerian_orientation_arborescence_count_pos_layer_mem D r k v).mpr ⟨k, le_refl k, hk⟩⟩
  have hn : 0 < n := by have := r.isLt; omega
  have hstabuniv : ∀ k, digraph_eulerian_orientation_arborescence_count_pos_layer D r k =
      digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1) →
      digraph_eulerian_orientation_arborescence_count_pos_layer D r k = Finset.univ := by
    intro k hk
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨m, hm⟩ := huniv v
    rcases le_total m k with hmk | hkm
    · exact digraph_eulerian_orientation_arborescence_count_pos_layer_mono_iter D r hmk hm
    · obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
      rw [digraph_eulerian_orientation_arborescence_count_pos_layer_stab D r hk d] at hm
      exact hm
  have hbound : digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1) = Finset.univ := by
    by_contra hne
    have hstrict : ∀ k, k+1 ≤ n-1 →
        digraph_eulerian_orientation_arborescence_count_pos_layer D r k ⊂
          digraph_eulerian_orientation_arborescence_count_pos_layer D r (k+1) := by
      intro k hk1
      refine Finset.ssubset_iff_subset_ne.mpr ⟨digraph_eulerian_orientation_arborescence_count_pos_layer_mono D r k, ?_⟩
      intro heq
      have hu : digraph_eulerian_orientation_arborescence_count_pos_layer D r k = Finset.univ := hstabuniv k heq
      have hsub : digraph_eulerian_orientation_arborescence_count_pos_layer D r k ⊆
          digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1) :=
        digraph_eulerian_orientation_arborescence_count_pos_layer_mono_iter D r (by omega)
      rw [hu] at hsub
      exact hne (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
    have hcard : ∀ k, k ≤ n-1 → k+1 ≤ (digraph_eulerian_orientation_arborescence_count_pos_layer D r k).card := by
      intro k hk
      induction k with
      | zero =>
          rw [digraph_eulerian_orientation_arborescence_count_pos_layer_zero]
          simp
      | succ k ih =>
          have ih' := ih (by omega)
          have hs := Finset.card_lt_card (hstrict k (by omega))
          omega
    have hc := hcard (n-1) (le_refl _)
    have hle := Finset.card_le_univ (digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1))
    have hlen : (digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1)).card ≤ n := by
      simpa using hle
    have hcn : n ≤ (digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1)).card := by omega
    have heqc : (digraph_eulerian_orientation_arborescence_count_pos_layer D r (n-1)).card = Fintype.card (Fin n) := by
      rw [Fintype.card_fin]; omega
    exact hne (Finset.eq_univ_of_card _ heqc)
  let d : Fin n → ℕ := fun v => Nat.find (huniv v)
  have d_spec : ∀ v, v ∈ digraph_eulerian_orientation_arborescence_count_pos_layer D r (d v) :=
    fun v => Nat.find_spec (huniv v)
  have d_min : ∀ v {j}, j < d v → v ∉ digraph_eulerian_orientation_arborescence_count_pos_layer D r j :=
    fun v j hj => Nat.find_min (huniv v) hj
  have d_le : ∀ v, d v ≤ n - 1 := by
    intro v
    apply Nat.find_le
    rw [hbound]
    exact Finset.mem_univ v
  have d_zero : ∀ v, d v = 0 ↔ v = r := by
    intro v
    change Nat.find (huniv v) = 0 ↔ v = r
    have h := Nat.find_eq_zero (huniv v)
    have h' : Nat.find (huniv v) = 0 ↔ v ∈ digraph_eulerian_orientation_arborescence_count_pos_layer D r 0 := h
    rw [digraph_eulerian_orientation_arborescence_count_pos_layer_zero] at h'
    simpa using h'
  have exists_succ : ∀ v, v ≠ r → ∃ u, D.Adj v u ∧ d u < d v := by
    intro v hvr
    have hdv0 : d v ≠ 0 := by intro h; exact hvr ((d_zero v).mp h)
    have hdv1 : 1 ≤ d v := by omega
    have hspec : v ∈ digraph_eulerian_orientation_arborescence_count_pos_layer D r (d v) := d_spec v
    have hstep := digraph_eulerian_orientation_arborescence_count_pos_layer_step D r (d v - 1)
    have hk : d v - 1 + 1 = d v := Nat.sub_add_cancel hdv1
    rw [hk] at hstep
    rw [hstep, Finset.mem_union] at hspec
    rcases hspec with h | h
    · exact absurd h (d_min v (by omega))
    · rw [digraph_eulerian_orientation_arborescence_count_pos_newLayer_mem] at h
      obtain ⟨u, hu, hvu⟩ := h
      have hle : d u ≤ d v - 1 := Nat.find_le (h := huniv u) hu
      exact ⟨u, hvu, by omega⟩
  let p : Fin n → Fin n := fun v => if h : v = r then r else Classical.choose (exists_succ v h)
  have p_r : p r = r := by simp [p]
  have p_adj : ∀ v, v ≠ r → D.Adj v (p v) := by
    intro v hv
    simp only [p, dif_neg hv]
    exact (Classical.choose_spec (exists_succ v hv)).1
  have p_lt : ∀ v, v ≠ r → d (p v) < d v := by
    intro v hv
    simp only [p, dif_neg hv]
    exact (Classical.choose_spec (exists_succ v hv)).2
  have hpr : ∀ m, p^[m] r = r := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply, p_r, ih]
  have hiter : ∀ m v, d v ≤ m → p^[m] v = r := by
    intro m
    induction m with
    | zero =>
        intro v hv
        have h0 : d v = 0 := by omega
        rw [(d_zero v).mp h0]
        rfl
    | succ m ih =>
        intro v hv
        by_cases hvr : v = r
        · subst hvr; exact hpr (m+1)
        · rw [Function.iterate_succ_apply]
          exact ih (p v) (by have := p_lt v hvr; omega)
  rw [digraph_arborescence_count_at]
  apply Finset.card_pos.mpr
  refine ⟨p, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨p_r, (fun v hv => p_adj v hv), (fun v => hiter n v (by have := d_le v; omega))⟩
