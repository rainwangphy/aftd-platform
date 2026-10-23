import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentBlockingBoundGe
import AFTD.Kb.Tcs.IsHereditarySegmentProperty
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.GreedyMatching
import AFTD.Kb.Tcs.SegmentEndpoints
import AFTD.Kb.Tcs.GreedyStep
import AFTD.Kb.Tcs.SegmentsBlockPointsProp

/-!
# greedy_matching_fraction_le_of_blocking_ge

Topic: online_algorithms   Node: 930fb1a258e5

Provenance: formalization of a published result. Source: arXiv:2610.23130 Theorem 1.2 (2)

Let P be a hereditary segment property. If β_P(ℓ) ≥ p (formalized by segment_blocking_bound_ge P ℓ p), then there exists a duplicate-free list pts of points in ℝ² in general position on which Greedy creates ℓ segments and matches at most a 2ℓ / (2ℓ + p) fraction of the input points, meaning 2ℓ / pts.length ≤ (2ℓ)/(2ℓ+p).
-/

open scoped Classical

/-- A representative pair of an unordered pair of points in the plane. -/
noncomputable def greedy_matching_fraction_le_of_blocking_ge_sym2rep (e : Sym2 (ℝ × ℝ)) :
    (ℝ × ℝ) × (ℝ × ℝ) := Quot.out e

/-- The representative pair reproduces the unordered pair. -/
lemma greedy_matching_fraction_le_of_blocking_ge_sym2rep_spec (e : Sym2 (ℝ × ℝ)) :
    s((greedy_matching_fraction_le_of_blocking_ge_sym2rep e).1,
      (greedy_matching_fraction_le_of_blocking_ge_sym2rep e).2) = e := Quot.out_eq e

/-- The endpoint set of the representative of `s(u,v)` is `{u, v}`. -/
lemma greedy_matching_fraction_le_of_blocking_ge_rep_pair_eq (u v : ℝ × ℝ) :
    ({(greedy_matching_fraction_le_of_blocking_ge_sym2rep (s(u, v))).1,
      (greedy_matching_fraction_le_of_blocking_ge_sym2rep (s(u, v))).2} : Finset (ℝ × ℝ))
      = {u, v} := by
  have h := greedy_matching_fraction_le_of_blocking_ge_sym2rep_spec (s(u, v))
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Finset.pair_comm]

/-- The two-element endpoint set of a segment, read off its representative. -/
noncomputable def greedy_matching_fraction_le_of_blocking_ge_endpointsOf (e : Sym2 (ℝ × ℝ)) :
    Finset (ℝ × ℝ) :=
  {(greedy_matching_fraction_le_of_blocking_ge_sym2rep e).1,
   (greedy_matching_fraction_le_of_blocking_ge_sym2rep e).2}

/-- `segment_endpoints` is the biUnion of the two-element endpoint sets. -/
lemma greedy_matching_fraction_le_of_blocking_ge_segment_endpoints_eq_biUnion
    (L : Finset (Sym2 (ℝ × ℝ))) :
    segment_endpoints L = L.biUnion greedy_matching_fraction_le_of_blocking_ge_endpointsOf := by
  unfold segment_endpoints
  congr 1
  funext e
  obtain ⟨u, v, rfl⟩ :
      ∃ u v, e = s(u, v) :=
    ⟨_, _, (greedy_matching_fraction_le_of_blocking_ge_sym2rep_spec e).symm⟩
  simp only [greedy_matching_fraction_le_of_blocking_ge_endpointsOf]
  rw [greedy_matching_fraction_le_of_blocking_ge_rep_pair_eq]
  rfl

/-- Membership in `segment_endpoints`, expressed through representatives. -/
lemma greedy_matching_fraction_le_of_blocking_ge_mem_segment_endpoints_iff
    (L : Finset (Sym2 (ℝ × ℝ))) (x : ℝ × ℝ) :
    x ∈ segment_endpoints L ↔ ∃ e ∈ L,
      x = (greedy_matching_fraction_le_of_blocking_ge_sym2rep e).1 ∨
      x = (greedy_matching_fraction_le_of_blocking_ge_sym2rep e).2 := by
  rw [greedy_matching_fraction_le_of_blocking_ge_segment_endpoints_eq_biUnion]
  constructor
  · intro h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e, he, hxe⟩ := h
    exact ⟨e, he, by
      simpa [greedy_matching_fraction_le_of_blocking_ge_endpointsOf, Finset.mem_insert,
        Finset.mem_singleton] using hxe⟩
  · rintro ⟨e, he, h | h⟩
    · rw [Finset.mem_biUnion]
      exact ⟨e, he, by simp [greedy_matching_fraction_le_of_blocking_ge_endpointsOf, h]⟩
    · rw [Finset.mem_biUnion]
      exact ⟨e, he, by simp [greedy_matching_fraction_le_of_blocking_ge_endpointsOf, h]⟩

/-- The segments of `L`, each replaced by its representative pair. -/
noncomputable def greedy_matching_fraction_le_of_blocking_ge_pairList
    (L : Finset (Sym2 (ℝ × ℝ))) : List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  L.toList.map greedy_matching_fraction_le_of_blocking_ge_sym2rep

/-- Flattening the representative pairs yields the endpoint set of `L`. -/
lemma greedy_matching_fraction_le_of_blocking_ge_flatten_toFinset
    (L : Finset (Sym2 (ℝ × ℝ))) :
    (List.flatMap (fun p : (ℝ × ℝ) × (ℝ × ℝ) => [p.1, p.2])
      (greedy_matching_fraction_le_of_blocking_ge_pairList L)).toFinset = segment_endpoints L := by
  apply Finset.ext
  intro x
  rw [List.mem_toFinset, greedy_matching_fraction_le_of_blocking_ge_mem_segment_endpoints_iff]
  simp only [greedy_matching_fraction_le_of_blocking_ge_pairList, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, Finset.mem_toList]
  constructor
  · rintro ⟨p, ⟨e, he, rfl⟩, h | h⟩
    · exact ⟨e, he, Or.inl h⟩
    · exact ⟨e, he, Or.inr h⟩
  · rintro ⟨e, he, h | h⟩
    · exact ⟨_, ⟨e, he, rfl⟩, Or.inl h⟩
    · exact ⟨_, ⟨e, he, rfl⟩, Or.inr h⟩

/-- The flattened representative-pair list has `2 * |L|` entries. -/
lemma greedy_matching_fraction_le_of_blocking_ge_flatten_length
    (L : Finset (Sym2 (ℝ × ℝ))) :
    (List.flatMap (fun p : (ℝ × ℝ) × (ℝ × ℝ) => [p.1, p.2])
      (greedy_matching_fraction_le_of_blocking_ge_pairList L)).length = 2 * L.card := by
  simp only [greedy_matching_fraction_le_of_blocking_ge_pairList]
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_map]
  simp
  omega

/-- A list whose finset of entries has the same cardinality as its length is duplicate-free. -/
lemma greedy_matching_fraction_le_of_blocking_ge_nodup_of_card
    {α : Type*} [DecidableEq α] {l : List α} (h : l.toFinset.card = l.length) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.toFinset_cons, List.length_cons] at h
    have ha : a ∉ t := by
      intro hat
      rw [Finset.insert_eq_of_mem (by simpa [List.mem_toFinset] using hat)] at h
      have hle : t.toFinset.card ≤ t.length := List.toFinset_card_le t
      omega
    have hains : a ∉ t.toFinset := by simpa [List.mem_toFinset] using ha
    rw [Finset.card_insert_of_notMem hains] at h
    have ht : t.toFinset.card = t.length := by omega
    exact List.nodup_cons.mpr ⟨ha, ih ht⟩

/-- Distinct endpoints make the flattened representative list duplicate-free. -/
lemma greedy_matching_fraction_le_of_blocking_ge_flatten_nodup
    (L : Finset (Sym2 (ℝ × ℝ))) (h2 : (segment_endpoints L).card = 2 * L.card) :
    (List.flatMap (fun p : (ℝ × ℝ) × (ℝ × ℝ) => [p.1, p.2])
      (greedy_matching_fraction_le_of_blocking_ge_pairList L)).Nodup := by
  apply greedy_matching_fraction_le_of_blocking_ge_nodup_of_card
  rw [greedy_matching_fraction_le_of_blocking_ge_flatten_toFinset, h2,
    ← greedy_matching_fraction_le_of_blocking_ge_flatten_length]

/-- Re-pairing the representatives recovers `L`. -/
lemma greedy_matching_fraction_le_of_blocking_ge_pairList_matched
    (L : Finset (Sym2 (ℝ × ℝ))) :
    ((greedy_matching_fraction_le_of_blocking_ge_pairList L).map
      (fun p => s(p.1, p.2))).toFinset = L := by
  have h : (greedy_matching_fraction_le_of_blocking_ge_pairList L).map
      (fun p => s(p.1, p.2)) = L.toList := by
    simp only [greedy_matching_fraction_le_of_blocking_ge_pairList, List.map_map]
    have hc : ((fun p : (ℝ × ℝ) × (ℝ × ℝ) => s(p.1, p.2)) ∘
        greedy_matching_fraction_le_of_blocking_ge_sym2rep) = id := by
      funext e
      exact greedy_matching_fraction_le_of_blocking_ge_sym2rep_spec e
    rw [hc, List.map_id]
  rw [h, Finset.toList_toFinset]

/-- Greedy appends the arriving point when no buffered point is admissible. -/
lemma greedy_matching_fraction_le_of_blocking_ge_step_none
    {P : Finset (Sym2 (ℝ × ℝ)) → Prop} {M : Finset (Sym2 (ℝ × ℝ))}
    {U : List (ℝ × ℝ)} {v : ℝ × ℝ} (h : ∀ u ∈ U, ¬ P (insert s(u, v) M)) :
    greedyStep P (M, U) v = (M, U ++ [v]) := by
  have hfind : List.find? (fun u => decide (P (insert s(u, v) M))) U = none := by
    rw [List.find?_eq_none]
    intro u hu
    simpa using h u hu
  simp only [greedyStep, hfind]

/-- Feeding the flattened representative pairs (all inside `L`) to Greedy matches all of them. -/
lemma greedy_matching_fraction_le_of_blocking_ge_foldl_pairs
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (L : Finset (Sym2 (ℝ × ℝ)))
    (hP : IsHereditarySegmentProperty P) (hPL : P L) :
    ∀ (pairs : List ((ℝ × ℝ) × (ℝ × ℝ))),
    (∀ p ∈ pairs, s(p.1, p.2) ∈ L) →
    ∀ M : Finset (Sym2 (ℝ × ℝ)), M ⊆ L →
      List.foldl (greedyStep P) (M, [])
        (List.flatMap (fun p : (ℝ × ℝ) × (ℝ × ℝ) => [p.1, p.2]) pairs)
        = (M ∪ (pairs.map (fun p => s(p.1, p.2))).toFinset, []) := by
  intro pairs
  induction pairs with
  | nil => intro hseg M hM; simp
  | cons p rest ih =>
    intro hseg M hM
    rw [List.flatMap_cons, List.foldl_append]
    have hsegp : s(p.1, p.2) ∈ L := hseg p (by simp)
    have hsub : insert s(p.1, p.2) M ⊆ L := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hsegp
      · exact hM hx
    have hPg : P (insert s(p.1, p.2) M) := hP.2 hsub hPL
    have hstep : greedyStep P (M, []) p.1 = (M, [p.1]) := by
      simp [greedyStep, List.find?_nil]
    have hstep2 : greedyStep P (M, [p.1]) p.2 = (insert s(p.1, p.2) M, []) := by
      have hfind : List.find? (fun u => decide (P (insert s(u, p.2) M))) [p.1] = some p.1 := by
        simp [hPg]
      simp only [greedyStep, hfind]
      simp
    have hone : List.foldl (greedyStep P) (M, []) [p.1, p.2] = (insert s(p.1, p.2) M, []) := by
      rw [List.foldl_cons, hstep, List.foldl_cons, hstep2]
      rfl
    rw [hone]
    rw [ih (fun q hq => hseg q (List.mem_cons_of_mem _ hq)) (insert s(p.1, p.2) M) hsub]
    rw [List.map_cons, List.toFinset_cons, Finset.union_insert, Finset.insert_union]

/-- A blocking family matches none of the blocked points: Greedy appends them all. -/
lemma greedy_matching_fraction_le_of_blocking_ge_foldl_S
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (L : Finset (Sym2 (ℝ × ℝ)))
    (S : Finset (ℝ × ℝ)) (hblk : segments_block_points_prop P L S) :
    ∀ ws : List (ℝ × ℝ), ws.Nodup → (∀ w ∈ ws, w ∈ S) →
    ∀ U : List (ℝ × ℝ), (∀ u ∈ U, u ∈ S) → U.Disjoint ws →
      List.foldl (greedyStep P) (L, U) ws = (L, U ++ ws) := by
  intro ws
  induction ws with
  | nil => intro _ _ U _ _; simp
  | cons w rest ih =>
    intro hnod hmem U hU hdis
    have hwS : w ∈ S := hmem w (by simp)
    have hnod' : rest.Nodup := (List.nodup_cons.mp hnod).2
    have hwrest : w ∉ rest := (List.nodup_cons.mp hnod).1
    have hdis' : U.Disjoint rest := by
      intro a ha har
      exact hdis ha (List.mem_cons_of_mem _ har)
    have hstep : greedyStep P (L, U) w = (L, U ++ [w]) := by
      apply greedy_matching_fraction_le_of_blocking_ge_step_none
      intro u hu
      have huS : u ∈ S := hU u hu
      have hne : u ≠ w := by
        intro h
        exact hdis hu (h ▸ List.mem_cons_self)
      exact hblk huS hwS hne
    rw [List.foldl_cons, hstep,
      ih hnod' (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) (U ++ [w]) ?_ ?_]
    · rw [List.append_assoc, List.singleton_append]
    · intro a ha
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with h | rfl
      · exact hU a h
      · exact hwS
    · intro a ha
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with h | rfl
      · exact hdis' h
      · exact hwrest

/-- Part (2) of Theorem 1.2: if β_P(ℓ) ≥ p, there exists an input on which Greedy creates ℓ segments and matches at most a 2ℓ/(2ℓ+p) fraction. -/
theorem greedy_matching_fraction_le_of_blocking_ge
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P) (ℓ p : ℕ)
    (hβ : segment_blocking_bound_ge P ℓ p) :
    ∃ pts : List (ℝ × ℝ), pts.Nodup ∧ points_in_general_position (pts.toFinset : Set (ℝ × ℝ)) ∧
      (greedyMatching P pts).1.card = ℓ ∧
      (2 * (ℓ : ℝ)) / (pts.length : ℝ) ≤ (2 * (ℓ : ℝ)) / (2 * (ℓ : ℝ) + (p : ℝ)) := by
  obtain ⟨L, S, hLcard, hPL, hends, hdisj, hgen, hblk, hpS⟩ := hβ
  classical
  have hends' : (segment_endpoints L).card = 2 * L.card := by rw [hLcard]; exact hends
  set pairs := greedy_matching_fraction_le_of_blocking_ge_pairList L with hpairs
  set ends : List (ℝ × ℝ) :=
    List.flatMap (fun q : (ℝ × ℝ) × (ℝ × ℝ) => [q.1, q.2]) pairs with hendsdef
  set pts : List (ℝ × ℝ) := ends ++ S.toList with hpts
  have hpairF : ends.toFinset = segment_endpoints L :=
    greedy_matching_fraction_le_of_blocking_ge_flatten_toFinset L
  have hpairN : ends.Nodup := greedy_matching_fraction_le_of_blocking_ge_flatten_nodup L hends'
  have hpairLen : ends.length = 2 * L.card :=
    greedy_matching_fraction_le_of_blocking_ge_flatten_length L
  have hsegmem : ∀ q ∈ pairs, s(q.1, q.2) ∈ L := by
    intro q hq
    rw [hpairs] at hq
    simp only [greedy_matching_fraction_le_of_blocking_ge_pairList, List.mem_map,
      Finset.mem_toList] at hq
    obtain ⟨e, he, rfl⟩ := hq
    rw [greedy_matching_fraction_le_of_blocking_ge_sym2rep_spec]
    exact he
  have hfold : List.foldl (greedyStep P) (∅, []) pts = (L, S.toList) := by
    rw [hpts, List.foldl_append]
    rw [greedy_matching_fraction_le_of_blocking_ge_foldl_pairs P L hP hPL pairs hsegmem ∅
      (Finset.empty_subset L)]
    rw [greedy_matching_fraction_le_of_blocking_ge_pairList_matched, Finset.empty_union]
    exact greedy_matching_fraction_le_of_blocking_ge_foldl_S P L S hblk S.toList
      (Finset.nodup_toList S) (fun w hw => Finset.mem_toList.mp hw) [] (by simp) (by simp)
  refine ⟨pts, ?_, ?_, ?_, ?_⟩
  · rw [hpts, List.nodup_append]
    refine ⟨hpairN, Finset.nodup_toList S, ?_⟩
    intro a ha b hb hab
    have ha' : a ∈ segment_endpoints L := by rw [← hpairF]; simpa using ha
    have hb' : b ∈ S := Finset.mem_toList.mp hb
    subst hab
    exact (Finset.disjoint_left.mp hdisj ha') hb'
  · have hset : pts.toFinset = segment_endpoints L ∪ S := by
      rw [hpts, hendsdef, hpairs, List.toFinset_append,
        greedy_matching_fraction_le_of_blocking_ge_flatten_toFinset, Finset.toList_toFinset]
    rw [hset, Finset.coe_union]
    exact hgen
  · simp only [greedyMatching]
    rw [hfold, hLcard]
  · have hlen : (pts.length : ℝ) = 2 * (L.card : ℝ) + (S.card : ℝ) := by
      rw [hpts, hendsdef, hpairs, List.length_append, hpairLen, Finset.length_toList]
      push_cast
      ring
    rcases Nat.eq_zero_or_pos (2 * ℓ + p) with hp0 | hppos
    · have hℓ0 : ℓ = 0 := by omega
      simp [hℓ0]
    · have hkey : 2 * (ℓ : ℝ) + (p : ℝ) ≤ 2 * (L.card : ℝ) + (S.card : ℝ) := by
        have h1 : 2 * ℓ + p ≤ 2 * L.card + S.card := by
          rw [hLcard]; exact Nat.add_le_add_left hpS _
        exact_mod_cast h1
      have hpos : (0 : ℝ) < 2 * (ℓ : ℝ) + (p : ℝ) := by
        have h2 : (0 : ℝ) < ((2 * ℓ + p : ℕ) : ℝ) := by exact_mod_cast hppos
        push_cast at h2 ⊢
        linarith
      rw [hlen]
      exact div_le_div_of_nonneg_left (by positivity) hpos hkey
