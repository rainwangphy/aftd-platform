import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_spliced_colors_update

Topic: online_algorithms   Node: 145a41f6325c

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemma 2.5

Updating a local vertex coloring exactly matches updating the embedded vertex on the larger board.
-/

def op869_offset_emb {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m) : Fin n ↪ Fin m where
  toFun x := ⟨offset+x.val, by omega⟩
  inj' := by
    intro x y he
    apply Fin.ext
    have hv := congrArg Fin.val he
    simp only at hv
    omega

def op869_splice_preds {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n)) (x : Fin m) : Finset (Fin m) :=
  if hx : offset ≤ x.val ∧ x.val < offset+n then
    let a : Fin n := ⟨x.val-offset, by omega⟩
    ext a ∪ (P a).map (op869_offset_emb offset h)
  else base x

lemma op869_splice_preds_at {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n)) (a : Fin n) :
    op869_splice_preds offset h base ext P (op869_offset_emb offset h a) =
      ext a ∪ (P a).map (op869_offset_emb offset h) := by
  classical
  unfold op869_splice_preds
  have ha : offset ≤ (op869_offset_emb offset h a).val ∧
      (op869_offset_emb offset h a).val < offset+n := by
    change offset ≤ offset+a.val ∧ offset+a.val < offset+n
    omega
  simp only [dif_pos ha]
  have heq : (⟨(op869_offset_emb offset h a).val - offset, by
      change offset+a.val-offset < n
      omega⟩ : Fin n) = a := by
    apply Fin.ext
    change offset+a.val-offset = a.val
    omega
  rw [heq]

theorem op869_spliced_block_induced_graph {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n))
    (hexternal : ∀ a x, x ∈ ext a → x.val < offset) :
    ∀ a b, (op869_graph_from_predecessors (op869_splice_preds offset h base ext P)).Adj
      (op869_offset_emb offset h a) (op869_offset_emb offset h b) ↔
      (op869_graph_from_predecessors P).Adj a b := by
  classical
  intro a b
  have hmem (a b : Fin n) :
      op869_offset_emb offset h a ∈
        op869_splice_preds offset h base ext P (op869_offset_emb offset h b) ↔ a ∈ P b := by
    rw [op869_splice_preds_at]
    simp only [Finset.mem_union, Finset.mem_map]
    have hn : op869_offset_emb offset h a ∉ ext b := by
      intro ha
      have hx := hexternal b _ ha
      change offset+a.val < offset at hx
      omega
    simp only [hn, false_or]
    constructor
    · rintro ⟨x,hx,he⟩
      have hxa : x = a := (op869_offset_emb offset h).injective he
      simpa [hxa] using hx
    · intro ha
      exact ⟨a,ha,rfl⟩
  have hlt (a b : Fin n) : op869_offset_emb offset h a < op869_offset_emb offset h b ↔ a < b := by
    change offset+a.val < offset+b.val ↔ a.val < b.val
    omega
  change ((op869_offset_emb offset h a < op869_offset_emb offset h b ∧
      op869_offset_emb offset h a ∈ op869_splice_preds offset h base ext P (op869_offset_emb offset h b)) ∨
    (op869_offset_emb offset h b < op869_offset_emb offset h a ∧
      op869_offset_emb offset h b ∈ op869_splice_preds offset h base ext P (op869_offset_emb offset h a))) ↔
    ((a < b ∧ a ∈ P b) ∨ (b < a ∧ b ∈ P a))
  rw [hlt, hlt, hmem, hmem]

theorem op869_spliced_predecessors_update {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n)) (i : Fin n) (T : Finset (Fin m)) (S : Finset (Fin n)) :
    op869_splice_preds offset h base (Function.update ext i T) (Function.update P i S) =
      Function.update (op869_splice_preds offset h base ext P) (op869_offset_emb offset h i)
        (T ∪ S.map (op869_offset_emb offset h)) := by
  classical
  funext x
  by_cases hx : x = op869_offset_emb offset h i
  · subst x
    simp only [Function.update_self, op869_splice_preds_at]
  · rw [Function.update_of_ne hx]
    unfold op869_splice_preds
    split_ifs with hrange
    · let a : Fin n := ⟨x.val-offset, by omega⟩
      have hai : a ≠ i := by
        intro heq
        apply hx
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change x.val-offset = i.val at hv
        change x.val = offset+i.val
        omega
      change (Function.update ext i T a) ∪ (Function.update P i S a).map (op869_offset_emb offset h) =
        ext a ∪ (P a).map (op869_offset_emb offset h)
      simp [Function.update_of_ne hai]
    · rfl

theorem op869_spliced_predecessors_outside {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n)) (x : Fin m)
    (hx : x.val < offset ∨ offset+n ≤ x.val) :
    op869_splice_preds offset h base ext P x = base x := by
  unfold op869_splice_preds
  split_ifs with hr
  · omega
  · rfl

theorem op869_spliced_earlier_edges {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (ext : Fin n → Finset (Fin m))
    (P : Fin n → Finset (Fin n)) (x : Fin m) (a : Fin n) (hx : x.val < offset) :
    (op869_graph_from_predecessors (op869_splice_preds offset h base ext P)).Adj
      x (op869_offset_emb offset h a) ↔ x ∈ ext a := by
  classical
  have hlt : x < op869_offset_emb offset h a := by
    change x.val < offset+a.val
    omega
  have hmap : x ∉ (P a).map (op869_offset_emb offset h) := by
    intro hm
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hm
    have heq := congrArg Fin.val he
    change offset+y.val = x.val at heq
    omega
  change ((x < op869_offset_emb offset h a ∧
      x ∈ op869_splice_preds offset h base ext P (op869_offset_emb offset h a)) ∨
    (op869_offset_emb offset h a < x ∧
      op869_offset_emb offset h a ∈ op869_splice_preds offset h base ext P x)) ↔ x ∈ ext a
  simp only [hlt, not_lt_of_ge (le_of_lt hlt), false_and, or_false, true_and]
  rw [op869_splice_preds_at]
  simp [hmap]

def op869_splice_colors {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ) (x : Fin m) : Finset ℕ :=
  if hx : offset ≤ x.val ∧ x.val < offset+n then C ⟨x.val-offset, by omega⟩ else base x

lemma op869_splice_colors_at {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ) (a : Fin n) :
    op869_splice_colors offset h base C (op869_offset_emb offset h a) = C a := by
  classical
  unfold op869_splice_colors
  have ha : offset ≤ (op869_offset_emb offset h a).val ∧
      (op869_offset_emb offset h a).val < offset+n := by
    change offset ≤ offset+a.val ∧ offset+a.val < offset+n
    omega
  simp only [dif_pos ha]
  have heq : (⟨(op869_offset_emb offset h a).val - offset, by
      change offset+a.val-offset < n
      omega⟩ : Fin n) = a := by
    apply Fin.ext
    change offset+a.val-offset = a.val
    omega
  rw [heq]



theorem op869_spliced_prefix_palette_contains {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ) (i : ℕ) :
    ((Finset.univ.filter (fun a : Fin n => a.val < i)).biUnion C) ⊆
      ((Finset.univ.filter (fun x : Fin m => x.val < offset+i)).biUnion
        (op869_splice_colors offset h base C)) := by
  classical
  intro c hc
  obtain ⟨a, ha, hca⟩ := Finset.mem_biUnion.mp hc
  have hai : a.val < i := (Finset.mem_filter.mp ha).2
  apply Finset.mem_biUnion.mpr
  refine ⟨op869_offset_emb offset h a, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change offset+a.val < offset+i
    omega
  · simpa [op869_splice_colors_at] using hca

theorem op869_spliced_valid_response {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ)
    (S : Finset (Fin n)) (T : Finset (Fin m)) (colors : Finset ℕ)
    (hvalid : ∀ x ∈ T ∪ S.map (op869_offset_emb offset h),
      Disjoint (op869_splice_colors offset h base C x) colors) :
    ∀ a ∈ S, Disjoint (C a) colors := by
  intro a ha
  have hx : op869_offset_emb offset h a ∈ T ∪ S.map (op869_offset_emb offset h) :=
    Finset.mem_union_right T (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
  simpa [op869_splice_colors_at] using hvalid (op869_offset_emb offset h a) hx

theorem op869_spliced_colors_biUnion {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ) (A : Finset (Fin n)) :
    ((A.map (op869_offset_emb offset h)).biUnion (op869_splice_colors offset h base C)) =
      A.biUnion C := by
  classical
  ext c
  simp only [Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ha, by simpa [op869_splice_colors_at] using hc⟩
  · rintro ⟨a, ha, hc⟩
    exact ⟨op869_offset_emb offset h a, ⟨a, ha, rfl⟩,
      by simpa [op869_splice_colors_at] using hc⟩

theorem op869_spliced_future_predecessors_empty {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (P : Fin n → Finset (Fin n)) (i : ℕ)
    (hbase : ∀ x, offset ≤ x.val → base x = ∅)
    (hlocal : ∀ a, i ≤ a.val → P a = ∅) :
    ∀ x, offset+i ≤ x.val → op869_splice_preds offset h base (fun _ => ∅) P x = ∅ := by
  classical
  intro x hx
  unfold op869_splice_preds
  split_ifs with hrange
  · let a : Fin n := ⟨x.val-offset, by omega⟩
    have ha : i ≤ a.val := by dsimp [a]; omega
    change (∅ : Finset (Fin m)) ∪ (P a).map (op869_offset_emb offset h) = ∅
    rw [hlocal a ha]
    simp
  · exact hbase x (by omega)

/-- Color updates and response transport for a spliced gadget interval. -/
theorem op869_spliced_colors_update {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset ℕ) (C : Fin n → Finset ℕ) (i : Fin n) (colors : Finset ℕ) :
    op869_splice_colors offset h base (Function.update C i colors) =
      Function.update (op869_splice_colors offset h base C) (op869_offset_emb offset h i) colors := by
  classical
  funext x
  by_cases hx : x = op869_offset_emb offset h i
  · subst x
    simp only [Function.update_self, op869_splice_colors_at]
  · rw [Function.update_of_ne hx]
    unfold op869_splice_colors
    split_ifs with hrange
    · let a : Fin n := ⟨x.val-offset, by omega⟩
      have hai : a ≠ i := by
        intro heq
        apply hx
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change x.val-offset = i.val at hv
        change x.val = offset+i.val
        omega
      change Function.update C i colors a = C a
      exact Function.update_of_ne hai _ _
    · rfl
