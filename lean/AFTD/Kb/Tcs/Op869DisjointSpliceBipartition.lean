import AFTD.Prelude
import AFTD.Kb.Tcs.Op869SplicedColorsUpdate
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_disjoint_splice_bipartition

Topic: online_algorithms   Node: 3f8b686e2cc3

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemma 2.3

Two bipartite graphs on disjoint board regions admit a combined bipartition that preserves both chosen side assignments.
-/

theorem op869_disjoint_splice_no_cross {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (P : Fin n → Finset (Fin n))
    (hclear : ∀ x, offset ≤ x.val → base x = ∅) :
    ∀ x y, (op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)).Adj x y →
      ((offset ≤ x.val ∧ x.val < offset+n) ↔ (offset ≤ y.val ∧ y.val < offset+n)) := by
  classical
  let G := op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)
  let inside : Fin m → Prop := fun x => offset ≤ x.val ∧ x.val < offset+n
  have hsep (x y : Fin m) (hx : inside x) (hy : ¬ inside y) : ¬ G.Adj x y := by
    dsimp [inside] at hx hy
    let a : Fin n := ⟨x.val-offset, by omega⟩
    have hxa : op869_offset_emb offset h a = x := by
      apply Fin.ext
      change offset+(x.val-offset) = x.val
      omega
    by_cases hybefore : y.val < offset
    · intro hadj
      have he := (op869_spliced_earlier_edges offset h base (fun _ => ∅) P y a hybefore).mp
        (by simpa [G,hxa] using hadj.symm)
      simp at he
    · have hyafter : offset+n ≤ y.val := by omega
      have hyempty : op869_splice_preds offset h base (fun _ => ∅) P y = ∅ := by
        rw [op869_spliced_predecessors_outside offset h base (fun _ => ∅) P y (Or.inr hyafter)]
        apply hclear
        omega
      have hxy : x < y := by
        change x.val < y.val
        omega
      intro hadj
      change (x < y ∧ x ∈ op869_splice_preds offset h base (fun _ => ∅) P y) ∨
        (y < x ∧ y ∈ op869_splice_preds offset h base (fun _ => ∅) P x) at hadj
      rcases hadj with ⟨_, hxmem⟩ | ⟨hyx, _⟩
      · simpa [hyempty] using hxmem
      · exact (not_lt_of_ge (le_of_lt hxy)) hyx
  intro x y hxy
  by_cases hx : inside x <;> by_cases hy : inside y
  · exact Iff.intro (fun _ => hy) (fun _ => hx)
  · exact False.elim (hsep x y hx hy hxy)
  · exact False.elim (hsep y x hy hx hxy.symm)
  · exact Iff.intro (fun h => False.elim (hx h)) (fun h => False.elim (hy h))


theorem op869_disjoint_splice_colorable {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (P : Fin n → Finset (Fin n)) (k : ℕ)
    (hclear : ∀ x, offset ≤ x.val → base x = ∅)
    (hbase : (op869_graph_from_predecessors base).Colorable k)
    (hlocal : (op869_graph_from_predecessors P).Colorable k) :
    (op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)).Colorable k := by
  classical
  let G := op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)
  let cb := hbase.some
  let cl := hlocal.some
  let inside : Fin m → Prop := fun x => offset ≤ x.val ∧ x.val < offset+n
  let col : Fin m → Fin k := fun x =>
    if hx : inside x then cl ⟨x.val-offset, by dsimp [inside] at hx; omega⟩ else cb x
  have hsep (x y : Fin m) (hx : inside x) (hy : ¬ inside y) : ¬ G.Adj x y := by
    dsimp [inside] at hx hy
    let a : Fin n := ⟨x.val-offset, by omega⟩
    have hxa : op869_offset_emb offset h a = x := by
      apply Fin.ext
      change offset+(x.val-offset) = x.val
      omega
    by_cases hybefore : y.val < offset
    · intro hadj
      have he := (op869_spliced_earlier_edges offset h base (fun _ => ∅) P y a hybefore).mp
        (by simpa [G,hxa] using hadj.symm)
      simp at he
    · have hyafter : offset+n ≤ y.val := by omega
      have hyempty : op869_splice_preds offset h base (fun _ => ∅) P y = ∅ := by
        rw [op869_spliced_predecessors_outside offset h base (fun _ => ∅) P y (Or.inr hyafter)]
        apply hclear
        omega
      have hxy : x < y := by
        change x.val < y.val
        omega
      intro hadj
      change (x < y ∧ x ∈ op869_splice_preds offset h base (fun _ => ∅) P y) ∨
        (y < x ∧ y ∈ op869_splice_preds offset h base (fun _ => ∅) P x) at hadj
      rcases hadj with ⟨_, hxmem⟩ | ⟨hyx, _⟩
      · simpa [hyempty] using hxmem
      · exact (not_lt_of_ge (le_of_lt hxy)) hyx
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro x y hadj
  by_cases hx : inside x
  · by_cases hy : inside y
    · let a : Fin n := ⟨x.val-offset, by dsimp [inside] at hx; omega⟩
      let b : Fin n := ⟨y.val-offset, by dsimp [inside] at hy; omega⟩
      have hxa : op869_offset_emb offset h a = x := by
        apply Fin.ext
        dsimp [a,inside] at hx
        change offset+(x.val-offset) = x.val
        omega
      have hyb : op869_offset_emb offset h b = y := by
        apply Fin.ext
        dsimp [b,inside] at hy
        change offset+(y.val-offset) = y.val
        omega
      have hlocalAdj : (op869_graph_from_predecessors P).Adj a b := by
        apply (op869_spliced_block_induced_graph offset h base (fun _ => ∅) P
          (by intro i z hz; simp at hz) a b).mp
        simpa [G,hxa,hyb] using hadj
      simpa [col, hx, hy, a, b] using cl.valid hlocalAdj
    · exact False.elim (hsep x y hx hy hadj)
  · by_cases hy : inside y
    · exact False.elim (hsep y x hy hx hadj.symm)
    · have hxout : x.val < offset ∨ offset+n ≤ x.val := by dsimp [inside] at hx; omega
      have hyout : y.val < offset ∨ offset+n ≤ y.val := by dsimp [inside] at hy; omega
      have hxP := op869_spliced_predecessors_outside offset h base (fun _ => ∅) P x hxout
      have hyP := op869_spliced_predecessors_outside offset h base (fun _ => ∅) P y hyout
      have hbaseAdj : (op869_graph_from_predecessors base).Adj x y := by
        change (x < y ∧ x ∈ base y) ∨ (y < x ∧ y ∈ base x)
        change (x < y ∧ x ∈ op869_splice_preds offset h base (fun _ => ∅) P y) ∨
          (y < x ∧ y ∈ op869_splice_preds offset h base (fun _ => ∅) P x) at hadj
        simpa [hxP,hyP] using hadj
      simpa [col,hx,hy] using cb.valid hbaseAdj

/-- Side-preserving splice of bipartite components. -/
theorem op869_disjoint_splice_bipartition {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (base : Fin m → Finset (Fin m)) (P : Fin n → Finset (Fin n))
    (baseSide : Fin m → Bool) (localSide : Fin n → Bool)
    (hclear : ∀ x, offset ≤ x.val → base x = ∅)
    (hbase : ∀ x y, (op869_graph_from_predecessors base).Adj x y → baseSide x ≠ baseSide y)
    (hlocal : ∀ x y, (op869_graph_from_predecessors P).Adj x y → localSide x ≠ localSide y) :
    ∃ side : Fin m → Bool,
      (∀ x, ¬ (offset ≤ x.val ∧ x.val < offset+n) → side x = baseSide x) ∧
      (∀ a, side (op869_offset_emb offset h a) = localSide a) ∧
      ∀ x y, (op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)).Adj x y →
        side x ≠ side y := by
  classical
  let G := op869_graph_from_predecessors (op869_splice_preds offset h base (fun _ => ∅) P)
  let inside : Fin m → Prop := fun x => offset ≤ x.val ∧ x.val < offset+n
  let col : Fin m → Bool := fun x =>
    if hx : inside x then localSide ⟨x.val-offset, by dsimp [inside] at hx; omega⟩ else baseSide x
  have hsep (x y : Fin m) (hx : inside x) (hy : ¬ inside y) : ¬ G.Adj x y := by
    dsimp [inside] at hx hy
    let a : Fin n := ⟨x.val-offset, by omega⟩
    have hxa : op869_offset_emb offset h a = x := by
      apply Fin.ext
      change offset+(x.val-offset) = x.val
      omega
    by_cases hybefore : y.val < offset
    · intro hadj
      have he := (op869_spliced_earlier_edges offset h base (fun _ => ∅) P y a hybefore).mp
        (by simpa [G,hxa] using hadj.symm)
      simp at he
    · have hyafter : offset+n ≤ y.val := by omega
      have hyempty : op869_splice_preds offset h base (fun _ => ∅) P y = ∅ := by
        rw [op869_spliced_predecessors_outside offset h base (fun _ => ∅) P y (Or.inr hyafter)]
        apply hclear
        omega
      have hxy : x < y := by
        change x.val < y.val
        omega
      intro hadj
      change (x < y ∧ x ∈ op869_splice_preds offset h base (fun _ => ∅) P y) ∨
        (y < x ∧ y ∈ op869_splice_preds offset h base (fun _ => ∅) P x) at hadj
      rcases hadj with ⟨_, hxmem⟩ | ⟨hyx, _⟩
      · simpa [hyempty] using hxmem
      · exact (not_lt_of_ge (le_of_lt hxy)) hyx
  refine ⟨col, ?_, ?_, ?_⟩
  · intro x hx
    simp [col, inside, hx]
  · intro a
    have ha : inside (op869_offset_emb offset h a) := by
      change offset ≤ offset+a.val ∧ offset+a.val < offset+n
      omega
    simp only [col, dif_pos ha]
    congr 1
    apply Fin.ext
    change offset+a.val-offset = a.val
    omega
  · intro x y hadj
    by_cases hx : inside x
    · by_cases hy : inside y
      · let a : Fin n := ⟨x.val-offset, by dsimp [inside] at hx; omega⟩
        let b : Fin n := ⟨y.val-offset, by dsimp [inside] at hy; omega⟩
        have hxa : op869_offset_emb offset h a = x := by
          apply Fin.ext
          dsimp [a,inside] at hx
          change offset+(x.val-offset) = x.val
          omega
        have hyb : op869_offset_emb offset h b = y := by
          apply Fin.ext
          dsimp [b,inside] at hy
          change offset+(y.val-offset) = y.val
          omega
        have hlocalAdj : (op869_graph_from_predecessors P).Adj a b := by
          apply (op869_spliced_block_induced_graph offset h base (fun _ => ∅) P
            (by intro i z hz; simp at hz) a b).mp
          simpa [G,hxa,hyb] using hadj
        simpa [col, hx, hy, a, b] using hlocal a b hlocalAdj
      · exact False.elim (hsep x y hx hy hadj)
    · by_cases hy : inside y
      · exact False.elim (hsep y x hy hx hadj.symm)
      · have hxout : x.val < offset ∨ offset+n ≤ x.val := by dsimp [inside] at hx; omega
        have hyout : y.val < offset ∨ offset+n ≤ y.val := by dsimp [inside] at hy; omega
        have hxP := op869_spliced_predecessors_outside offset h base (fun _ => ∅) P x hxout
        have hyP := op869_spliced_predecessors_outside offset h base (fun _ => ∅) P y hyout
        have hbaseAdj : (op869_graph_from_predecessors base).Adj x y := by
          change (x < y ∧ x ∈ base y) ∨ (y < x ∧ y ∈ base x)
          change (x < y ∧ x ∈ op869_splice_preds offset h base (fun _ => ∅) P y) ∨
            (y < x ∧ y ∈ op869_splice_preds offset h base (fun _ => ∅) P x) at hadj
          simpa [hxP,hyP] using hadj
        simpa [col,hx,hy] using hbase x y hbaseAdj
