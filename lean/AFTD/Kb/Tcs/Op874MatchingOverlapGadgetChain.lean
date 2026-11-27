import AFTD.Prelude
import AFTD.Kb.Tcs.Op874DisjointMatchingPalettesCutObstruction
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op874_matching_overlap_gadget_chain

Topic: graphs   Node: f696447f4b6c

Provenance: helper lemma. Unbounded matching-palette overlap examples for OP-874; https://arxiv.org/abs/2610.41950.

For every positive number of blocks, there is a connected bridgeless simple cubic graph with an eight-cycle factor per block and a locally maximal matching-constant cut, retaining two designated matching edges and one same-bit factor edge in each block.
-/

def in1230_m2 : Fin 8 → Fin 8 := ![6,4,7,5,1,3,0,2]

def in1230_bits : Fin 8 → Bool := ![true,false,false,true,false,true,true,false]

def in1230_blk (n : ℕ) (v : Fin 8) (i : Fin (n+1)) : Fin (n+1) :=
  if v = 1 ∨ v = 3 then i + 1 else if v = 4 ∨ v = 5 then i - 1 else i

def in1230_mate (n : ℕ) (u : Fin (n+1) × Fin 8) : Fin (n+1) × Fin 8 :=
  (in1230_blk n u.2 u.1, in1230_m2 u.2)

theorem in1230_mate_mate (n : ℕ) (u : Fin (n+1) × Fin 8) :
    in1230_mate n (in1230_mate n u) = u := by
  obtain ⟨i, v⟩ := u
  fin_cases v <;> simp [in1230_mate, in1230_blk, in1230_m2]

theorem in1230_m2_ne (a : Fin 8) : in1230_m2 a ≠ a ∧ in1230_m2 a ≠ a + 1 ∧ in1230_m2 a ≠ a - 1 := by
  revert a; decide

def in1230_G (n : ℕ) : SimpleGraph (Fin (n+1) × Fin 8) where
  Adj u w := (u.1 = w.1 ∧ (w.2 = u.2 + 1 ∨ u.2 = w.2 + 1)) ∨ in1230_mate n u = w
  symm := ⟨fun u w h => by
    rcases h with ⟨h1, h2 | h2⟩ | h
    · exact Or.inl ⟨h1.symm, Or.inr h2⟩
    · exact Or.inl ⟨h1.symm, Or.inl h2⟩
    · right; rw [← h, in1230_mate_mate]⟩
  loopless := ⟨fun u h => by
    have hc : ∀ a : Fin 8, a ≠ a + 1 := by decide
    rcases h with ⟨-, h | h⟩ | h
    · exact hc _ h
    · exact hc _ h
    · exact (in1230_m2_ne u.2).1 (congrArg Prod.snd h)⟩

theorem in1230_adj (n : ℕ) (u w : Fin (n+1) × Fin 8) :
    (in1230_G n).Adj u w ↔ (u.1 = w.1 ∧ (w.2 = u.2 + 1 ∨ u.2 = w.2 + 1)) ∨ in1230_mate n u = w :=
  Iff.rfl

theorem in1230_step (n : ℕ) (i : Fin (n+1)) (a : Fin 8) : (in1230_G n).Adj (i, a) (i, a + 1) :=
  Or.inl ⟨rfl, Or.inl rfl⟩

def in1230_M (n : ℕ) : Set (Sym2 (Fin (n+1) × Fin 8)) := {e | ∃ u, e = s(u, in1230_mate n u)}

theorem in1230_mem_M (n : ℕ) (u w : Fin (n+1) × Fin 8) :
    s(u, w) ∈ in1230_M n ↔ in1230_mate n u = w := by
  constructor
  · rintro ⟨x, hx⟩
    rcases Sym2.eq_iff.mp hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (in1230_mate_mate n _)
  · intro h
    exact ⟨u, by rw [h]⟩

open scoped Fin.NatCast in
theorem in1230_block_reach (n : ℕ) (i : Fin (n+1)) (v : Fin 8) :
    (in1230_G n).Reachable (i, 0) (i, v) := by
  have h : ∀ m : ℕ, (in1230_G n).Reachable (i, 0) (i, (m : Fin 8)) := by
    intro m
    induction m with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ m ih =>
      refine ih.trans ?_
      have := in1230_step n i (m : Fin 8)
      rw [Nat.cast_succ]
      exact this.reachable
  have := h v.val
  rwa [Fin.cast_val_eq_self] at this

open scoped Fin.NatCast in
theorem in1230_connected (n : ℕ) : (in1230_G n).Connected := by
  have hb : ∀ m : ℕ, (in1230_G n).Reachable (0, 0) ((m : Fin (n+1)), 0) := by
    intro m
    induction m with
    | zero => simpa using SimpleGraph.Reachable.refl _
    | succ m ih =>
      refine ih.trans ((in1230_block_reach n _ 1).trans ?_)
      have hadj : (in1230_G n).Adj ((m : Fin (n+1)), 1) (((m+1 : ℕ) : Fin (n+1)), 4) := by
        right
        simp [in1230_mate, in1230_blk, in1230_m2]
      exact hadj.reachable.trans (in1230_block_reach n _ 4).symm
  have hall : ∀ u : Fin (n+1) × Fin 8, (in1230_G n).Reachable (0, 0) u := by
    rintro ⟨i, v⟩
    have := hb i.val
    rw [Fin.cast_val_eq_self] at this
    exact this.trans (in1230_block_reach n i v)
  have : Nonempty (Fin (n+1) × Fin 8) := ⟨(0, 0)⟩
  exact ⟨fun u w => (hall u).symm.trans (hall w)⟩

/-- an edge of `G` other than `e`, recognised by second coordinates -/
theorem in1230_del_adj (n : ℕ) (u w x y : Fin (n+1) × Fin 8) (h : (in1230_G n).Adj x y)
    (hne : s(x.2, y.2) ≠ s(u.2, w.2)) : ((in1230_G n).deleteEdges {s(u, w)}).Adj x y := by
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h, ?_⟩
  intro he
  rw [Set.mem_singleton_iff] at he
  apply hne
  have := congrArg (Sym2.map Prod.snd) he
  simpa using this

open scoped Fin.NatCast in
theorem in1230_cycle_not_bridge (n : ℕ) (i : Fin (n+1)) (a : Fin 8) :
    ((in1230_G n).deleteEdges {s((i, a), (i, a + 1))}).Reachable (i, a) (i, a + 1) := by
  have hkey : ∀ t : ℕ, t < 7 → s(a - (t : Fin 8), a - (t : Fin 8) - 1) ≠ s(a, a + 1) := by
    revert a; decide
  have h : ∀ t : ℕ, t ≤ 7 →
      ((in1230_G n).deleteEdges {s((i, a), (i, a + 1))}).Reachable (i, a) (i, a - (t : Fin 8)) := by
    intro t ht
    induction t with
    | zero => simpa using SimpleGraph.Reachable.refl _
    | succ t ih =>
      refine (ih (by omega)).trans ?_
      have hadj : (in1230_G n).Adj (i, a - (t : Fin 8)) (i, a - (t : Fin 8) - 1) :=
        Or.inl ⟨rfl, Or.inr (sub_add_cancel _ _).symm⟩
      have e : a - ((t + 1 : ℕ) : Fin 8) = a - (t : Fin 8) - 1 := by rw [Nat.cast_succ, sub_sub]
      rw [e]
      exact (in1230_del_adj n _ _ _ _ hadj (hkey t (by omega))).reachable
  have := h 7 le_rfl
  have e7 : a - ((7 : ℕ) : Fin 8) = a + 1 := by
    have : ∀ b : Fin 8, b - ((7 : ℕ) : Fin 8) = b + 1 := by decide
    exact this a
  rwa [e7] at this

theorem in1230_not_bridge (n : ℕ) (e : Sym2 (Fin (n+1) × Fin 8)) : ¬ (in1230_G n).IsBridge e := by
  induction e using Sym2.ind with
  | _ u w =>
  rw [SimpleGraph.isBridge_iff, not_not]
  by_cases hadj : (in1230_G n).Adj u w
  · obtain ⟨i, a⟩ := u
    obtain ⟨j, b⟩ := w
    rcases hadj with ⟨h1, h2 | h2⟩ | h
    · simp only at h1 h2
      subst h1 h2
      exact in1230_cycle_not_bridge n i a
    · simp only at h1 h2
      subst h1 h2
      rw [Sym2.eq_swap]
      exact (in1230_cycle_not_bridge n i b).symm
    · -- matching edges: explicit detours
      simp only [in1230_mate, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have D := in1230_del_adj n (i, a) (in1230_blk n a i, in1230_m2 a)
      fin_cases a <;> simp only [in1230_blk, in1230_m2] <;> norm_num
      · -- 0 -- 6 : 0, 7, 6
        refine ((D (i, 0) (i, 7) (in1230_step n i 7).symm (by dsimp only; decide)).reachable).trans ?_
        exact (D (i, 7) (i, 6) (in1230_step n i 6).symm (by dsimp only; decide)).reachable
      · -- 1 -- (i+1, 4) : 1, 2, 3, (i+1, 5), (i+1, 4)
        refine ((D (i, 1) (i, 2) (in1230_step n i 1) (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 2) (i, 3) (in1230_step n i 2) (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 3) (i + 1, 5) (Or.inr (by simp [in1230_mate, in1230_blk, in1230_m2]))
          (by dsimp only; decide)).reachable).trans ?_
        exact (D (i + 1, 5) (i + 1, 4) (in1230_step n (i + 1) 4).symm (by dsimp only; decide)).reachable
      · -- 2 -- 7 : 2, 1, 0, 7
        refine ((D (i, 2) (i, 1) (in1230_step n i 1).symm (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 1) (i, 0) (in1230_step n i 0).symm (by dsimp only; decide)).reachable).trans ?_
        exact (D (i, 0) (i, 7) (in1230_step n i 7).symm (by dsimp only; decide)).reachable
      · -- 3 -- (i+1, 5) : 3, 2, 1, (i+1, 4), (i+1, 5)
        refine ((D (i, 3) (i, 2) (in1230_step n i 2).symm (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 2) (i, 1) (in1230_step n i 1).symm (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 1) (i + 1, 4) (Or.inr (by simp [in1230_mate, in1230_blk, in1230_m2]))
          (by dsimp only; decide)).reachable).trans ?_
        exact (D (i + 1, 4) (i + 1, 5) (in1230_step n (i + 1) 4) (by dsimp only; decide)).reachable
      · -- 4 -- (i-1, 1) : 4, 5, (i-1, 3), (i-1, 2), (i-1, 1)
        refine ((D (i, 4) (i, 5) (in1230_step n i 4) (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 5) (i - 1, 3) (Or.inr (by simp [in1230_mate, in1230_blk, in1230_m2]))
          (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i - 1, 3) (i - 1, 2) (in1230_step n (i - 1) 2).symm (by dsimp only; decide)).reachable).trans ?_
        exact (D (i - 1, 2) (i - 1, 1) (in1230_step n (i - 1) 1).symm (by dsimp only; decide)).reachable
      · -- 5 -- (i-1, 3) : 5, 4, (i-1, 1), (i-1, 2), (i-1, 3)
        refine ((D (i, 5) (i, 4) (in1230_step n i 4).symm (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 4) (i - 1, 1) (Or.inr (by simp [in1230_mate, in1230_blk, in1230_m2]))
          (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i - 1, 1) (i - 1, 2) (in1230_step n (i - 1) 1) (by dsimp only; decide)).reachable).trans ?_
        exact (D (i - 1, 2) (i - 1, 3) (in1230_step n (i - 1) 2) (by dsimp only; decide)).reachable
      · -- 6 -- 0 : 6, 7, 0
        refine ((D (i, 6) (i, 7) (in1230_step n i 6) (by dsimp only; decide)).reachable).trans ?_
        exact (D (i, 7) (i, 0) (in1230_step n i 7) (by dsimp only; decide)).reachable
      · -- 7 -- 2 : 7, 0, 1, 2
        refine ((D (i, 7) (i, 0) (in1230_step n i 7) (by dsimp only; decide)).reachable).trans ?_
        refine ((D (i, 0) (i, 1) (in1230_step n i 0) (by dsimp only; decide)).reachable).trans ?_
        exact (D (i, 1) (i, 2) (in1230_step n i 1) (by dsimp only; decide)).reachable
  · have hdel : (in1230_G n).deleteEdges {s(u, w)} = in1230_G n := by
      ext x y
      rw [SimpleGraph.deleteEdges_adj]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro he
        rw [Set.mem_singleton_iff] at he
        apply hadj
        rw [← SimpleGraph.mem_edgeSet, ← he]
        exact h
    rw [hdel]
    exact (in1230_connected n).preconnected u w

theorem op874_matching_overlap_gadget_chain (k : ℕ) (hk : 0 < k) :
    ∃ (G : SimpleGraph (Fin k × Fin 8)) (M : Set (Sym2 (Fin k × Fin 8)))
      (b : Fin k × Fin 8 → Bool),
      letI : DecidableRel G.Adj := Classical.decRel _;
      G.Connected ∧ G.IsRegularOfDegree 3 ∧ (∀ e, ¬ G.IsBridge e) ∧
      (∀ e ∈ M, e ∈ G.edgeSet) ∧
      (∀ v, ∃! e, e ∈ M ∧ v ∈ e) ∧
      (∀ u v, G.Adj u v → s(u,v) ∈ M → b u = b v) ∧
      (∀ u v, G.Adj u v → s(u,v) ∈ M →
        Set.ncard {w | G.Adj u w ∧ b w = b u ∧ s(u,w) ∉ M} +
        Set.ncard {w | G.Adj v w ∧ b w = b v ∧ s(v,w) ∉ M} ≤ 2) ∧
      (∀ u v, G.Adj u v ↔
        (u.1 = v.1 ∧ (v.2 = u.2+1 ∨ u.2 = v.2+1)) ∨ s(u,v) ∈ M) ∧
      (∀ i : Fin k, s((i,2),(i,7)) ∈ M ∧ s((i,6),(i,0)) ∈ M ∧
        b (i,1) = b (i,2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  classical
  refine ⟨in1230_G n, in1230_M n, fun u => in1230_bits u.2, ?_⟩
  -- the at-most-one same-bit cycle neighbour
  have hone : ∀ u : Fin (n+1) × Fin 8,
      Set.ncard {w | (in1230_G n).Adj u w ∧ in1230_bits w.2 = in1230_bits u.2 ∧
        s(u,w) ∉ in1230_M n} ≤ 1 := by
    intro u
    let c : Fin 8 → Fin 8 := fun a => if in1230_bits (a + 1) = in1230_bits a then a + 1 else a - 1
    have hc : ∀ a b : Fin 8, (b = a + 1 ∨ a = b + 1) → in1230_bits b = in1230_bits a → b = c a := by
      decide
    have hsub : {w | (in1230_G n).Adj u w ∧ in1230_bits w.2 = in1230_bits u.2 ∧
        s(u,w) ∉ in1230_M n} ⊆ {(u.1, c u.2)} := by
      rintro w ⟨hw, hb, hm⟩
      rw [in1230_mem_M] at hm
      rcases hw with ⟨h1, h2⟩ | h
      · rw [Set.mem_singleton_iff]
        exact Prod.ext h1.symm (hc u.2 w.2 h2 hb)
      · exact absurd h hm
    calc _ ≤ Set.ncard ({(u.1, c u.2)} : Set (Fin (n+1) × Fin 8)) :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton _
  refine ⟨in1230_connected n, ?_, in1230_not_bridge n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hN : (in1230_G n).neighborFinset u =
        {(u.1, u.2 + 1), (u.1, u.2 - 1), in1230_mate n u} := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, in1230_adj]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨h1, h2 | h2⟩ | h)
        · left; exact Prod.ext h1.symm h2
        · right; left; exact Prod.ext h1.symm (by rw [h2]; exact (add_sub_cancel_right _ _).symm)
        · right; right; exact h.symm
      · rintro (h | h | h)
        · left; rw [h]; exact ⟨rfl, Or.inl rfl⟩
        · left; rw [h]; exact ⟨rfl, Or.inr (sub_add_cancel _ _).symm⟩
        · right; exact h.symm
    rw [hN]
    have hd : ∀ a : Fin 8, a + 1 ≠ a - 1 := by decide
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact (in1230_m2_ne u.2).2.2 (congrArg Prod.snd h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hd u.2 (congrArg Prod.snd h), fun h => ?_⟩
      exact (in1230_m2_ne u.2).2.1 (congrArg Prod.snd h).symm
  · rintro e ⟨u, rfl⟩
    exact Or.inr rfl
  · intro v
    refine ⟨s(v, in1230_mate n v), ⟨⟨v, rfl⟩, Sym2.mem_mk_left _ _⟩, ?_⟩
    rintro e ⟨⟨x, rfl⟩, hv⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · rfl
    · rw [in1230_mate_mate, Sym2.eq_swap]
  · rintro u v - hm
    rw [in1230_mem_M] at hm
    subst hm
    obtain ⟨i, a⟩ := u
    show in1230_bits a = in1230_bits (in1230_m2 a)
    revert a; decide
  · intro u v _ _
    calc _ ≤ 1 + 1 := add_le_add (hone u) (hone v)
      _ = 2 := rfl
  · intro u v
    rw [in1230_adj, in1230_mem_M]
  · intro i
    refine ⟨(in1230_mem_M n _ _).2 ?_, (in1230_mem_M n _ _).2 ?_, rfl⟩
    · simp [in1230_mate, in1230_blk, in1230_m2]
    · simp [in1230_mate, in1230_blk, in1230_m2]
