import AFTD.Prelude
import AFTD.Kb.Tcs.Op869DisjointIntervalGameLift
import AFTD.Kb.Tcs.Op869GameMaintainsPrefix
import AFTD.Kb.Tcs.Op869BoardTwoCopiesAmplify
import AFTD.Kb.Tcs.Op869MacroStepStrategySimulation
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree
import AFTD.Kb.Tcs.Op869DisjointSpliceBipartition
import AFTD.Kb.Tcs.F

/-!
# op869_one_sided_bipartite_gadget

Topic: online_algorithms   Node: 30a45f40149a

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.3

A t-fold adversary can build a bipartite graph in at most 2^(j+1)-1 vertices with one side containing at least t+j ceil(t/2) colors.
-/

def op869_one_sided_goal {n : ℕ} (t j : ℕ) (s : Op869SequentialState n) : Prop :=
  ∃ side : Fin n → Bool,
    (∀ x y, (op869_graph_from_predecessors s.P).Adj x y → side x ≠ side y) ∧
    t+j*((t+1)/2) ≤
      ((Finset.univ.filter (fun x : Fin n => x.val < s.i ∧ side x = true)).biUnion s.C).card

theorem op869_play_one_sided_copy {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ) (t j : ℕ)
    (hclear : ∀ x, offset ≤ x.val → baseP x = ∅ ∧ baseC x = ∅)
    (hbase : (op869_graph_from_predecessors baseP).Colorable 2)
    (hgame : op869_sequential_goal_game (op869_one_sided_goal t j) (op869_sequential_legal 2 n)
      (op869_sequential_valid t) op869_sequential_next n
      ⟨0, (fun _ : Fin n => ∅), (fun _ : Fin n => ∅)⟩) :
    op869_sequential_goal_game
      (fun sg : Op869SequentialState m => ∃ sl : Op869SequentialState n,
        op869_disjoint_interval_related offset h baseP baseC sl sg ∧
        op869_prefix_invariant 2 sl ∧ op869_one_sided_goal t j sl)
      (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next n
      ⟨offset, baseP, baseC⟩ := by
  have hsource := op869_game_maintains_prefix 2 n t (op869_one_sided_goal t j) n
    ⟨0, (fun _ => ∅), (fun _ => ∅)⟩ (op869_empty_prefix_invariant n 2 (by omega)) hgame
  apply op869_disjoint_interval_game_lift offset h baseP baseC 2 n t
    (fun x hx => (hclear x hx).1) hbase
    (fun sl => op869_prefix_invariant 2 sl ∧ op869_one_sided_goal t j sl)
    (fun sg => ∃ sl : Op869SequentialState n,
      op869_disjoint_interval_related offset h baseP baseC sl sg ∧
      op869_prefix_invariant 2 sl ∧ op869_one_sided_goal t j sl)
  · intro sl sg hr hg
    exact ⟨sl,hr,hg⟩
  · exact op869_disjoint_interval_start offset h baseP baseC hclear
  · exact hsource



theorem op869_one_sided_goal_disjoint_lift {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (baseSide : Fin m → Bool) (t j : ℕ)
    (hclear : ∀ x, offset ≤ x.val → baseP x = ∅)
    (hbaseSide : ∀ x y, (op869_graph_from_predecessors baseP).Adj x y → baseSide x ≠ baseSide y)
    (sl : Op869SequentialState n) (sg : Op869SequentialState m)
    (hrel : op869_disjoint_interval_related offset h baseP baseC sl sg)
    (hgoal : op869_one_sided_goal t j sl) :
    op869_one_sided_goal t j sg := by
  classical
  rcases hrel with ⟨hindex,hP,hC⟩
  obtain ⟨localSide,hlocalSide,hbound⟩ := hgoal
  obtain ⟨side,houtside,hinside,hproper⟩ :=
    op869_disjoint_splice_bipartition offset h baseP sl.P baseSide localSide hclear hbaseSide hlocalSide
  refine ⟨side, ?_, ?_⟩
  · simpa [hP] using hproper
  · let A := Finset.univ.filter (fun x : Fin n => x.val < sl.i ∧ localSide x = true)
    let B := Finset.univ.filter (fun x : Fin m => x.val < sg.i ∧ side x = true)
    have hsub : A.map (op869_offset_emb offset h) ⊆ B := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
      have ha' : a.val < sl.i ∧ localSide a = true := (Finset.mem_filter.mp ha).2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change offset+a.val < sg.i
        omega
      · rw [hinside a]
        exact ha'.2
    have hc := Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left sg.C hsub)
    have heq : ((A.map (op869_offset_emb offset h)).biUnion sg.C).card =
        (A.biUnion sl.C).card := by
      rw [hC, op869_spliced_colors_biUnion]
    rw [heq] at hc
    exact le_trans hbound hc


theorem op869_one_sided_gadget_base (t n : ℕ) (hn : 1 ≤ n) :
    op869_sequential_goal_game
      (fun s : Op869SequentialState n => ∃ side : Fin n → Bool,
        (∀ x y, (op869_graph_from_predecessors s.P).Adj x y → side x ≠ side y) ∧
        t ≤ ((Finset.univ.filter (fun x : Fin n => x.val < s.i ∧ side x = true)).biUnion s.C).card)
      (op869_sequential_legal 2 n) (op869_sequential_valid t) op869_sequential_next n
      ⟨0, (fun _ => ∅), (fun _ => ∅)⟩ := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    have hi : 0 < n+1 := by omega
    let v : Fin (n+1) := ⟨0,hi⟩
    let P : Fin (n+1) → Finset (Fin (n+1)) := fun _ => ∅
    let C : Fin (n+1) → Finset ℕ := fun _ => ∅
    have hP : Function.update P v ∅ = P := by
      funext a
      by_cases ha : a = v <;> simp [P,ha]
    have hgraph : (op869_graph_from_predecessors P).Colorable 2 := by
      have he := op869_empty_prefix_invariant (n+1) 2 (by omega)
      exact he.2.1
    change op869_sequential_goal_game _ (op869_sequential_legal 2 (n+1))
      (op869_sequential_valid t) op869_sequential_next (n+1) ⟨0,P,C⟩
    simp only [op869_sequential_goal_game]
    refine ⟨∅, ?_, ?_⟩
    · refine ⟨hi, ?_, ?_, ?_⟩
      · simp
      · change (op869_graph_from_predecessors (Function.update P v ∅)).Colorable 2
        rw [hP]
        exact hgraph
      · change ∀ a, op869_predecessor_postdegree (Function.update P v ∅) a ≤ n+1
        rw [hP]
        intro a
        unfold op869_predecessor_postdegree
        simp [P]
    · intro colors hvalid
      left
      simp only [op869_sequential_next, dif_pos hi]
      refine ⟨fun _ => true, ?_, ?_⟩
      · intro a b hadj
        change (op869_graph_from_predecessors (Function.update P v ∅)).Adj a b at hadj
        rw [hP] at hadj
        change (a < b ∧ a ∈ P b) ∨ (b < a ∧ b ∈ P a) at hadj
        simp [P] at hadj
      · have hsubset : colors ⊆
          ((Finset.univ.filter (fun x : Fin (n+1) => x.val < 1 ∧ true = true)).biUnion
            (Function.update C v colors)) := by
          intro c hc
          refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
          · simp [v]
          · simpa using hc
        have hcard := Finset.card_le_card hsubset
        have hct : colors.card = t := hvalid.1
        change t ≤ ((Finset.univ.filter (fun x : Fin (n+1) => x.val < 1 ∧ true = true)).biUnion
          (Function.update C v colors)).card
        omega


theorem op869_one_sided_root_game {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (baseSide : Fin m → Bool) (localSide : Fin n → Bool)
    (i a t : ℕ) (hi : i ≤ n) (hr : offset+i < m)
    (hbaseClear : ∀ x, offset ≤ x.val → baseP x = ∅)
    (hlocalClear : ∀ x, i ≤ x.val → P x = ∅)
    (hbaseSide : ∀ x y, (op869_graph_from_predecessors baseP).Adj x y → baseSide x ≠ baseSide y)
    (hlocalSide : ∀ x y, (op869_graph_from_predecessors P).Adj x y → localSide x ≠ localSide y)
    (S : Finset (Fin m)) (hSbefore : ∀ x ∈ S, x.val < offset)
    (hSside : ∀ x ∈ S, baseSide x = true)
    (hfirst : a ≤ (S.biUnion (op869_splice_colors offset h baseC C)).card)
    (hsecond : a ≤ (((Finset.univ.filter (fun x : Fin n => x.val < i ∧ localSide x = true)).map
      (op869_offset_emb offset h)).biUnion (op869_splice_colors offset h baseC C)).card) :
    op869_sequential_goal_game
      (fun s : Op869SequentialState m => ∃ side : Fin m → Bool,
        (∀ x y, (op869_graph_from_predecessors s.P).Adj x y → side x ≠ side y) ∧
        a+(t+1)/2 ≤ ((Finset.univ.filter (fun x : Fin m => x.val < s.i ∧ side x = true)).biUnion s.C).card)
      (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next 1
      ⟨offset+i, op869_splice_preds offset h baseP (fun _ => ∅) P,
        op869_splice_colors offset h baseC C⟩ := by
  classical
  let root : Fin m := ⟨offset+i, hr⟩
  let P₀ := op869_splice_preds offset h baseP (fun _ => ∅) P
  let C₀ := op869_splice_colors offset h baseC C
  have hSroot : ∀ x ∈ S, x < root := by
    intro x hx
    have hb := hSbefore x hx
    change x.val < offset+i
    omega
  have hclear : ∀ x, root.val ≤ x.val → P₀ x = ∅ := by
    intro x hx
    apply op869_spliced_future_predecessors_empty offset h baseP P i hbaseClear hlocalClear
    exact hx
  obtain ⟨same, hsameOutside, hsameInside, hsameProper⟩ :=
    op869_disjoint_splice_bipartition offset h baseP P baseSide localSide hbaseClear hbaseSide hlocalSide
  have hsameS : ∀ x ∈ S, same x = true := by
    intro x hx
    rw [hsameOutside x (by have := hSbefore x hx; omega)]
    exact hSside x hx
  obtain ⟨side, hkeep, hroot, hproper⟩ :=
    op869_add_root_to_bipartition P₀ root S same hclear hSroot hsameProper hsameS
  simp only [op869_sequential_goal_game]
  refine ⟨S, ?_, ?_⟩
  · refine ⟨hr, ?_, ?_, ?_⟩
    · intro x hx
      exact hSroot x hx
    · change (op869_graph_from_predecessors (Function.update P₀ root S)).Colorable 2
      exact op869_bool_bipartition_colorable _ side hproper
    · change ∀ x, op869_predecessor_postdegree (Function.update P₀ root S) x ≤ m
      intro x
      unfold op869_predecessor_postdegree
      simpa using Finset.card_le_univ (Finset.univ.filter
        (fun y : Fin m => x < y ∧ x ∈ Function.update P₀ root S y))
  · intro X hvalid
    left
    simp only [op869_sequential_next, dif_pos hr]
    have hamp := op869_board_two_copies_amplify offset h baseP baseC P C baseSide localSide
      i a t hi hr hbaseClear hlocalClear hbaseSide hlocalSide S hSbefore hSside X hvalid.1 hvalid.2 hfirst hsecond
    obtain ⟨side',hproper',hbound⟩ := hamp
    refine ⟨side',hproper',?_⟩
    change a+(t+1)/2 ≤ ((Finset.univ.filter (fun x : Fin m =>
      x.val < offset+i+1 ∧ side' x = true)).biUnion (Function.update C₀ root X)).card
    simpa only [Nat.lt_succ_iff] using hbound


theorem op869_game_goal_mono {S M R : Type} (g₁ g₂ : S → Prop)
    (legal : S → M → Prop) (valid : S → M → R → Prop) (next : S → M → R → S)
    (hgoal : ∀ s, g₁ s → g₂ s) (fuel : ℕ) (s : S)
    (hgame : op869_sequential_goal_game g₁ legal valid next fuel s) :
    op869_sequential_goal_game g₂ legal valid next fuel s := by
  induction fuel generalizing s with
  | zero => simp [op869_sequential_goal_game] at hgame
  | succ fuel ih =>
    simp only [op869_sequential_goal_game] at hgame ⊢
    obtain ⟨a,ha,hnext⟩ := hgame
    refine ⟨a,ha,?_⟩
    intro r hr
    rcases hnext r hr with hgoal₁ | hrest
    · exact Or.inl (hgoal _ hgoal₁)
    · exact Or.inr (ih _ hrest)

theorem op869_one_sided_bipartite_gadget_proof (t : ℕ) (ht : 1 ≤ t) (j : ℕ) :
    ∀ m : ℕ, 2^(j+1)-1 ≤ m →
      op869_sequential_goal_game (op869_one_sided_goal t j)
        (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next m
        ⟨0, (fun _ : Fin m => ∅), (fun _ : Fin m => ∅)⟩ := by
  induction j with
  | zero =>
    intro m hm
    have hm' : 1 ≤ m := by norm_num at hm; omega
    apply op869_game_goal_mono _ (op869_one_sided_goal t 0)
      (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next
      ?_ m _ (op869_one_sided_gadget_base t m hm')
    intro s hs
    simpa [op869_one_sided_goal] using hs
  | succ j ih =>
    intro m hm
    let b := 2^(j+1)-1
    have hpow : 2 ≤ 2^(j+1) := by
      have hp := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ j+1)
      simpa using hp
    have hpows : 2^((j+1)+1) = 2^(j+1)*2 := by rw [pow_succ]
    have hb : 1 ≤ b := by dsimp [b]; omega
    have hbudget : b+(b+1) ≤ m := by dsimp [b]; omega
    have h0 : 0+b ≤ m := by omega
    let E : Fin m → Finset (Fin m) := fun _ => ∅
    let F : Fin m → Finset ℕ := fun _ => ∅
    have hclear0 : ∀ x : Fin m, 0 ≤ x.val → E x = ∅ ∧ F x = ∅ := by simp [E,F]
    have hbase0 : (op869_graph_from_predecessors E).Colorable 2 := by
      have h := op869_empty_prefix_invariant m 2 (by omega)
      exact h.2.1
    have hbaseSide0 : ∀ x y, (op869_graph_from_predecessors E).Adj x y →
        (fun _ : Fin m => false) x ≠ (fun _ : Fin m => false) y := by
      intro x y hxy
      change (x < y ∧ x ∈ E y) ∨ (y < x ∧ y ∈ E x) at hxy
      simp [E] at hxy
    have hlocal := ih b (by dsimp [b]; rfl)
    let firstGoal : Op869SequentialState m → Prop := fun sg =>
      ∃ sl : Op869SequentialState b, op869_disjoint_interval_related 0 h0 E F sl sg ∧
        op869_prefix_invariant 2 sl ∧ op869_one_sided_goal t j sl
    have hfirst : op869_sequential_goal_game firstGoal (op869_sequential_legal 2 m)
        (op869_sequential_valid t) op869_sequential_next b ⟨0,E,F⟩ :=
      op869_play_one_sided_copy 0 h0 E F t j hclear0 hbase0 hlocal
    have hfirst' := op869_game_maintains_prefix 2 m t firstGoal b ⟨0,E,F⟩
      (op869_empty_prefix_invariant m 2 (by omega)) hfirst
    have hcont : ∀ sf : Op869SequentialState m,
        (op869_prefix_invariant 2 sf ∧ firstGoal sf) →
        op869_one_sided_goal t (j+1) sf ∨
          op869_sequential_goal_game (op869_one_sided_goal t (j+1))
            (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next (b+1) sf := by
      intro sf hsf
      obtain ⟨hinvf, sl, hrel, hinvl, hgl⟩ := hsf
      have hfi : sf.i ≤ b := by
        have hidx := hrel.1
        have hli := hinvl.1
        omega
      have hfirstGlobal : op869_one_sided_goal t j sf :=
        op869_one_sided_goal_disjoint_lift 0 h0 E F (fun _ => false) t j
          (fun x hx => rfl) hbaseSide0 sl sf hrel hgl
      obtain ⟨baseSide,hbaseSide,hbaseBound⟩ := hfirstGlobal
      have h2 : sf.i+b ≤ m := by omega
      have hclear2 : ∀ x : Fin m, sf.i ≤ x.val → sf.P x = ∅ ∧ sf.C x = ∅ := hinvf.2.2
      have hbase2 : (op869_graph_from_predecessors sf.P).Colorable 2 := hinvf.2.1
      let secondGoal : Op869SequentialState m → Prop := fun sg =>
        ∃ sl₂ : Op869SequentialState b, op869_disjoint_interval_related sf.i h2 sf.P sf.C sl₂ sg ∧
          op869_prefix_invariant 2 sl₂ ∧ op869_one_sided_goal t j sl₂
      have hsecond : op869_sequential_goal_game secondGoal (op869_sequential_legal 2 m)
          (op869_sequential_valid t) op869_sequential_next b sf :=
        op869_play_one_sided_copy sf.i h2 sf.P sf.C t j hclear2 hbase2 hlocal
      have hsecond' := op869_game_maintains_prefix 2 m t secondGoal b sf hinvf hsecond
      have hcont2 : ∀ sg : Op869SequentialState m,
          (op869_prefix_invariant 2 sg ∧ secondGoal sg) →
          op869_one_sided_goal t (j+1) sg ∨
            op869_sequential_goal_game (op869_one_sided_goal t (j+1))
              (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next 1 sg := by
        intro sg hsg
        obtain ⟨hinvg, sl₂, hrel₂, hinvl₂, hgl₂⟩ := hsg
        obtain ⟨localSide,hlocalSide,hlocalBound⟩ := hgl₂
        rcases hrel₂ with ⟨hidx,hP,hC⟩
        have hroot : sf.i+sl₂.i < m := by
          have hli := hinvl₂.1
          omega
        let S := Finset.univ.filter (fun x : Fin m => x.val < sf.i ∧ baseSide x = true)
        have hSbefore : ∀ x ∈ S, x.val < sf.i := by
          intro x hx
          exact (Finset.mem_filter.mp hx).2.1
        have hSside : ∀ x ∈ S, baseSide x = true := by
          intro x hx
          exact (Finset.mem_filter.mp hx).2.2
        have hpalette : S.biUnion (op869_splice_colors sf.i h2 sf.C sl₂.C) = S.biUnion sf.C := by
          apply Finset.biUnion_congr rfl
          intro x hx
          have hx' := hSbefore x hx
          simp [op869_splice_colors, not_le_of_gt hx']
        have hfirstBound : t+j*((t+1)/2) ≤
            (S.biUnion (op869_splice_colors sf.i h2 sf.C sl₂.C)).card := by
          rw [hpalette]
          exact hbaseBound
        have hsecondBound : t+j*((t+1)/2) ≤
            (((Finset.univ.filter (fun x : Fin b => x.val < sl₂.i ∧ localSide x = true)).map
              (op869_offset_emb sf.i h2)).biUnion (op869_splice_colors sf.i h2 sf.C sl₂.C)).card := by
          rw [op869_spliced_colors_biUnion]
          exact hlocalBound
        have hrootGame := op869_one_sided_root_game sf.i h2 sf.P sf.C sl₂.P sl₂.C baseSide localSide
          sl₂.i (t+j*((t+1)/2)) t hinvl₂.1 hroot
          (fun x hx => (hclear2 x hx).1) (fun x hx => (hinvl₂.2.2 x hx).1)
          hbaseSide hlocalSide S hSbefore hSside hfirstBound hsecondBound
        have hrootGoal : ∀ s : Op869SequentialState m,
            (∃ side : Fin m → Bool,
              (∀ x y, (op869_graph_from_predecessors s.P).Adj x y → side x ≠ side y) ∧
              (t+j*((t+1)/2))+(t+1)/2 ≤
                ((Finset.univ.filter (fun x : Fin m => x.val < s.i ∧ side x = true)).biUnion s.C).card) →
            op869_one_sided_goal t (j+1) s := by
          intro s hs
          rcases hs with ⟨side,hp,hc⟩
          refine ⟨side,hp,?_⟩
          have heq : t+(j+1)*((t+1)/2) = (t+j*((t+1)/2))+(t+1)/2 := by ring
          rw [heq]
          exact hc
        have hrootGame' := op869_game_goal_mono _ _ (op869_sequential_legal 2 m)
          (op869_sequential_valid t) op869_sequential_next hrootGoal 1 _ hrootGame
        right
        cases sg with
        | mk idx PP CC =>
          simp only [Op869SequentialState.i, Op869SequentialState.P, Op869SequentialState.C] at hidx hP hC
          subst idx
          subst PP
          subst CC
          exact hrootGame'
      right
      exact op869_game_early_bind (op869_one_sided_goal t (j+1))
        (fun sg => op869_prefix_invariant 2 sg ∧ secondGoal sg)
        (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next
        b 1 sf hsecond' hcont2
    have hcombined := op869_game_early_bind (op869_one_sided_goal t (j+1))
      (fun sf => op869_prefix_invariant 2 sf ∧ firstGoal sf)
      (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next
      b (b+1) ⟨0,E,F⟩ hfirst' hcont
    exact op869_sequential_fuel_mono_internal (op869_one_sided_goal t (j+1))
      (op869_sequential_legal 2 m) (op869_sequential_valid t) op869_sequential_next
      (b+(b+1)) m ⟨0,E,F⟩ hbudget hcombined

/-- The one-sided adaptive bipartite color-amplification gadget. -/
theorem op869_one_sided_bipartite_gadget :
  ∀ t j n : ℕ, 1 ≤ t → 2^(j+1)-1 ≤ n →
    op869_sequential_goal_game
      (fun s : Op869SequentialState n => ∃ side : Fin n → Bool,
        (∀ x y, (op869_graph_from_predecessors s.P).Adj x y → side x ≠ side y) ∧
        t+j*((t+1)/2) ≤
          ((Finset.univ.filter (fun x : Fin n => x.val < s.i ∧ side x = true)).biUnion s.C).card)
      (op869_sequential_legal 2 n) (op869_sequential_valid t) op869_sequential_next n
      ⟨0, (fun _ => ∅), (fun _ => ∅)⟩ := by
  intro t j n ht hn
  exact op869_one_sided_bipartite_gadget_proof t ht j n hn
