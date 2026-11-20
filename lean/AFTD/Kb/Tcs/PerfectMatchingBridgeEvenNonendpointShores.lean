import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# perfect_matching_bridge_even_nonendpoint_shores

Topic: graphs   Node: 3a8710343af5

Provenance: helper lemma. OP-1957 factor-critical forced-bridge shore construction.

A matched bridge gives two even nonendpoint shores, grouping any extra components on one side.
-/

theorem perfect_matching_bridge_even_nonendpoint_shores {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (x z : V)
    (hxz : P.Adj x z) (hbridge : ¬ (G.deleteEdges {s(x,z)}).Reachable x z) :
    ∃ Q W : Finset V, Disjoint Q W ∧ Q ∪ W ∪ {x,z} = Finset.univ ∧
      x ∉ Q ∧ z ∉ Q ∧ x ∉ W ∧ z ∉ W ∧ Even Q.card ∧ Even W.card ∧
      (∀ q ∈ Q, ¬ G.Adj z q) ∧ (∀ w ∈ W, ¬ G.Adj x w) ∧
      (∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w) := by
  classical
  let F := G.deleteEdges {s(x,z)}
  have hxzG := P.adj_sub hxz
  have hxz_ne : x ≠ z := hxzG.ne
  have hz_not_x : ¬ F.Reachable z x := by
    intro h
    exact hbridge h.symm
  let W : Finset V := Finset.univ.filter (fun a => a ≠ z ∧ F.Reachable z a)
  let Q : Finset V := Finset.univ.filter (fun a => a ≠ x ∧ ¬ F.Reachable z a)
  have hW : ∀ a, a ∈ W ↔ a ≠ z ∧ F.Reachable z a := by intro a; simp [W]
  have hQ : ∀ a, a ∈ Q ↔ a ≠ x ∧ ¬ F.Reachable z a := by intro a; simp [Q]
  have hxW : x ∉ W := by simp [hW, hz_not_x]
  have hzW : z ∉ W := by simp [hW]
  have hxQ : x ∉ Q := by simp [hQ]
  have hzQ : z ∉ Q := by simp [hQ, SimpleGraph.Reachable.refl]
  have hdis : Disjoint Q W := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact ((hQ a).mp ha).2 ((hW a).mp hb).2
  have hpart : Q ∪ W ∪ {x,z} = Finset.univ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
    by_cases hax : a = x
    · exact Or.inr (Or.inl hax)
    · by_cases haz : a = z
      · exact Or.inr (Or.inr haz)
      · by_cases hreach : F.Reachable z a
        · exact Or.inl (Or.inr ((hW a).mpr ⟨haz,hreach⟩))
        · exact Or.inl (Or.inl ((hQ a).mpr ⟨hax,hreach⟩))
  have hedge : ∀ a b, a ≠ x → a ≠ z → b ≠ x → b ≠ z → G.Adj a b → F.Adj a b := by
    intro a b hax haz hbx hbz hab
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simp [Sym2.eq_iff,hax,haz,hbx,hbz]⟩
  have hzQadj : ∀ q ∈ Q, ¬ G.Adj z q := by
    intro q hq h
    have hqx := ((hQ q).mp hq).1
    have hqz : q ≠ z := fun h => hzQ (h ▸ hq)
    have hF : F.Adj z q := SimpleGraph.deleteEdges_adj.mpr ⟨h, by simp [Sym2.eq_iff,hxz_ne.symm,hqx,hqz]⟩
    exact ((hQ q).mp hq).2 hF.reachable
  have hxWadj : ∀ w ∈ W, ¬ G.Adj x w := by
    intro w hw h
    have hwz := ((hW w).mp hw).1
    have hwx : w ≠ x := fun h => hxW (h ▸ hw)
    have hF : F.Adj x w := SimpleGraph.deleteEdges_adj.mpr ⟨h, by simp [Sym2.eq_iff,hxz_ne,hwx,hwz]⟩
    exact hz_not_x (((hW w).mp hw).2.trans hF.symm.reachable)
  have hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w := by
    intro q hq w hw h
    have hqx := ((hQ q).mp hq).1
    have hqz : q ≠ z := fun h => hzQ (h ▸ hq)
    have hwz := ((hW w).mp hw).1
    have hwx : w ≠ x := fun h => hxW (h ▸ hw)
    have hF := hedge q w hqx hqz hwx hwz h
    exact ((hQ q).mp hq).2 (((hW w).mp hw).2.trans hF.symm.reachable)
  let T := P.induce {a | a ∈ W}
  have hT : T.IsMatching := by
    intro a ha
    have haW : a ∈ W := ha
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
    have haz : a ≠ z := ((hW a).mp haW).1
    have hax : a ≠ x := fun h => hxW (h ▸ haW)
    have hbx : b ≠ x := by
      intro h
      subst b
      have hza : z = a := hP.1.eq_of_adj_left hxz hab.symm
      exact haz hza.symm
    have hbz : b ≠ z := by
      intro h
      subst b
      have hxa : x = a := hP.1.eq_of_adj_right hxz hab
      exact hax hxa.symm
    have habF := hedge a b hax haz hbx hbz (P.adj_sub hab)
    have hbW : b ∈ W := (hW b).mpr ⟨hbz, ((hW a).mp haW).2.trans habF.reachable⟩
    refine ⟨b, ⟨haW,hbW,hab⟩, ?_⟩
    intro c hc
    exact huniq c hc.2.2
  have hWeven : Even W.card := by simpa [T] using hT.even_card
  have hpair : Disjoint (Q ∪ W) ({x,z} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_union] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact ha.elim hxQ hxW
    · exact ha.elim hzQ hzW
  have hcard : Q.card + W.card + 2 = Fintype.card V := by
    have h := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hpair, Finset.card_union_of_disjoint hdis,
      Finset.card_pair hxz_ne, Finset.card_univ] at h
    exact h
  have heven := hP.even_card
  have hQeven : Even Q.card := by
    obtain ⟨a,ha⟩ := heven
    obtain ⟨b,hb⟩ := hWeven
    refine ⟨a-b-1, ?_⟩
    omega
  exact ⟨Q,W,hdis,hpart,hxQ,hzQ,hxW,hzW,hQeven,hWeven,hzQadj,hxWadj,hcross⟩
