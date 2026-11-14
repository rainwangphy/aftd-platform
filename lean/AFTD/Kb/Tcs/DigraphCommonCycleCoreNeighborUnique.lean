import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_common_cycle_core_neighbor_unique

Topic: graphs   Node: 1a660db3b27a

Provenance: helper lemma. Common-cycle core argument for the oriented twenty-cut profile; experiment 26272 checks all oriented graphs through five vertices.

Inside a strongly connected finite set, if every directed cycle contains a fixed core, every vertex has at most one outgoing neighbor and at most one incoming neighbor in that core.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private theorem in833_path_close_cycle {α : Type} [DecidableEq α]
    (D : Digraph α) (p : List α) (a b : α)
    (hpath : digraph_is_directed_path D p a b) (hne : a ≠ b) (hclose : D.Adj b a) :
    digraph_directed_cycle_on D p.toFinset := by
  obtain ⟨hchain, hnodup, hhead, hlast⟩ := hpath
  have hlen : 2 ≤ p.length := by
    cases p with
    | nil => simp at hhead
    | cons z zs =>
      cases zs with
      | nil => simp_all
      | cons w ws => simp
  exact ⟨p, hnodup, hlen, rfl, hchain, a, b, hhead, hlast, hclose⟩

private theorem in833_core_out_unique
    (α : Type) [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (T S : Finset α) (hST : S ⊆ T)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hstrong : ∀ u ∈ T, ∀ v ∈ T,
      ∃ p : List α, digraph_is_directed_path D p u v ∧ ∀ z ∈ p, z ∈ T)
    (hcore : ∀ C : Finset α, C ⊆ T → digraph_directed_cycle_on D C → S ⊆ C) :
    ∀ x ∈ T, (S.filter fun y => D.Adj x y).card ≤ 1 := by
  classical
  intro x hx
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have haS : a ∈ S := (Finset.mem_filter.mp ha).1
  have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
  have hxa : D.Adj x a := (Finset.mem_filter.mp ha).2
  have hxb : D.Adj x b := (Finset.mem_filter.mp hb).2
  by_contra hab
  have hax : a ≠ x := by intro h; subst a; exact (hloop x) hxa
  have hbx : b ≠ x := by intro h; subst b; exact (hloop x) hxb
  obtain ⟨p,hpath,hpT⟩ := hstrong a (hST haS) x hx
  obtain ⟨hchain, hnodup, hhead, hlast⟩ := hpath
  by_cases hbp : b ∈ p
  · obtain ⟨pre,tail,hp⟩ := List.mem_iff_append.mp hbp
    cases pre with
    | nil =>
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hp hhead
      have : a = b := by simpa [hp] using hhead.symm
      exact hab this
    | cons z zs =>
      have hz : z = a := by
        rw [hp] at hhead
        simpa using hhead
      subst z
      have hnodup' : ((a :: zs) ++ b :: tail).Nodup := by simpa [hp] using hnodup
      have hsufnodup : (b :: tail).Nodup := (List.nodup_append.mp hnodup').2.1
      have hnot : a ∉ b :: tail := by
        intro ha'
        exact (List.nodup_append.mp hnodup').2.2 a (by simp) a ha' rfl
      have hchain' : ((a :: zs) ++ b :: tail).IsChain D.Adj := by simpa [hp] using hchain
      have hsufchain : (b :: tail).IsChain D.Adj := hchain'.right_of_append
      have hsuflast : (b :: tail).getLast? = some x := by
        rw [hp, List.getLast?_append_cons] at hlast
        exact hlast
      have hsufpath : digraph_is_directed_path D (b :: tail) b x :=
        ⟨hsufchain, hsufnodup, by simp, hsuflast⟩
      have hcycle := in833_path_close_cycle D (b :: tail) b x hsufpath hbx hxb
      have hsub : (b :: tail).toFinset ⊆ T := by
        intro y hy
        have hy' : y ∈ b :: tail := by simpa using hy
        apply hpT y
        rw [hp]
        exact List.mem_append_right _ hy'
      have hc := hcore (b :: tail).toFinset hsub hcycle haS
      exact hnot (by simpa using hc)
  · have hcycle := in833_path_close_cycle D p a x ⟨hchain,hnodup,hhead,hlast⟩ hax hxa
    have hsub : p.toFinset ⊆ T := by
      intro y hy
      apply hpT y
      simpa using hy
    have hc := hcore p.toFinset hsub hcycle hbS
    exact hbp (by simpa using hc)

private theorem in833_core_reverse_cycle {α : Type} [DecidableEq α]
    (D : Digraph α) (C : Finset α)
    (h : digraph_directed_cycle_on ⟨fun u v => D.Adj v u⟩ C) :
    digraph_directed_cycle_on D C := by
  obtain ⟨l, hnodup, hlen, hset, hchain, a, b, ha, hb, hab⟩ := h
  refine ⟨l.reverse, ?_, ?_, ?_, ?_, b, a, ?_, ?_, ?_⟩
  · exact List.nodup_reverse.mpr hnodup
  · simpa using hlen
  · simpa using hset
  · exact List.isChain_reverse.mpr hchain
  · simpa using hb
  · simpa using ha
  · exact hab

theorem digraph_common_cycle_core_neighbor_unique
    (α : Type) [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (T S : Finset α) (hST : S ⊆ T)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hstrong : ∀ u ∈ T, ∀ v ∈ T,
      ∃ p : List α, digraph_is_directed_path D p u v ∧ ∀ z ∈ p, z ∈ T)
    (hcore : ∀ C : Finset α, C ⊆ T → digraph_directed_cycle_on D C → S ⊆ C) :
    ∀ x ∈ T, (S.filter fun y => D.Adj x y).card ≤ 1 ∧
      (S.filter fun y => D.Adj y x).card ≤ 1 := by
  classical
  have hout := in833_core_out_unique α D T S hST hloop hstrong hcore
  let E : Digraph α := ⟨fun u v => D.Adj v u⟩
  have hEloop : ∀ v, ¬ E.Adj v v := hloop
  have hEstrong : ∀ u ∈ T, ∀ v ∈ T,
      ∃ p : List α, digraph_is_directed_path E p u v ∧ ∀ z ∈ p, z ∈ T := by
    intro u hu v hv
    obtain ⟨p,hp,hT⟩ := hstrong v hv u hu
    obtain ⟨hc,hn,hh,hl⟩ := hp
    refine ⟨p.reverse, ?_, ?_⟩
    · refine ⟨?_, by simpa using hn, ?_, ?_⟩
      · exact List.isChain_reverse.mpr hc
      · simpa using hl
      · simpa using hh
    · intro z hz
      apply hT z
      simpa using hz
  have hEcore : ∀ C : Finset α, C ⊆ T → digraph_directed_cycle_on E C → S ⊆ C := by
    intro C hsub hc
    exact hcore C hsub (in833_core_reverse_cycle D C hc)
  have hin := in833_core_out_unique α E T S hST hEloop hEstrong hEcore
  intro x hx
  refine ⟨hout x hx, ?_⟩
  simpa [E] using hin x hx
