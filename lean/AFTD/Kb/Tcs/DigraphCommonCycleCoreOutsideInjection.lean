import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonCycleCoreNeighborUnique
import AFTD.Kb.Tcs.DigraphIsDirectedPath
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_common_cycle_core_outside_injection

Topic: graphs   Node: c6d6b603f3fa

Provenance: helper lemma. Common-cycle core counting for the oriented twenty-cut profile.

In a strongly connected finite vertex set, suppose all directed cycles contain a core K and every vertex in a subset S of K has at least two outneighbors inside the set. Then there are at least |S| vertices outside K.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem digraph_common_cycle_core_outside_injection
    (α : Type) [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (T K S : Finset α) (hKT : K ⊆ T) (hSK : S ⊆ K)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hstrong : ∀ u ∈ T, ∀ v ∈ T,
      ∃ p : List α, digraph_is_directed_path D p u v ∧ ∀ z ∈ p, z ∈ T)
    (hcore : ∀ C : Finset α, C ⊆ T → digraph_directed_cycle_on D C → K ⊆ C)
    (hdeg : ∀ v ∈ S, 2 ≤ (T.filter fun w => D.Adj v w).card) :
    S.card ≤ (T \ K).card := by
  classical
  have hu := digraph_common_cycle_core_neighbor_unique α D T K hKT hloop hstrong hcore
  have hex : ∀ s ∈ S, ∃ x ∈ T \ K, D.Adj s x := by
    intro s hs
    have hsK : s ∈ K := hSK hs
    have hsT : s ∈ T := hKT hsK
    by_contra hn
    have hsub : (T.filter fun w => D.Adj s w) ⊆ (K.filter fun w => D.Adj s w) := by
      intro w hw
      have hwT : w ∈ T := (Finset.mem_filter.mp hw).1
      have hadj : D.Adj s w := (Finset.mem_filter.mp hw).2
      have hwK : w ∈ K := by
        by_contra hwK
        exact hn ⟨w,Finset.mem_sdiff.mpr ⟨hwT,hwK⟩,hadj⟩
      exact Finset.mem_filter.mpr ⟨hwK,hadj⟩
    have hc := Finset.card_le_card hsub
    have hd := hdeg s hs
    have hbound := (hu s hsT).1
    omega
  let f : {s : α // s ∈ S} → {x : α // x ∈ T \ K} := fun s =>
    ⟨(hex s.val s.property).choose, (hex s.val s.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    have ax := (hex a.val a.property).choose_spec.2
    have bx := (hex b.val b.property).choose_spec.2
    have hx : (f a).val = (f b).val := congrArg Subtype.val heq
    have hxT : (f a).val ∈ T := (Finset.mem_sdiff.mp (f a).property).1
    have haK : a.val ∈ K := hSK a.property
    have hbK : b.val ∈ K := hSK b.property
    have hcard := (hu (f a).val hxT).2
    apply (Finset.card_le_one.mp hcard) a.val (Finset.mem_filter.mpr ⟨haK, ax⟩)
      b.val (Finset.mem_filter.mpr ⟨hbK, ?_⟩)
    change D.Adj b.val (f b).val at bx
    simpa [hx] using bx
  have hh := Fintype.card_le_of_injective f hf
  simpa using hh
