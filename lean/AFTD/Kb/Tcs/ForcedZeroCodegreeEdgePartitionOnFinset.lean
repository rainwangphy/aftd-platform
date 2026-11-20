import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedZeroCodegreeEdgeGivesOddBridgePartition

/-!
# forced_zero_codegree_edge_partition_on_finset

Topic: graphs   Node: e7e724b47980

Provenance: helper lemma. OP-1957 uniform bridge-family endpoint bound.

The forced zero-codegree edge partition lifts from an induced graph to the original finite vertex set.
-/

theorem forced_zero_codegree_edge_partition_on_finset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S)
    (P : (G.induce {a | a ∈ S}).Subgraph) (hP : P.IsPerfectMatching)
    (huv : P.Adj ⟨u,hu⟩ ⟨v,hv⟩)
    (hforced : ∀ Q : (G.induce {a | a ∈ S}).Subgraph, Q.IsPerfectMatching → Q.Adj ⟨u,hu⟩ ⟨v,hv⟩)
    (hco : ∀ a ∈ S, ¬ ((Gᶜ).Adj u a ∧ (Gᶜ).Adj v a)) :
    ∃ A B : Finset V, u ∈ A ∧ v ∈ B ∧ Disjoint A B ∧ A ∪ B = S ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v := by
  classical
  have hco' : ∀ a : {a : V // a ∈ S}, ¬ (((G.induce {a | a ∈ S})ᶜ).Adj ⟨u,hu⟩ a ∧
      ((G.induce {a | a ∈ S})ᶜ).Adj ⟨v,hv⟩ a) := by
    intro a h
    have hu' : (Gᶜ).Adj u a.val := ⟨fun he => h.1.1 (Subtype.ext he), h.1.2⟩
    have hv' : (Gᶜ).Adj v a.val := ⟨fun he => h.2.1 (Subtype.ext he), h.2.2⟩
    exact hco a.val a.property ⟨hu',hv'⟩
  obtain ⟨A',B',huA,hvB,hdis,hpart,-,-,hcut⟩ :=
    forced_zero_codegree_edge_gives_odd_bridge_partition _ P hP ⟨u,hu⟩ ⟨v,hv⟩ huv hforced hco'
  let A : Finset V := A'.image Subtype.val
  let B : Finset V := B'.image Subtype.val
  have hA : ∀ a, a ∈ A ↔ ∃ a' ∈ A', a'.val = a := by intro a; simp [A]
  have hB : ∀ b, b ∈ B ↔ ∃ b' ∈ B', b'.val = b := by intro b; simp [B]
  have huA' : u ∈ A := (hA u).mpr ⟨⟨u,hu⟩,huA,rfl⟩
  have hvB' : v ∈ B := (hB v).mpr ⟨⟨v,hv⟩,hvB,rfl⟩
  have hdis' : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨a',ha',hea⟩ := (hA a).mp ha
    obtain ⟨b',hb',heb⟩ := (hB a).mp hb
    have he : a' = b' := Subtype.ext (hea.trans heb.symm)
    exact (Finset.disjoint_left.mp hdis) ha' (he ▸ hb')
  have huniv : Finset.univ.image (Subtype.val : {a : V // a ∈ S} → V) = S := by ext a; simp
  have hpart' : A ∪ B = S := by
    have hp := congrArg (Finset.image (Subtype.val : {a : V // a ∈ S} → V)) hpart
    simp only [Finset.image_union] at hp
    change A ∪ B = _ at hp
    rw [huniv] at hp
    exact hp
  refine ⟨A,B,huA',hvB',hdis',hpart',?_⟩
  intro a ha b hb hab
  obtain ⟨a',ha',rfl⟩ := (hA a).mp ha
  obtain ⟨b',hb',rfl⟩ := (hB b).mp hb
  obtain ⟨h1,h2⟩ := hcut a' ha' b' hb' hab
  exact ⟨congrArg Subtype.val h1,congrArg Subtype.val h2⟩
