import AFTD.Prelude

/-!
# matchable_anticomplete_intersection_even

Topic: graphs   Node: 332b2b59938a

Provenance: helper lemma. OP-1957 bridge-shore parity reduction.

Any anticomplete side of a vertex set inducing a perfect matching has even cardinality.
-/

theorem matchable_anticomplete_intersection_even {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W A : Finset V)
    (hmatch : ∃ P : (G.induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching)
    (hcross : ∀ a ∈ W, a ∈ A → ∀ b ∈ W, b ∉ A → ¬ G.Adj a b) :
    Even (W ∩ A).card := by
  classical
  obtain ⟨P,hP⟩ := hmatch
  let U : Set {a : V // a ∈ W} := {a | a.val ∈ A}
  let T := P.induce U
  have hT : T.IsMatching := by
    intro a ha
    have haU : a ∈ U := ha
    obtain ⟨b,hab,huniq⟩ := hP.1 (hP.2 a)
    have hbU : b ∈ U := by
      by_contra hb
      exact hcross a.val a.property haU b.val b.property hb (P.adj_sub hab)
    refine ⟨b, ⟨haU,hbU,hab⟩, ?_⟩
    intro c hc
    exact huniq c hc.2.2
  have heven := hT.even_card
  have hcard : U.toFinset.card = (W ∩ A).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      exact Finset.mem_inter.mpr ⟨a.property, by simpa [U] using ha⟩
    · intro a ha b hb h
      exact Subtype.ext h
    · intro a ha
      obtain ⟨haW,haA⟩ := Finset.mem_inter.mp ha
      refine ⟨⟨a,haW⟩, ?_, rfl⟩
      simpa [U] using haA
  simpa [T,hcard] using heven
