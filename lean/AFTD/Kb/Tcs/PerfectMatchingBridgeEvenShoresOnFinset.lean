import AFTD.Prelude
import AFTD.Kb.Tcs.PerfectMatchingBridgeEvenNonendpointShores
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# perfect_matching_bridge_even_shores_on_finset

Topic: graphs   Node: dc909b1053d0

Provenance: helper lemma. OP-1957 factor-critical forced-bridge shore construction.

A matched bridge in an induced finite graph gives even nonendpoint shores as finite subsets of the original vertex set.
-/

theorem perfect_matching_bridge_even_shores_on_finset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (x z : V) (hx : x ∈ R) (hz : z ∈ R)
    (P : (G.induce {a | a ∈ R}).Subgraph) (hP : P.IsPerfectMatching)
    (hxz : P.Adj ⟨x,hx⟩ ⟨z,hz⟩)
    (hbridge : ¬ ((G.induce {a | a ∈ R}).deleteEdges
      {s(⟨x,hx⟩,⟨z,hz⟩)}).Reachable ⟨x,hx⟩ ⟨z,hz⟩) :
    ∃ Q W : Finset V, Disjoint Q W ∧ Q ∪ W ∪ {x,z} = R ∧
      x ∉ Q ∧ z ∉ Q ∧ x ∉ W ∧ z ∉ W ∧ Even Q.card ∧ Even W.card ∧
      (∀ q ∈ Q, ¬ G.Adj z q) ∧ (∀ w ∈ W, ¬ G.Adj x w) ∧
      (∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w) := by
  classical
  obtain ⟨Q',W',hdis,hpart,hxQ,hzQ,hxW,hzW,hqe,hwe,hzq,hxw,hcross⟩ :=
    perfect_matching_bridge_even_nonendpoint_shores _ P hP ⟨x,hx⟩ ⟨z,hz⟩ hxz hbridge
  let Q : Finset V := Q'.image Subtype.val
  let W : Finset V := W'.image Subtype.val
  have hQ : ∀ a, a ∈ Q ↔ ∃ q ∈ Q', q.val = a := by intro a; simp [Q]
  have hW : ∀ a, a ∈ W ↔ ∃ w ∈ W', w.val = a := by intro a; simp [W]
  have hd : Disjoint Q W := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨q,hq,hqa⟩ := (hQ a).mp ha
    obtain ⟨w,hw,hwa⟩ := (hW a).mp hb
    have h : q = w := Subtype.ext (hqa.trans hwa.symm)
    exact (Finset.disjoint_left.mp hdis) hq (h ▸ hw)
  have huniv : Finset.univ.image (Subtype.val : {a : V // a ∈ R} → V) = R := by
    ext a
    simp
  have hpart' : Q ∪ W ∪ {x,z} = R := by
    have hp := congrArg (Finset.image (Subtype.val : {a : V // a ∈ R} → V)) hpart
    simp only [Finset.image_union, Finset.image_insert, Finset.image_singleton,
      Subtype.coe_mk] at hp
    change Q ∪ W ∪ {x,z} = _ at hp
    rw [huniv] at hp
    exact hp
  have hxQ' : x ∉ Q := by
    rintro h
    obtain ⟨q,hq,hqx⟩ := (hQ x).mp h
    have he : q = (⟨x,hx⟩ : {a : V // a ∈ R}) := Subtype.ext hqx
    exact hxQ (he ▸ hq)
  have hzQ' : z ∉ Q := by
    rintro h
    obtain ⟨q,hq,hqz⟩ := (hQ z).mp h
    have he : q = (⟨z,hz⟩ : {a : V // a ∈ R}) := Subtype.ext hqz
    exact hzQ (he ▸ hq)
  have hxW' : x ∉ W := by
    rintro h
    obtain ⟨w,hw,hwx⟩ := (hW x).mp h
    have he : w = (⟨x,hx⟩ : {a : V // a ∈ R}) := Subtype.ext hwx
    exact hxW (he ▸ hw)
  have hzW' : z ∉ W := by
    rintro h
    obtain ⟨w,hw,hwz⟩ := (hW z).mp h
    have he : w = (⟨z,hz⟩ : {a : V // a ∈ R}) := Subtype.ext hwz
    exact hzW (he ▸ hw)
  have hqe' : Even Q.card := by simpa [Q, Finset.card_image_of_injective _ Subtype.val_injective] using hqe
  have hwe' : Even W.card := by simpa [W, Finset.card_image_of_injective _ Subtype.val_injective] using hwe
  have hzq' : ∀ q ∈ Q, ¬ G.Adj z q := by
    intro q hq
    obtain ⟨q',hq',rfl⟩ := (hQ q).mp hq
    exact hzq q' hq'
  have hxw' : ∀ w ∈ W, ¬ G.Adj x w := by
    intro w hw
    obtain ⟨w',hw',rfl⟩ := (hW w).mp hw
    exact hxw w' hw'
  have hcross' : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w := by
    intro q hq w hw
    obtain ⟨q',hq',rfl⟩ := (hQ q).mp hq
    obtain ⟨w',hw',rfl⟩ := (hW w).mp hw
    exact hcross q' hq' w' hw'
  exact ⟨Q,W,hd,hpart',hxQ',hzQ',hxW',hzW',hqe',hwe',hzq',hxw',hcross'⟩
