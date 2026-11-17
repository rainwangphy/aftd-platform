import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# enc1385Game

Topic: automata   Node: 5f2ad36c924a

Provenance: helper lemma. Block-encoded phase arena for arXiv:2611.10136, Conjecture 19.

Given a finite-state three-priority tree game, construct a phase-state game that encodes each original direction followed by a one-hot target-state code, uses zero priorities before the final bit, and pulls the winning branch sets back through the projection to block-leading bits. Invalid prefixes have a deterministic fallback so every position has a legal move.
-/

structure Enc1385State (Q : Type) where
  origNode : List Bool
  origState : Q
  pending : List Bool

noncomputable def enc1385StateCode {Q : Type} [Fintype Q] (q : Q) : List Bool := by
  classical
  exact List.ofFn (fun i : Fin (Fintype.card Q) => decide (i = Fintype.equivFin Q q))

noncomputable def enc1385Block {Q : Type} [Fintype Q] (e : TreeGameEdge Q 3) : List Bool :=
  e.dir :: enc1385StateCode e.target_state

noncomputable def enc1385Decode {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (bits : List Bool) : Q := by
  classical
  exact if h : ∃ q : Q, enc1385StateCode q = bits then Classical.choose h else G.init_state

noncomputable def enc1385Step {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (s : Enc1385State Q) (bit : Bool) : Enc1385State Q := by
  let bits := s.pending ++ [bit]
  exact if bits.length = Fintype.card Q + 1 then
    ⟨s.origNode ++ [bits.headD false], enc1385Decode G bits.tail, []⟩
  else ⟨s.origNode, s.origState, bits⟩

noncomputable def enc1385Real {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (s : Enc1385State Q) (bit : Bool) (prio : Fin 3) : Prop :=
  ∃ e ∈ G.edges, e.source_node = s.origNode ∧ e.source_state = s.origState ∧
    s.pending ++ [bit] <+: enc1385Block e ∧
    (if (s.pending ++ [bit]).length = Fintype.card Q + 1 then prio = e.prio else prio = 0)

noncomputable def enc1385Allowed {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (s : Enc1385State Q) (bit : Bool) (prio : Fin 3) : Prop :=
  enc1385Real G s bit prio ∨
    ((¬ ∃ bit' prio', enc1385Real G s bit' prio') ∧ bit = false ∧ prio = 0)

lemma enc1385_allowed_exists {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (s : Enc1385State Q) : ∃ bit prio, enc1385Allowed G s bit prio := by
  classical
  by_cases h : ∃ bit prio, enc1385Real G s bit prio
  · obtain ⟨bit, prio, h⟩ := h
    exact ⟨bit, prio, Or.inl h⟩
  · exact ⟨false, 0, Or.inr ⟨h, rfl, rfl⟩⟩

noncomputable def enc1385Game {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) :
    PrioritizedBorelGame (Enc1385State Q) 3 where
  owner := fun vq => G.owner (vq.2.origNode, vq.2.origState)
  init_state := ⟨[], G.init_state, []⟩
  edges := {e | e.target_state = enc1385Step G e.source_state e.dir ∧
    enc1385Allowed G e.source_state e.dir e.prio}
  edges_outgoing := by
    intro v s
    obtain ⟨bit, prio, h⟩ := enc1385_allowed_exists G s
    exact ⟨⟨v, s, bit, prio, enc1385Step G s bit⟩, ⟨rfl, h⟩, rfl, rfl⟩
  winning_sets := fun p => {β | (fun n => β (n * (Fintype.card Q + 1))) ∈ G.winning_sets p}
  winning_measurable := by
    intro p
    apply (G.winning_measurable p).preimage
    exact measurable_pi_lambda _ (fun n => measurable_pi_apply _)
