import AFTD.Prelude
import AFTD.Kb.Tcs.Op309PaddedBoundaryPort

/-!
# op309_padded_almost_star_port_graph_valid

Topic: graphs   Node: 0fc32617c476

Provenance: helper lemma. Padded port-class reduction in state/campaigns/op309-in1035-almost-star-port-route.md.

The port map respects local equalities and represents the port-color cliques of each P3, P4, and three-star, as well as original-edge properness at uncovered vertices.
-/

def op309_padded_almost_star_port_graph_valid {V W : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset G.edgeSet) (Q : SimpleGraph W)
    (q : Sum G.edgeSet (V × Fin 3) → W) : Prop :=
    let degree : V → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
    let selected : V → V → Prop := fun u v => s(u,v) ∈ R.image Subtype.val
    let port : Sum G.edgeSet (V × Fin 3) → V → Prop :=
      fun e v => op309_padded_boundary_port G R v e
    (∀ v : V, degree v = 0 → ∀ e f : G.edgeSet,
      e ∉ R → f ∉ R → v ∈ e.1 → v ∈ f.1 → e ≠ f →
      Q.Adj (q (.inl e)) (q (.inl f))) ∧
    (∀ a b c : V, [a,b,c].Nodup → selected a b → selected b c →
      degree a = 1 → degree b = 2 → degree c = 1 →
      ∀ ea ea' eb ec ec' : Sum G.edgeSet (V × Fin 3),
        port ea a → port ea' a → ea ≠ ea' → port eb b →
        port ec c → port ec' c → ec ≠ ec' →
        ((q ea = q ec ∧ q ea' = q ec') ∨ (q ea = q ec' ∧ q ea' = q ec)) ∧
        [q eb, q ea, q ea'].Pairwise Q.Adj) ∧
    (∀ a b c d : V, [a,b,c,d].Nodup → selected a b → selected b c → selected c d →
      degree a = 1 → degree b = 2 → degree c = 2 → degree d = 1 →
      ∀ ea ea' eb ec ed ed' : Sum G.edgeSet (V × Fin 3),
        port ea a → port ea' a → ea ≠ ea' → port eb b → port ec c →
        port ed d → port ed' d → ed ≠ ed' →
        ∃ (chooseA chooseD : Bool),
          let chosenA := if chooseA then ea else ea'
          let otherA := if chooseA then ea' else ea
          let chosenD := if chooseD then ed else ed'
          let otherD := if chooseD then ed' else ed
          q chosenA = q ec ∧ q chosenD = q eb ∧
          [q eb, q ec, q otherA, q otherD].Pairwise Q.Adj) ∧
    (∀ x a b d : V, [x,a,b,d].Nodup →
      selected x a → selected x b → selected x d →
      degree x = 3 → degree a = 1 → degree b = 1 → degree d = 1 →
      ∀ ea ea' eb eb' ed ed' : Sum G.edgeSet (V × Fin 3),
        port ea a → port ea' a → ea ≠ ea' →
        port eb b → port eb' b → eb ≠ eb' →
        port ed d → port ed' d → ed ≠ ed' →
        ((q ea = q eb ∧ q ea' = q eb') ∨ (q ea = q eb' ∧ q ea' = q eb)) ∧
        ((q ea = q ed ∧ q ea' = q ed') ∨ (q ea = q ed' ∧ q ea' = q ed)) ∧
        Q.Adj (q ea) (q ea'))
