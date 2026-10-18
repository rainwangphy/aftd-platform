import AFTD.Prelude
import AFTD.Kb.Tcs.HandshakeUpdateContam
import AFTD.Kb.Tcs.Handshake

/-!
# seq_contam

Topic: combinatorics   Node: c9579356430f

Provenance: helper lemma. step towards glove_number_k4

The contamination map obtained by running the handshake sequence `seq` starting from the contamination map `t`. (This is the index-free version of the paper's contamination sequence `t_a(i)`.)
-/

/-- The contamination map after executing the sequence `seq`, starting from `t`. -/
def seq_contam {V : Type*} {Γ : Type*} [DecidableEq Γ] (seq : List (Handshake V Γ)) (t : Γ × Bool → Set V) : Γ × Bool → Set V := seq.foldl (fun t h => handshake_update_contam h t) t
