import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CausalLinearNetworkCode

/-!
# linear_code_supports_rate_unit_edge

Topic: information   Node: a858da246799

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Non-vacuity of LinearCodeSupportsRate: on the two-vertex graph with a single unit-capacity edge, with the single session 0 -> 1, a deterministic causal binary linear network code with one transmission slot and one message symbol (T = 1, L = 1, M = 1) supports rate 1.
-/

/-- The single unit-capacity edge with one session admits a one-slot binary linear code at rate 1. -/
theorem linear_code_supports_rate_unit_edge :
  ∃ (net : CapacitatedNetwork (Fin 2)) (sess : UnicastSessions (Fin 2) (Fin 1)),
    net.cap s((0 : Fin 2), (1 : Fin 2)) = 1 ∧
    sess.src (0 : Fin 1) = (0 : Fin 2) ∧ sess.tgt (0 : Fin 1) = (1 : Fin 2) ∧
    LinearCodeSupportsRate (ZMod 2) net sess 1 := by
  have hsym : ∀ e : Sym2 (Fin 2), ¬ e.IsDiag → e = s((0 : Fin 2), (1 : Fin 2)) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at he
      fin_cases a <;> fin_cases b <;> simp_all
  let net : CapacitatedNetwork (Fin 2) :=
    { G := ⊤
      decAdj := Classical.decRel _
      cap := fun e => if e = s((0 : Fin 2), (1 : Fin 2)) then 1 else 0
      cap_pos := by
        intro e he
        rw [SimpleGraph.edgeSet_top] at he
        simp only [Set.mem_compl_iff, Sym2.mem_diagSet] at he
        rw [if_pos (hsym e he)]
        norm_num
      cap_zero := by
        intro e he
        rw [if_neg]
        intro h
        apply he
        rw [h, SimpleGraph.mem_edgeSet]
        simp }
  let sess : UnicastSessions (Fin 2) (Fin 1) :=
    { src := fun _ => 0
      tgt := fun _ => 1
      src_ne_tgt := by intro k; fin_cases k; simp }
  refine ⟨net, sess, ?_, ?_, ?_, ?_⟩
  · simp [net]
  · simp [sess]
  · simp [sess]
  · unfold LinearCodeSupportsRate
    refine ⟨?_, ?_⟩
    · refine
        { M := 1, T := 1, L := 1
          hT := by norm_num
          hL := by norm_num
          snd := fun _ => 0
          rcv := fun _ => 1
          snd_ne_rcv := ?_
          cap_le := ?_
          α := fun _ _ _ => 1
          β := fun _ _ => 0
          γ := fun _ _ _ => 1
          causal := ?_
          snd_local := ?_
          rcv_local := ?_
          dec_local := ?_
          correct := ?_ }
      · intro m; fin_cases m; simp
      · intro e
        simp only [net]
        by_cases h : e = s((0 : Fin 2), (1 : Fin 2))
        · rw [if_pos h, h]
          simp
        · rw [if_neg h]
          simp
          exact fun hh => h hh.symm
      · intro m m' h; simp at h
      · intro m k j h; simp [sess]
      · intro m m' h; simp at h
      · intro k j m h; simp [sess]
      · intro msg
        refine ⟨fun _ => msg 0 0, ?_, ?_⟩
        · intro m
          fin_cases m
          simp
        · intro k j
          fin_cases k
          fin_cases j
          simp
    · norm_num
