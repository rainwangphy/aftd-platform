import AFTD.Prelude
import AFTD.Kb.Tcs.WeakenedCycleRamseyNumber
import AFTD.Kb.Tcs.ColorAvoidingSubgraph
import AFTD.Kb.Tcs.WeakenedCycleRamseyProperty

/-!
# not_op_1406_weakened_cycle_ramsey_number_ge_self

Topic: combinatorics   Node: ad26513b4b86

Provenance: original. Related work: refutes `op_1406_weakened_cycle_ramsey_number_ge_self`

The statement `op_1406_weakened_cycle_ramsey_number_ge_self` is false: The case t = 1 makes it false. weakened_cycle_ramsey_property t ℓ n demands that for every colouring c : (K_n).edgeSet → Fin t there is a colour j such that C_ℓ embeds in the subgraph of edges whose colour is ≠ j. When t = 1 (so the codomain is Fin 1), for every colouring c and every j : Fin 1 we have c e = j for all e (Subsingleton.elim), hence color_avoiding_subgraph (completeGraph (Fin n)) c j has no edges at all, i.e. equals ⊥. But for ℓ ≥ 3 the cycle graph C_ℓ has an edge (e.g. cycleGraph 3 has Adj 0 1), and a graph with an edge admits no homomorphism into ⊥ (map_adj gives an edge in ⊥, contradiction). Therefore weakened_cycle_ramsey_property 1 3 n is false for every n, so {n | weakened_cycle_ramsey_property 1 3 n} = ∅ and weakened_cycle_ramsey_number 1 3 = sInf ∅ = 0. Taking t = 1, ℓ = 3 (which satisfy 1 ≤ t and 3 ≤ ℓ) gives 3 ≤ 0, a contradiction. Hence the universally quantified statement is false; the paper's theorem needs t ≥ 2 (one needs at least two colours in order to avoid one of them).
-/

theorem not_op_1406_weakened_cycle_ramsey_number_ge_self : ¬ (∀ (t ℓ : ℕ) (ht : 1 ≤ t) (hℓ : 3 ≤ ℓ), ℓ ≤ weakened_cycle_ramsey_number t ℓ) := by
  intro h
  have h1 : 3 ≤ weakened_cycle_ramsey_number 1 3 := h 1 3 le_rfl (by norm_num)
  have h0 : weakened_cycle_ramsey_number 1 3 = 0 := by
    unfold weakened_cycle_ramsey_number
    have hset : {n : ℕ | weakened_cycle_ramsey_property 1 3 n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      obtain ⟨j, hom, hinj⟩ := hp (fun _ => (0 : Fin 1))
      rw [show color_avoiding_subgraph (SimpleGraph.completeGraph (Fin n)) (fun _ => (0 : Fin 1)) j = ⊥ from by
        ext a b
        rw [color_avoiding_subgraph, SimpleGraph.fromEdgeSet_adj]
        constructor
        · rintro ⟨⟨_, hne⟩, _⟩
          exact absurd (Subsingleton.elim _ j) hne
        · intro hh
          exact absurd hh (by simp)] at hom
      have hadj := hom.map_adj (show (SimpleGraph.cycleGraph 3).Adj 0 1 by decide)
      simp at hadj
    rw [hset, Nat.sInf_empty]
  omega
