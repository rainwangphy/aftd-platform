import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFreeTripleNeighbors
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.IsPkFree
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.G

/-!
# not_is_pk_free_claw_free_hole_dominating

Topic: graphs   Node: 4c22fa9ef4b7

Provenance: original. Related work: refutes `is_pk_free_claw_free_hole_dominating`

The statement `is_pk_free_claw_free_hole_dominating` is false: The statement is false as written: it allows k = 4 and m = 3 (since k - 1 = 3 ≤ 3). Counterexample: start from K4 on vertices {0,1,2,3} and attach a pendant vertex 4 adjacent only to 3 (i.e. the "paw"-like graph H = K4 with a pendant edge). Call it cex.

* cex is connected (0,1,2,3 form a clique and 4 is adjacent to 3).
* cex is P4-free: any induced P4 would need four vertices inducing a path; any four of {0,1,2,3} induce K4 minus at most one edge (contains a triangle, so not a path), and including vertex 4 (degree 1, neighbour 3 which is adjacent to everything else) always produces an induced P3 at most — checked exhaustively by `decide` over all injections Fin 4 → Fin 5.
* cex is claw-free: the claw needs a vertex with three pairwise non-adjacent neighbours; every vertex of cex has neighbourhood inducing a clique or a single edge — again checked exhaustively by `decide` over all injections Fin 1 ⊕ Fin 3 → Fin 5.
* The triangle {0,1,2} is an induced cycle C3 (embedding f5 of cycleGraph 3), and it is not dominating: vertex 4 is not in {0,1,2} and its only neighbour is 3, which is not in {0,1,2}.

So all hypotheses hold with k = 4, m = 3, yet `simple_graph_is_dominating cex (Set.range f5)` fails. The informal source presumably requires the hole to have length ≥ k (or k - 2 with a different constant, or the graph to be Claw-free AND P_k-free with k ≥ 5 plus the hole length being at least k - 1 meaning m ≥ k - 1 with m ≥ 5...). Note that for k = 4, k - 1 = 3, and triangles are never "long", so the bound k - 1 must be at least 5 (or m must be required to be ≥ k, since the argument uses an induced path on k vertices built from the hole plus a vertex at distance 2 from it, which needs the hole to have at least k - 1 vertices... actually the derivation needs a vertex outside the hole at distance exactly 2, and then the hole contributes 3 consecutive vertices, giving a P5 = k, which is why k ≥ 5 must be assumed).
-/

open SimpleGraph
universe u

/-- The counterexample graph: `K4` on `{0,1,2,3}` together with a pendant vertex `4` attached to `3`. -/
def not_is_pk_free_claw_free_hole_dominating_cex : SimpleGraph (ULift.{u,0} (Fin 5)) where
  Adj a b := (a ≠ b) ∧ (a = ULift.up (4 : Fin 5) → b = ULift.up (3 : Fin 5)) ∧
    (b = ULift.up (4 : Fin 5) → a = ULift.up (3 : Fin 5))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance not_is_pk_free_claw_free_hole_dominating_cex_decRel :
    DecidableRel not_is_pk_free_claw_free_hole_dominating_cex.Adj := by
  intro a b; unfold not_is_pk_free_claw_free_hole_dominating_cex; infer_instance

instance not_is_pk_free_claw_free_hole_dominating_bip_decRel :
    DecidableRel (completeBipartiteGraph (Fin 1) (Fin 3)).Adj := by
  intro a b; unfold completeBipartiteGraph; infer_instance

/-- The embedding of the triangle `C₃` into the counterexample. -/
def not_is_pk_free_claw_free_hole_dominating_toFun : Fin 3 → ULift.{u,0} (Fin 5) :=
  fun i => ULift.up ⟨i.val, by omega⟩

lemma not_is_pk_free_claw_free_hole_dominating_toFun_inj :
    Function.Injective not_is_pk_free_claw_free_hole_dominating_toFun := by
  intro a b h
  have h' := ULift.up_injective h
  ext
  simpa using congrArg Fin.val h'

lemma not_is_pk_free_claw_free_hole_dominating_rel_iff : ∀ a b : Fin 3,
    not_is_pk_free_claw_free_hole_dominating_cex.Adj
      (not_is_pk_free_claw_free_hole_dominating_toFun a)
      (not_is_pk_free_claw_free_hole_dominating_toFun b) ↔ (cycleGraph 3).Adj a b := by
  decide

/-- The triangle `{0,1,2}` as an induced cycle in the counterexample. -/
def not_is_pk_free_claw_free_hole_dominating_emb :
    SimpleGraph.cycleGraph 3 ↪g not_is_pk_free_claw_free_hole_dominating_cex :=
  RelEmbedding.mk
    ⟨not_is_pk_free_claw_free_hole_dominating_toFun,
      not_is_pk_free_claw_free_hole_dominating_toFun_inj⟩
    (by intro a b; exact not_is_pk_free_claw_free_hole_dominating_rel_iff a b)

lemma not_is_pk_free_claw_free_hole_dominating_step : ∀ i : Fin 4,
    not_is_pk_free_claw_free_hole_dominating_cex.Adj
      (ULift.up (Fin.castSucc i)) (ULift.up i.succ) := by
  intro i; fin_cases i <;> decide

lemma not_is_pk_free_claw_free_hole_dominating_reach : ∀ k : Fin 5,
    not_is_pk_free_claw_free_hole_dominating_cex.Reachable
      (ULift.up (0 : Fin 5)) (ULift.up k) := by
  intro k
  fin_cases k
  · exact SimpleGraph.Reachable.refl _
  · exact ⟨SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 0)
      SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 0)
      (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 1)
        SimpleGraph.Walk.nil)⟩
  · exact ⟨SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 0)
      (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 1)
        (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 2)
          SimpleGraph.Walk.nil))⟩
  · exact ⟨SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 0)
      (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 1)
        (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 2)
          (SimpleGraph.Walk.cons (not_is_pk_free_claw_free_hole_dominating_step 3)
            SimpleGraph.Walk.nil)))⟩

lemma not_is_pk_free_claw_free_hole_dominating_connected :
    not_is_pk_free_claw_free_hole_dominating_cex.Connected where
  preconnected := by
    rintro ⟨a⟩ ⟨b⟩
    exact (not_is_pk_free_claw_free_hole_dominating_reach a).symm.trans
      (not_is_pk_free_claw_free_hole_dominating_reach b)
  nonempty := ⟨ULift.up (0:Fin 5)⟩

lemma not_is_pk_free_claw_free_hole_dominating_no_pk_embed :
    ∀ g : Fin 4 → ULift.{u,0} (Fin 5),
      ¬ (∀ a b : Fin 4,
        not_is_pk_free_claw_free_hole_dominating_cex.Adj (g a) (g b) ↔
          ((a:ℕ)+1 = (b:ℕ) ∨ (b:ℕ)+1 = (a:ℕ))) := by
  decide

lemma not_is_pk_free_claw_free_hole_dominating_no_claw_embed :
    ∀ g : Fin 1 ⊕ Fin 3 → ULift.{u,0} (Fin 5), Function.Injective g →
      ¬ (∀ a b,
        not_is_pk_free_claw_free_hole_dominating_cex.Adj (g a) (g b) ↔
          (completeBipartiteGraph (Fin 1) (Fin 3)).Adj a b) := by
  decide

lemma not_is_pk_free_claw_free_hole_dominating_pk_free_four :
    IsPkFree not_is_pk_free_claw_free_hole_dominating_cex 4 := by
  rintro ⟨f⟩
  exact not_is_pk_free_claw_free_hole_dominating_no_pk_embed f.toFun
    (fun a b => f.map_rel_iff'.trans SimpleGraph.pathGraph_adj)

lemma not_is_pk_free_claw_free_hole_dominating_claw_free :
    IsClawFree not_is_pk_free_claw_free_hole_dominating_cex := by
  rintro ⟨f⟩
  exact not_is_pk_free_claw_free_hole_dominating_no_claw_embed f.toFun f.inj'
    (fun a b => f.map_rel_iff')

lemma not_is_pk_free_claw_free_hole_dominating_emb_not_mem :
    (ULift.up (4:Fin 5) : ULift.{u,0} (Fin 5)) ∉
      Set.range not_is_pk_free_claw_free_hole_dominating_emb := by
  simp only [Set.mem_range, not_exists]
  intro i
  fin_cases i <;> decide

lemma not_is_pk_free_claw_free_hole_dominating_emb_no_adj :
    ∀ i : Fin 3,
      ¬ not_is_pk_free_claw_free_hole_dominating_cex.Adj
        (not_is_pk_free_claw_free_hole_dominating_emb i) (ULift.up (4:Fin 5)) := by
  intro i
  fin_cases i <;> decide

theorem not_is_pk_free_claw_free_hole_dominating : ¬ (∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (k m : ℕ) (hk : IsPkFree G k) (hclaw : IsClawFree G)
    (hm : k - 1 ≤ m) (f : SimpleGraph.cycleGraph m ↪g G), simple_graph_is_dominating G (Set.range f)) := by
  intro h
  have hdom : simple_graph_is_dominating not_is_pk_free_claw_free_hole_dominating_cex
      (Set.range not_is_pk_free_claw_free_hole_dominating_emb) :=
    h (V := ULift (Fin 5)) not_is_pk_free_claw_free_hole_dominating_cex
      not_is_pk_free_claw_free_hole_dominating_connected 4 3
      not_is_pk_free_claw_free_hole_dominating_pk_free_four
      not_is_pk_free_claw_free_hole_dominating_claw_free (by norm_num)
      not_is_pk_free_claw_free_hole_dominating_emb
  rcases hdom (ULift.up (4:Fin 5)) with hmem | ⟨w, ⟨i, hi⟩, hadj⟩
  · exact not_is_pk_free_claw_free_hole_dominating_emb_not_mem hmem
  · exact not_is_pk_free_claw_free_hole_dominating_emb_no_adj i (hi.symm ▸ hadj)
