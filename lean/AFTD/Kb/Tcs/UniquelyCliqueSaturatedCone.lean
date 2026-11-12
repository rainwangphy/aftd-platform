import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated
import AFTD.Kb.Tcs.SimpleGraphCone

/-!
# uniquely_clique_saturated_cone

Topic: graphs   Node: 47d7d5a47656

Provenance: helper lemma. arXiv:2611.13656 Proposition 2.1 (ii)

Let r ≥ 3 be an integer, and let G be a finite simple graph. If G is uniquely K_r-saturated, then the cone G ∨ K_1 is uniquely K_{r+1}-saturated.
-/

open scoped Sym2

/-- The embedding `V ↪ Option V` sending `v` to `some v`. -/
private def ucscEmb {V : Type*} : V ↪ Option V := Function.Embedding.some

/-- The vertices of `G` encoded in a finite set of vertices of the cone `G ∨ K_1`. -/
private noncomputable def ucscVerts {V : Type*} (t : Finset (Option V)) : Finset V :=
  t.preimage Option.some (fun _ _ _ _ h => Option.some.inj h)

private lemma ucscVerts_mem {V : Type*} {t : Finset (Option V)} {x : V} :
    x ∈ ucscVerts t ↔ some x ∈ t := Finset.mem_preimage

/-- The cliques of the cone `H ∨ K_1` are exactly the images of the cliques of `H`. -/
private lemma ucsc_cone_isClique {V : Type*} (H : SimpleGraph V) (t : Finset (Option V)) :
    (simple_graph_cone H).IsClique (↑t : Set (Option V)) ↔ H.IsClique (↑(ucscVerts t) : Set V) := by
  rw [SimpleGraph.isClique_iff, SimpleGraph.isClique_iff]
  constructor
  · intro h p hp q hq hpq
    exact h (ucscVerts_mem.mp hp) (ucscVerts_mem.mp hq) (fun hc => hpq (Option.some.inj hc))
  · intro h p hp q hq hpq
    cases p with
    | none =>
      cases q with
      | none => exact absurd rfl hpq
      | some q => trivial
    | some p =>
      cases q with
      | none => trivial
      | some q =>
        exact h (ucscVerts_mem.mpr hp) (ucscVerts_mem.mpr hq) (fun hc => hpq (by rw [hc]))

/-- Coning commutes with adjoining the edge `{a,b}`. -/
private lemma ucsc_cone_sup {V : Type*} (G : SimpleGraph V) (a b : V) :
    simple_graph_cone (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}) =
      simple_graph_cone G ⊔ SimpleGraph.fromEdgeSet {s(Option.some a, Option.some b)} := by
  ext u v
  cases u <;> cases v <;>
    simp [simple_graph_cone, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]

private lemma ucscVerts_insert_none_map {V : Type*} [DecidableEq V] (u : Finset V) :
    ucscVerts (insert none (u.map ucscEmb)) = u := by
  classical
  ext x
  rw [ucscVerts_mem, Finset.mem_insert]
  simp [ucscEmb]

private lemma ucsc_not_mem_map_none {V : Type*} (u : Finset V) : (none : Option V) ∉ u.map ucscEmb := by
  classical
  rw [Finset.mem_map]
  rintro ⟨x, -, hx⟩
  simp only [ucscEmb] at hx
  exact absurd hx (by simp)

private lemma ucscVerts_map {V : Type*} [DecidableEq V] (t : Finset (Option V)) :
    (ucscVerts t).map ucscEmb = t.erase none := by
  classical
  ext y
  cases y with
  | none => rw [Finset.mem_erase]; simp [ucscVerts_mem, ucscEmb]
  | some z =>
      rw [Finset.mem_erase, Finset.mem_map]
      constructor
      · rintro ⟨a, ha, haz⟩
        rw [ucscVerts_mem] at ha
        simp only [ucscEmb] at haz
        exact ⟨by simp, haz ▸ ha⟩
      · rintro ⟨-, hz⟩
        exact ⟨z, by rw [ucscVerts_mem]; exact hz, rfl⟩

private lemma ucscVerts_insert_none {V : Type*} [DecidableEq V] {t : Finset (Option V)}
    (h : none ∈ t) : insert none ((ucscVerts t).map ucscEmb) = t := by
  classical
  rw [ucscVerts_map, Finset.insert_erase h]

private lemma ucscVerts_card_add_one {V : Type*} [DecidableEq V] {t : Finset (Option V)}
    (h : none ∈ t) : (ucscVerts t).card + 1 = t.card := by
  classical
  calc (ucscVerts t).card + 1
      = ((ucscVerts t).map ucscEmb).card + 1 := by rw [Finset.card_map]
    _ = (insert none ((ucscVerts t).map ucscEmb)).card := by
          rw [Finset.card_insert_of_notMem (ucsc_not_mem_map_none _)]
    _ = t.card := by rw [ucscVerts_insert_none h]

private lemma ucscVerts_card_of_not_mem {V : Type*} [DecidableEq V] {t : Finset (Option V)}
    (h : none ∉ t) : (ucscVerts t).card = t.card := by
  classical
  calc (ucscVerts t).card
      = ((ucscVerts t).map ucscEmb).card := (Finset.card_map _).symm
    _ = (t.erase none).card := by rw [ucscVerts_map]
    _ = t.card := by rw [Finset.erase_eq_of_notMem h]

/-- If `S` is the unique `r`-clique of `H`, then `H` has no `(r+1)`-clique. -/
private lemma ucsc_no_nclique_succ {V : Type*} [DecidableEq V] (H : SimpleGraph V) {r : ℕ}
    (hr : 1 ≤ r) (S : Finset V)
    (hun : ∀ y : Finset V, H.IsNClique r y → y = S) :
    ∀ w : Finset V, ¬ H.IsNClique (r + 1) w := by
  intro w hw
  rw [SimpleGraph.isNClique_iff] at hw
  obtain ⟨hcl, hcard⟩ := hw
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < w.card)
  have hcard1 : (w.erase c).card = r := by
    rw [Finset.card_erase_of_mem hc, hcard]; omega
  have hcl1 : H.IsClique (↑(w.erase c) : Set V) :=
    hcl.subset (fun x hx => Finset.mem_of_mem_erase hx)
  have heq1 : w.erase c = S := hun _ (by rw [SimpleGraph.isNClique_iff]; exact ⟨hcl1, hcard1⟩)
  obtain ⟨c', hc'⟩ := Finset.card_pos.mp (by omega : 0 < (w.erase c).card)
  have hc'w : c' ∈ w := Finset.mem_of_mem_erase hc'
  have hcard2 : (w.erase c').card = r := by
    rw [Finset.card_erase_of_mem hc'w, hcard]; omega
  have hcl2 : H.IsClique (↑(w.erase c') : Set V) :=
    hcl.subset (fun x hx => Finset.mem_of_mem_erase hx)
  have heq2 : w.erase c' = S := hun _ (by rw [SimpleGraph.isNClique_iff]; exact ⟨hcl2, hcard2⟩)
  have hmem : c' ∈ w.erase c' := by rw [heq2, ← heq1]; exact hc'
  rw [Finset.mem_erase] at hmem
  exact hmem.1 rfl

/-- The cone G ∨ K_1 of a uniquely K_r-saturated graph is uniquely K_{r+1}-saturated. -/
theorem uniquely_clique_saturated_cone
    {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hG : is_uniquely_clique_saturated G r) :
    is_uniquely_clique_saturated (simple_graph_cone G) (r + 1) := by
  classical
  rw [is_uniquely_clique_saturated] at hG ⊢
  obtain ⟨hno, huniq⟩ := hG
  constructor
  · intro t ht
    rw [SimpleGraph.isNClique_iff] at ht
    obtain ⟨hcl, hcard⟩ := ht
    have hcl' : G.IsClique (↑(ucscVerts t) : Set V) := (ucsc_cone_isClique G t).mp hcl
    by_cases hnone : none ∈ t
    · have hc : (ucscVerts t).card = r := by
        have h := ucscVerts_card_add_one hnone
        omega
      exact hno _ (by rw [SimpleGraph.isNClique_iff]; exact ⟨hcl', hc⟩)
    · have hc : (ucscVerts t).card = r + 1 := by
        rw [ucscVerts_card_of_not_mem hnone]; exact hcard
      obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq (s := ucscVerts t) (n := r) (by omega)
      have hclu : G.IsClique (↑u : Set V) :=
        hcl'.subset (fun x hx => Finset.mem_coe.mpr (husub (Finset.mem_coe.mp hx)))
      exact hno _ (by rw [SimpleGraph.isNClique_iff]; exact ⟨hclu, hucard⟩)
  · intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at he
      obtain ⟨hne, hnonadj⟩ := he
      cases u with
      | none =>
        cases v with
        | none => exact absurd rfl hne
        | some b => exact absurd trivial hnonadj
      | some a =>
        cases v with
        | none => exact absurd trivial hnonadj
        | some b =>
          have hnab : ¬ G.Adj a b := hnonadj
          have habne : a ≠ b := fun h => hne (by rw [h])
          have heG : s(a, b) ∈ Gᶜ.edgeSet := by
            rw [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
            exact ⟨habne, hnab⟩
          obtain ⟨S, hS, hSuniq⟩ := huniq _ heG
          rw [SimpleGraph.isNClique_iff] at hS
          obtain ⟨hScl, hScard⟩ := hS
          rw [← ucsc_cone_sup G a b]
          refine ⟨insert none (S.map ucscEmb), ?_, ?_⟩
          · simp only [SimpleGraph.isNClique_iff]
            refine ⟨?_, ?_⟩
            · rw [ucsc_cone_isClique, ucscVerts_insert_none_map]
              exact hScl
            · rw [Finset.card_insert_of_notMem (ucsc_not_mem_map_none S), Finset.card_map, hScard]
          · intro t ht
            simp only [SimpleGraph.isNClique_iff] at ht
            obtain ⟨htcl, htcard⟩ := ht
            have htcl' : (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).IsClique (↑(ucscVerts t) : Set V) :=
              (ucsc_cone_isClique _ t).mp htcl
            by_cases hnone : none ∈ t
            · have hc : (ucscVerts t).card = r := by
                have h := ucscVerts_card_add_one hnone
                omega
              have hn : (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).IsNClique r (ucscVerts t) := by
                rw [SimpleGraph.isNClique_iff]; exact ⟨htcl', hc⟩
              have heq : ucscVerts t = S := hSuniq _ hn
              have hins : insert none ((ucscVerts t).map ucscEmb) = t := ucscVerts_insert_none hnone
              rw [heq] at hins
              exact hins.symm
            · have hc : (ucscVerts t).card = r + 1 := by
                rw [ucscVerts_card_of_not_mem hnone]; exact htcard
              have hn : (G ⊔ SimpleGraph.fromEdgeSet {s(a, b)}).IsNClique (r+1) (ucscVerts t) := by
                rw [SimpleGraph.isNClique_iff]; exact ⟨htcl', hc⟩
              exact absurd hn (ucsc_no_nclique_succ _ (by omega) S hSuniq _)
