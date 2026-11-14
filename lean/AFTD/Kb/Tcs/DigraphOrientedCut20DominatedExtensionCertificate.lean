import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOrientedCut20DominatedExtension
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExampleCertificate
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphOrientedCut20SharpExample

/-!
# digraph_oriented_cut20_dominated_extension_certificate

Topic: graphs   Node: ece3cde088cb

Provenance: helper lemma. Finite extension in experiment 26335; the robust two-cycle criterion is a known separate theorem.

The extended example is oriented, strongly connected, has minimum outdegree seven, a seven-outregular twenty-vertex part with cut twenty and no two cycles, and every two distinct vertices have a common predecessor.
-/

private instance in833_dominated_extension_decAdj : DecidableRel digraph_oriented_cut20_dominated_extension.Adj := by
  unfold digraph_oriented_cut20_dominated_extension
  infer_instance

/-- Truncation `Fin 39 → Fin 26` used to read arcs inside the twenty-vertex part
inside the sharp example on twenty-six vertices. -/
def digraph_oriented_cut20_dominated_extension_trunc (x : Fin 39) : Fin 26 :=
  ⟨x.val % 26, Nat.mod_lt _ (by norm_num)⟩

/-- The truncation is injective on the twenty-vertex part. -/
theorem digraph_oriented_cut20_dominated_extension_trunc_inj :
    ∀ a b : Fin 39, a.val < 20 → b.val < 20 →
      digraph_oriented_cut20_dominated_extension_trunc a
        = digraph_oriented_cut20_dominated_extension_trunc b → a = b := by
  decide

/-- On the twenty-vertex part the extended digraph agrees with the sharp example. -/
theorem digraph_oriented_cut20_dominated_extension_trunc_adj :
    ∀ a b : Fin 39, a.val < 20 → b.val < 20 →
      digraph_oriented_cut20_dominated_extension.Adj a b →
        digraph_oriented_cut20_sharp_example.Adj
          (digraph_oriented_cut20_dominated_extension_trunc a)
          (digraph_oriented_cut20_dominated_extension_trunc b) := by
  decide

/-- "Being a chain" is preserved by the truncation, provided the list stays inside a
set on which adjacency is carried to the sharp example. -/
theorem digraph_oriented_cut20_dominated_extension_isChain_map (s : Finset (Fin 39))
    (hadj : ∀ a ∈ s, ∀ b ∈ s, digraph_oriented_cut20_dominated_extension.Adj a b →
      digraph_oriented_cut20_sharp_example.Adj
        (digraph_oriented_cut20_dominated_extension_trunc a)
        (digraph_oriented_cut20_dominated_extension_trunc b))
    (l : List (Fin 39)) :
    List.IsChain digraph_oriented_cut20_dominated_extension.Adj l → (∀ x ∈ l, x ∈ s) →
      List.IsChain digraph_oriented_cut20_sharp_example.Adj
        (l.map digraph_oriented_cut20_dominated_extension_trunc) := by
  intro hc
  induction hc with
  | nil => intro _; exact List.IsChain.nil
  | singleton a => intro _; exact List.IsChain.singleton _
  | @cons_cons a b rest hab htail ih =>
      intro hmem
      exact List.IsChain.cons_cons
        (hadj a (hmem a (by simp)) b (hmem b (by simp)) hab)
        (ih (fun z hz => hmem z (by simp [hz])))

/-- Any directed cycle supported on the twenty-vertex part of the extended digraph
transports to a directed cycle of the sharp example on twenty-six vertices. -/
theorem digraph_oriented_cut20_dominated_extension_cycle_map (s : Finset (Fin 39))
    (hsub : ∀ x ∈ s, x.val < 20)
    (h : digraph_directed_cycle_on digraph_oriented_cut20_dominated_extension s) :
    digraph_directed_cycle_on digraph_oriented_cut20_sharp_example
      (s.image digraph_oriented_cut20_dominated_extension_trunc) := by
  classical
  obtain ⟨l, hnd, hlen, hts, hchain, a, b, hhead, hlast, hback⟩ := h
  have hmem : ∀ x ∈ l, x ∈ s := by
    intro x hx
    rw [← hts]
    exact List.mem_toFinset.2 hx
  have hsub' : ∀ x ∈ l, x.val < 20 := fun x hx => hsub x (hmem x hx)
  refine ⟨l.map digraph_oriented_cut20_dominated_extension_trunc, ?_, ?_, ?_, ?_,
    digraph_oriented_cut20_dominated_extension_trunc a,
    digraph_oriented_cut20_dominated_extension_trunc b, ?_, ?_, ?_⟩
  · exact List.Nodup.map_on (fun x hx y hy hxy =>
      digraph_oriented_cut20_dominated_extension_trunc_inj x y
        (hsub' x hx) (hsub' y hy) hxy) hnd
  · simpa using hlen
  · rw [← hts]
    ext x
    simp [List.mem_toFinset, List.mem_map, Finset.mem_image]
  · exact digraph_oriented_cut20_dominated_extension_isChain_map s (fun p hp q hq hab =>
      digraph_oriented_cut20_dominated_extension_trunc_adj p q
        (hsub p hp) (hsub q hq) hab) l hchain hmem
  · rw [List.head?_map, hhead]; rfl
  · rw [List.getLast?_map, hlast]; rfl
  · exact digraph_oriented_cut20_dominated_extension_trunc_adj b a
      (hsub' b (List.mem_of_mem_getLast? hlast)) (hsub' a (List.mem_of_mem_head? hhead)) hback

/-- Vertex `0` is a hub: it is reachable from every vertex in at most three steps and
reaches every vertex in at most two steps; hence the extended digraph is strongly
connected. -/
theorem digraph_oriented_cut20_dominated_extension_strong (u v : Fin 39) :
    Relation.ReflTransGen digraph_oriented_cut20_dominated_extension.Adj u v := by
  have hF : ∀ v : Fin 39, v = 0 ∨ digraph_oriented_cut20_dominated_extension.Adj 0 v ∨
      ∃ w, digraph_oriented_cut20_dominated_extension.Adj 0 w ∧
        digraph_oriented_cut20_dominated_extension.Adj w v := by decide
  have hB : ∀ u : Fin 39, u = 5 ∨ u = 0 ∨
      digraph_oriented_cut20_dominated_extension.Adj u 0 ∨
      ∃ w, digraph_oriented_cut20_dominated_extension.Adj u w ∧
        digraph_oriented_cut20_dominated_extension.Adj w 0 := by decide
  have a513 : digraph_oriented_cut20_dominated_extension.Adj 5 13 := by decide
  have a136 : digraph_oriented_cut20_dominated_extension.Adj 13 6 := by decide
  have a60 : digraph_oriented_cut20_dominated_extension.Adj 6 0 := by decide
  have h5 : Relation.ReflTransGen digraph_oriented_cut20_dominated_extension.Adj 5 0 :=
    Relation.ReflTransGen.head a513 (Relation.ReflTransGen.head a136
      (Relation.ReflTransGen.head a60 Relation.ReflTransGen.refl))
  have to0 : ∀ u : Fin 39,
      Relation.ReflTransGen digraph_oriented_cut20_dominated_extension.Adj u 0 := by
    intro u
    rcases hB u with h | h | h | ⟨w, h1, h2⟩
    · subst h; exact h5
    · subst h; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h1
        (Relation.ReflTransGen.head h2 Relation.ReflTransGen.refl)
  have from0 : ∀ v : Fin 39,
      Relation.ReflTransGen digraph_oriented_cut20_dominated_extension.Adj 0 v := by
    intro v
    rcases hF v with h | h | ⟨w, h1, h2⟩
    · subst h; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h1
        (Relation.ReflTransGen.head h2 Relation.ReflTransGen.refl)
  exact (to0 u).trans (from0 v)

theorem digraph_oriented_cut20_dominated_extension_certificate :
    let D := digraph_oriented_cut20_dominated_extension
    let B : Finset (Fin 39) := Finset.univ.filter fun v => v.val < 20
    (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
    (∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card) ∧
    (∀ v ∈ B, (Finset.univ.filter fun w => D.Adj v w).card = 7) ∧
    (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20 ∧
    (∀ u v, u ≠ v → ∃ w, D.Adj w u ∧ D.Adj w v) ∧
    (∀ u v, Relation.ReflTransGen D.Adj u v) ∧
    (¬ ∃ c : Fin 2 → Finset (Fin 39), (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact digraph_oriented_cut20_dominated_extension_strong
  · rintro ⟨c, hcyc, hdisj⟩
    refine digraph_oriented_cut20_sharp_example_certificate.2.2.2.1
      ⟨fun i => (c i).image digraph_oriented_cut20_dominated_extension_trunc, ?_, ?_⟩
    · intro i
      exact digraph_oriented_cut20_dominated_extension_cycle_map (c i)
        (fun x hx => by have := (hcyc i).1 hx; simpa using this) (hcyc i).2
    · intro i j hij
      refine Finset.disjoint_left.2 fun x hx1 hx2 => ?_
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx1
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 hx2
      have hia : a.val < 20 := by have := (hcyc i).1 ha; simpa using this
      have hjb : b.val < 20 := by have := (hcyc j).1 hb; simpa using this
      have hab : a = b :=
        digraph_oriented_cut20_dominated_extension_trunc_inj a b hia hjb hba.symm
      have hdis : Disjoint (c i) (c j) := hdisj hij
      rw [← hab] at hb
      exact (Finset.disjoint_left.1 hdis ha) hb
