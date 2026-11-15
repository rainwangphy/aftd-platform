import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph

/-!
# simple_graph_reconfiguration_exists_walk_le_three_halves_of_bipartite

Topic: graphs   Node: bc6e5a233cba

Provenance: helper lemma. arXiv:2611.17022 Lemma 6 -- Large diameter for (Δ+2)-colouring reconfiguration

Let G be a finite bipartite simple graph on a type V with decidable equality and decidable adjacency. For every integer k ≥ G.maxDegree + 2 and any two proper k-colourings α and β of G with colours in Fin k, there exists a walk in the k-colouring reconfiguration graph of G from α to β of length at most 3 * Fintype.card V / 2.
-/

theorem rc32_assign {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) (g : V → Fin k)
    (s : Finset V) (hs : ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w) :
    ∀ γ : G.Coloring (Fin k), (∀ v ∈ s, ∀ w, G.Adj v w → g v ≠ γ w) →
      ∃ γ' : G.Coloring (Fin k), (∀ v, γ' v = if v ∈ s then g v else γ v) ∧
        ∃ w : (simple_graph_reconfiguration_graph G k).Walk γ γ',
          w.length ≤ (s.filter (fun v => γ v ≠ g v)).card := by
  induction s using Finset.induction_on with
  | empty =>
    intro γ _
    exact ⟨γ, fun v => by simp, SimpleGraph.Walk.nil, by simp⟩
  | @insert a s ha ih =>
    intro γ hval
    have hs' : ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w := fun v hv w hw =>
      hs v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw)
    obtain ⟨γ1, h1, w1, hw1⟩ := ih hs' γ (fun v hv w hvw =>
      hval v (Finset.mem_insert_of_mem hv) w hvw)
    have hcard : (s.filter (fun v => γ v ≠ g v)).card ≤
        ((insert a s).filter (fun v => γ v ≠ g v)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hga : γ a = g a
    · refine ⟨γ1, fun v => ?_, w1, hw1.trans hcard⟩
      rw [h1 v]
      by_cases hv : v = a
      · subst hv
        simp [ha, hga]
      · simp [hv]
    · have hnbr : ∀ w, G.Adj a w → g a ≠ γ1 w := by
        intro w haw
        have hw : w ∉ s := fun hw =>
          hs a (Finset.mem_insert_self _ _) w (Finset.mem_insert_of_mem hw) haw
        rw [h1 w, if_neg hw]
        exact hval a (Finset.mem_insert_self _ _) w haw
      let γ2 : G.Coloring (Fin k) :=
        SimpleGraph.Coloring.mk (Function.update γ1 a (g a)) (by
          intro x y hxy
          by_cases hx : x = a
          · subst hx
            have hy : y ≠ x := fun h => by subst h; exact G.irrefl hxy
            rw [Function.update_self, Function.update_of_ne hy]
            exact hnbr y hxy
          · by_cases hy : y = a
            · subst hy
              rw [Function.update_self, Function.update_of_ne hx]
              exact (hnbr x hxy.symm).symm
            · rw [Function.update_of_ne hx, Function.update_of_ne hy]
              exact γ1.valid hxy)
      have hγ2 : ∀ v, γ2 v = Function.update γ1 a (g a) v := fun v => rfl
      have hγ1a : γ1 a = γ a := by rw [h1 a, if_neg ha]
      have hadj : (simple_graph_reconfiguration_graph G k).Adj γ1 γ2 := by
        refine ⟨a, ?_, ?_⟩
        · show γ1 a ≠ γ2 a
          rw [hγ2, Function.update_self, hγ1a]
          exact hga
        · intro u hu
          change γ1 u ≠ γ2 u at hu
          by_contra hua
          exact hu (by rw [hγ2, Function.update_of_ne hua])
      refine ⟨γ2, fun v => ?_, w1.concat hadj, ?_⟩
      · rw [hγ2]
        by_cases hv : v = a
        · subst hv
          simp
        · rw [Function.update_of_ne hv, h1 v]
          simp [hv]
      · rw [SimpleGraph.Walk.length_concat, Finset.filter_insert, if_pos hga,
          Finset.card_insert_of_notMem (by simp [ha])]
        omega

theorem rc32_free {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : G.maxDegree + 2 ≤ k) (f : V → Fin k) (c : Fin k) (v : V) :
    ∃ x : Fin k, x ≠ c ∧ ∀ w, G.Adj v w → f w ≠ x := by
  have hlt : (insert c ((G.neighborFinset v).image f)).card <
      (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc (insert c ((G.neighborFinset v).image f)).card
        ≤ ((G.neighborFinset v).image f).card + 1 := Finset.card_insert_le _ _
      _ ≤ (G.neighborFinset v).card + 1 := Nat.add_le_add_right Finset.card_image_le _
      _ ≤ G.maxDegree + 1 := by
          rw [G.card_neighborFinset_eq_degree]
          exact Nat.add_le_add_right (G.degree_le_maxDegree v) _
      _ < k := by omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨x, fun h => hx (h ▸ Finset.mem_insert_self _ _), fun w hw hfx => hx ?_⟩
  exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨w, by simpa using hw, hfx⟩)

theorem rc32_route {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : G.maxDegree + 2 ≤ k) (A B : Finset V)
    (hcov : ∀ v, v ∈ A ∨ v ∈ B) (hdisj : ∀ v, v ∈ A → v ∉ B)
    (hA : ∀ v ∈ A, ∀ w ∈ A, ¬ G.Adj v w) (hB : ∀ v ∈ B, ∀ w ∈ B, ¬ G.Adj v w)
    (c : Fin k) (α β : G.Coloring (Fin k)) :
    ∃ w : (simple_graph_reconfiguration_graph G k).Walk α β,
      w.length + (A.filter (fun v => α v = c)).card + (A.filter (fun v => β v = c)).card ≤
        2 * A.card + B.card + (B.filter (fun v => α v = c)).card +
          (B.filter (fun v => β v = c)).card := by
  have otherA : ∀ v w, v ∈ A → G.Adj v w → w ∈ B := fun v w hv hvw =>
    (hcov w).resolve_left (fun hw => hA v hv w hw hvw)
  have otherB : ∀ v w, v ∈ B → G.Adj v w → w ∈ A := fun v w hv hvw =>
    (hcov w).resolve_right (fun hw => hB v hv w hw hvw)
  choose F1 hF1c hF1 using rc32_free G hk α c
  choose F3 hF3c hF3 using rc32_free G hk β c
  -- phase 1: move B off colour c
  obtain ⟨γ1, e1, w1, l1⟩ := rc32_assign G k (fun v => if α v = c then F1 v else α v) B hB α
    (by
      intro v hv w hvw
      by_cases h : α v = c
      · rw [if_pos h]; exact (hF1 v w hvw).symm
      · rw [if_neg h]; exact α.valid hvw)
  -- phase 2: colour A with c
  obtain ⟨γ2, e2, w2, l2⟩ := rc32_assign G k (fun _ => c) A hA γ1
    (by
      intro v hv w hvw
      have hw := otherA v w hv hvw
      rw [e1 w, if_pos hw]
      by_cases h : α w = c
      · rw [if_pos h]; exact (hF1c w).symm
      · rw [if_neg h]; exact Ne.symm h)
  -- phase 3: B to β, parking the vertices whose β-colour is c
  obtain ⟨γ3, e3, w3, l3⟩ := rc32_assign G k (fun v => if β v ≠ c then β v else F3 v) B hB γ2
    (by
      intro v hv w hvw
      have hw := otherB v w hv hvw
      rw [e2 w, if_pos hw]
      by_cases h : β v ≠ c
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact hF3c v)
  -- phase 4: A to β
  obtain ⟨γ4, e4, w4, l4⟩ := rc32_assign G k (fun v => β v) A hA γ3
    (by
      intro v hv w hvw
      have hw := otherA v w hv hvw
      rw [e3 w, if_pos hw]
      by_cases h : β w ≠ c
      · rw [if_pos h]; exact β.valid hvw
      · rw [if_neg h]; exact hF3 w v hvw.symm)
  -- phase 5: B to β
  obtain ⟨γ5, e5, w5, l5⟩ := rc32_assign G k (fun v => β v) B hB γ4
    (by
      intro v hv w hvw
      have hw := otherB v w hv hvw
      rw [e4 w, if_pos hw]
      exact β.valid hvw)
  have h5 : γ5 = β := by
    ext v
    rw [e5 v]
    by_cases hv : v ∈ B
    · rw [if_pos hv]
    · rw [if_neg hv, e4 v, if_pos ((hcov v).resolve_right hv)]
  refine ⟨((((w1.append w2).append w3).append w4).append w5).copy rfl h5, ?_⟩
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append]
  -- cost bounds
  have c1 : (B.filter (fun v => α v ≠ (if α v = c then F1 v else α v))).card ≤
      (B.filter (fun v => α v = c)).card := by
    apply Finset.card_le_card
    intro v
    simp only [Finset.mem_filter]
    rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    by_contra hc
    exact h (by rw [if_neg hc])
  have c2 : (A.filter (fun v => γ1 v ≠ c)).card + (A.filter (fun v => α v = c)).card =
      A.card := by
    have : A.filter (fun v => γ1 v ≠ c) = A.filter (fun v => ¬ α v = c) := by
      apply Finset.filter_congr
      intro v hv
      rw [e1 v, if_neg (hdisj v hv)]
    rw [this, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have c3 : (B.filter (fun v => γ2 v ≠ (if β v ≠ c then β v else F3 v))).card ≤ B.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have c4 : (A.filter (fun v => γ3 v ≠ β v)).card + (A.filter (fun v => β v = c)).card =
      A.card := by
    have : A.filter (fun v => γ3 v ≠ β v) = A.filter (fun v => ¬ β v = c) := by
      apply Finset.filter_congr
      intro v hv
      rw [e3 v, if_neg (hdisj v hv), e2 v, if_pos hv]
      exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
    rw [this, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have hdisj' : ∀ v, v ∈ B → v ∉ A := fun v hv hvA => hdisj v hvA hv
  have c5 : (B.filter (fun v => γ4 v ≠ β v)).card ≤ (B.filter (fun v => β v = c)).card := by
    apply Finset.card_le_card
    intro v
    simp only [Finset.mem_filter]
    rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    rw [e4 v, if_neg (hdisj' v hv), e3 v, if_pos hv] at h
    by_contra hc
    exact h (by rw [if_pos hc])
  omega

/-- Any two proper k-colourings of a bipartite graph are joined in the reconfiguration graph by a walk of length at most ⌊3n/2⌋ when k ≥ Δ + 2. -/
theorem simple_graph_reconfiguration_exists_walk_le_three_halves_of_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite)
    {k : ℕ} (hk : G.maxDegree + 2 ≤ k)
    (α β : G.Coloring (Fin k)) :
    ∃ w : (simple_graph_reconfiguration_graph G k).Walk α β,
      w.length ≤ 3 * Fintype.card V / 2 := by
  obtain ⟨χ⟩ := hG
  have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ ¬ b = 0) := by decide
  set A := Finset.univ.filter (fun v => χ v = 0) with hAdef
  set B := Finset.univ.filter (fun v => ¬ χ v = 0) with hBdef
  have hcov : ∀ v, v ∈ A ∨ v ∈ B := by
    intro v
    by_cases h : χ v = 0
    · exact Or.inl (by simp [hAdef, h])
    · exact Or.inr (by simp [hBdef, h])
  have hdisj : ∀ v, v ∈ A → v ∉ B := by
    intro v hv hv'
    simp only [hAdef, hBdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact hv' hv
  have hA : ∀ v ∈ A, ∀ w ∈ A, ¬ G.Adj v w := by
    intro v hv w hw hvw
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    exact (key _ _ (χ.valid hvw)).1 hv hw
  have hB : ∀ v ∈ B, ∀ w ∈ B, ¬ G.Adj v w := by
    intro v hv w hw hvw
    simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    exact hw ((key _ _ (χ.valid hvw.symm)).2 hv)
  have hcard : A.card + B.card = Fintype.card V := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hk2 : 0 < k := by omega
  obtain ⟨w1, h1⟩ := rc32_route G hk A B hcov hdisj hA hB ⟨0, hk2⟩ α β
  obtain ⟨w2, h2⟩ := rc32_route G hk B A (fun v => (hcov v).symm)
    (fun v hv hvA => hdisj v hvA hv) hB hA ⟨0, hk2⟩ α β
  by_cases hle : w1.length ≤ w2.length
  · exact ⟨w1, by omega⟩
  · exact ⟨w2, by omega⟩
