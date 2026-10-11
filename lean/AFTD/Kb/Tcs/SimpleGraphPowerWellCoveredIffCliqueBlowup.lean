import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowup
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowupEdist

/-!
# simple_graph_power_well_covered_iff_clique_blowup

Topic: graphs   Node: 6abca38fd333

Provenance: helper lemma. The per-d form of the argument proving arXiv:2610.09300 (On graphs whose powers are well-covered), Theorem 1.6 (Claim 2 there: maximal independent sets of H^d are exactly one vertex from Q_i for each v_i in a maximal independent set of G^d).

For every d ≥ 1 and positive integers a_i, G^d is well-covered iff H^d is well-covered, where H = G[K_{a_1}, …, K_{a_n}].
-/

theorem simple_graph_clique_blowup_power_adj_iff {V : Type*} (G : SimpleGraph V) (a : V → ℕ)
    (ha : ∀ i, 0 < a i) (d : ℕ) (hd : 1 ≤ d) (p q : Σ i, Fin (a i)) :
    (simple_graph_power (simple_graph_clique_blowup G a) d).Adj p q ↔
      p ≠ q ∧ (p.1 = q.1 ∨ (simple_graph_power G d).Adj p.1 q.1) := by
  simp only [simple_graph_power]
  constructor
  · rintro ⟨hne, hle⟩
    refine ⟨hne, ?_⟩
    by_cases h : p.1 = q.1
    · exact Or.inl h
    · right; exact ⟨h, by rwa [← simple_graph_clique_blowup_edist G a ha p q h]⟩
  · rintro ⟨hne, h | ⟨h1, h2⟩⟩
    · refine ⟨hne, ?_⟩
      have hadj : (simple_graph_clique_blowup G a).Adj p q := Or.inl ⟨h, hne⟩
      rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]; exact_mod_cast hd
    · exact ⟨hne, by rwa [simple_graph_clique_blowup_edist G a ha p q h1]⟩

theorem simple_graph_power_well_covered_iff_clique_blowup {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : V → ℕ) (ha : ∀ i, 0 < a i) (d : ℕ) (hd : 1 ≤ d) :
    simple_graph_is_well_covered (simple_graph_power G d) ↔
      simple_graph_is_well_covered (simple_graph_power (simple_graph_clique_blowup G a) d) := by
  set Gd := simple_graph_power G d
  set Hd := simple_graph_power (simple_graph_clique_blowup G a) d
  have hA := simple_graph_clique_blowup_power_adj_iff G a ha d hd
  -- independence in Hd
  have indep_iff : ∀ I : Finset (Σ i, Fin (a i)), Hd.IsIndepSet (I : Set (Σ i, Fin (a i))) ↔
      (Set.InjOn (Sigma.fst : (Σ i, Fin (a i)) → V) (I : Set (Σ i, Fin (a i))) ∧ Gd.IsIndepSet ((I.image Sigma.fst : Finset V) : Set V)) := by
    intro I
    constructor
    · intro hI
      refine ⟨fun x hx y hy hxy => ?_, ?_⟩
      · by_contra hne
        exact hI hx hy hne ((hA x y).2 ⟨hne, Or.inl hxy⟩)
      · intro i hi j hj hij hadj
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hi hj
        obtain ⟨x, hx, rfl⟩ := hi
        obtain ⟨y, hy, rfl⟩ := hj
        have hne : x ≠ y := fun e => hij (e ▸ rfl)
        exact hI hx hy hne ((hA x y).2 ⟨hne, Or.inr hadj⟩)
    · rintro ⟨hinj, hJ⟩ x hx y hy hne hadj
      obtain ⟨-, h | h⟩ := (hA x y).1 hadj
      · exact hne (hinj hx hy h)
      · refine hJ ?_ ?_ (Gd.ne_of_adj h) h
        · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨x, hx, rfl⟩
        · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨y, hy, rfl⟩
  -- lift of a set of parts
  let L : Finset V → Finset (Σ i, Fin (a i)) := fun J => J.image (fun i => ⟨i, ⟨0, ha i⟩⟩)
  have L_inj : Function.Injective (fun i : V => (⟨i, ⟨0, ha i⟩⟩ : Σ i, Fin (a i))) := by
    intro i j h; exact congrArg Sigma.fst h
  have L_card : ∀ J, (L J).card = J.card := fun J => Finset.card_image_of_injective _ L_inj
  have L_fst : ∀ J, (L J).image Sigma.fst = J := by
    intro J; ext x; simp [L]
  -- maximal independent sets correspond
  have max_proj : ∀ I, Maximal (fun u : Finset (Σ i, Fin (a i)) => Hd.IsIndepSet (u : Set (Σ i, Fin (a i)))) I →
      Maximal (fun u : Finset V => Gd.IsIndepSet (u : Set V)) (I.image Sigma.fst) ∧
        (I.image Sigma.fst).card = I.card := by
    intro I hI
    obtain ⟨hinj, hJ⟩ := (indep_iff I).1 hI.1
    refine ⟨⟨hJ, fun t ht hsub => ?_⟩, Finset.card_image_of_injOn hinj⟩
    intro k hk
    by_contra hkn
    set z : Σ i, Fin (a i) := ⟨k, ⟨0, ha k⟩⟩
    have hzI : z ∉ I := fun hz => hkn (Finset.mem_image.2 ⟨z, hz, rfl⟩)
    have hind : Hd.IsIndepSet ((insert z I : Finset (Σ i, Fin (a i))) : Set (Σ i, Fin (a i))) := by
      intro x hx y hy hne hadj
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      have hnz : ∀ x ∈ I, ¬ Hd.Adj z x := by
        intro x hx h
        obtain ⟨-, h | h⟩ := (hA z x).1 h
        · exact hkn (Finset.mem_image.2 ⟨x, hx, h.symm⟩)
        · exact ht hk (hsub (Finset.mem_image.2 ⟨x, hx, rfl⟩)) (Gd.ne_of_adj h) h
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hne rfl
      · exact hnz y hy hadj
      · exact hnz x hx hadj.symm
      · exact hI.1 hx hy hne hadj
    have := hI.2 hind (Finset.subset_insert _ _)
    exact hzI (this (Finset.mem_insert_self _ _))
  have max_lift : ∀ J, Maximal (fun u : Finset V => Gd.IsIndepSet (u : Set V)) J →
      Maximal (fun u : Finset (Σ i, Fin (a i)) => Hd.IsIndepSet (u : Set (Σ i, Fin (a i)))) (L J) := by
    intro J hJ
    have hindL : Hd.IsIndepSet ((L J : Finset (Σ i, Fin (a i))) : Set (Σ i, Fin (a i))) := by
      refine (indep_iff _).2 ⟨?_, by rw [L_fst]; exact hJ.1⟩
      intro x hx y hy hxy
      simp only [L, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨j, -, rfl⟩ := hy
      simp only at hxy; subst hxy; rfl
    refine ⟨hindL, fun t ht hsub => ?_⟩
    intro y hy
    by_contra hyn
    by_cases hyJ : y.1 ∈ J
    · -- y is in the same part as a member of L J
      have hmem : (⟨y.1, ⟨0, ha y.1⟩⟩ : Σ i, Fin (a i)) ∈ L J :=
        Finset.mem_image.2 ⟨y.1, hyJ, rfl⟩
      have hne : y ≠ ⟨y.1, ⟨0, ha y.1⟩⟩ := fun e => hyn (e ▸ hmem)
      exact ht hy (hsub hmem) hne ((hA _ _).2 ⟨hne, Or.inl rfl⟩)
    · have hind : Gd.IsIndepSet ((insert y.1 J : Finset V) : Set V) := by
        intro i hi j hj hij hadj
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
        have hny : ∀ j ∈ J, ¬ Gd.Adj y.1 j := by
          intro j hj h
          have hmem : (⟨j, ⟨0, ha j⟩⟩ : Σ i, Fin (a i)) ∈ L J := Finset.mem_image.2 ⟨j, hj, rfl⟩
          have hne : y ≠ ⟨j, ⟨0, ha j⟩⟩ := fun e => hyn (e ▸ hmem)
          exact ht hy (hsub hmem) hne ((hA _ _).2 ⟨hne, Or.inr h⟩)
        rcases hi with rfl | hi <;> rcases hj with rfl | hj
        · exact hij rfl
        · exact hny j hj hadj
        · exact hny i hi hadj.symm
        · exact hJ.1 hi hj hij hadj
      exact hyJ (hJ.2 hind (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  constructor
  · intro hG I I' hI hI'
    obtain ⟨h1, c1⟩ := max_proj I hI
    obtain ⟨h2, c2⟩ := max_proj I' hI'
    rw [← c1, ← c2]; exact hG _ _ h1 h2
  · intro hH J J' hJ hJ'
    rw [← L_card J, ← L_card J']
    exact hH _ _ (max_lift J hJ) (max_lift J' hJ')
