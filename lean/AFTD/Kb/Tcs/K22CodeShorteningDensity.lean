import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode

/-!
# k22_code_shortening_density

Topic: combinatorics   Node: d4f0cce56fb8

Provenance: helper lemma. step towards k22_code_exists_dense_family

For natural numbers 4 ≤ n ≤ N, any K_{2,2}-code on Fin N can be restricted to Fin n with density at least that of the original code.
-/

private lemma k22_code_shortening_density_symmDiff_adj {V : Type*} (G G' : SimpleGraph V) (u v : V) :
    (symmDiff G G').Adj u v ↔ (G.Adj u v ∧ ¬ G'.Adj u v) ∨ (G'.Adj u v ∧ ¬ G.Adj u v) := by
  rw [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, SimpleGraph.sdiff_adj]

private lemma k22_code_shortening_density_comap_symmDiff {M : ℕ} (G G' : SimpleGraph (Fin (M+1))) :
    (symmDiff G G').comap Fin.castSucc
      = symmDiff (G.comap Fin.castSucc) (G'.comap Fin.castSucc) := by
  ext a b
  simp only [SimpleGraph.comap_adj, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]

private lemma k22_code_shortening_density_comap_between {M : ℕ} (s t : Set (Fin M)) :
    (SimpleGraph.between (Fin.castSucc '' s) (Fin.castSucc '' t) ⊤).comap Fin.castSucc
      = SimpleGraph.between s t ⊤ := by
  ext a b
  simp only [SimpleGraph.comap_adj, SimpleGraph.between_adj, SimpleGraph.top_adj,
    Set.mem_image, Fin.castSucc_inj]
  constructor
  · rintro ⟨hne, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩ | ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩⟩
    · exact ⟨fun h => hne (by rw [h]), Or.inl ⟨hx, hy⟩⟩
    · exact ⟨fun h => hne (by rw [h]), Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨hne, h | h⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨fun h' => hne (Fin.castSucc_inj.mp h'), Or.inl ⟨⟨a, h1, rfl⟩, ⟨b, h2, rfl⟩⟩⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨fun h' => hne (Fin.castSucc_inj.mp h'), Or.inr ⟨⟨a, h1, rfl⟩, ⟨b, h2, rfl⟩⟩⟩

private lemma k22_code_shortening_density_eq_of_res_eq {M : ℕ} (G G' : SimpleGraph (Fin (M+1)))
    (hres : G.comap Fin.castSucc = G'.comap Fin.castSucc)
    (hlast : ∀ i : Fin M, G.Adj (Fin.castSucc i) (Fin.last M) ↔ G'.Adj (Fin.castSucc i) (Fin.last M)) :
    G = G' := by
  ext u v
  rcases Fin.eq_castSucc_or_eq_last u with ⟨a, rfl⟩ | rfl <;>
  rcases Fin.eq_castSucc_or_eq_last v with ⟨b, rfl⟩ | rfl
  · rw [← SimpleGraph.comap_adj, ← SimpleGraph.comap_adj, hres]
  · exact hlast a
  · simpa only [SimpleGraph.adj_comm] using hlast b
  · exact ⟨fun h => absurd h (G.loopless.irrefl _), fun h => absurd h (G'.loopless.irrefl _)⟩

private lemma k22_code_shortening_density_last_notin {M : ℕ} (A : Finset (Fin M)) :
    (Fin.last M) ∉ (Fin.castSucc '' (↑A : Set (Fin M))) := by
  rintro ⟨x, _, hx⟩
  exact absurd hx (Fin.castSucc_lt_last x).ne

private lemma k22_code_shortening_density_transfer {M : ℕ} (G G' : SimpleGraph (Fin (M+1)))
    (hnbh : ∀ i : Fin M, G.Adj (Fin.castSucc i) (Fin.last M) ↔ G'.Adj (Fin.castSucc i) (Fin.last M))
    (A B : Finset (Fin M))
    (hAB : symmDiff (G.comap Fin.castSucc) (G'.comap Fin.castSucc)
      = SimpleGraph.between (↑A : Set (Fin M)) (↑B : Set (Fin M)) ⊤) :
    symmDiff G G' = SimpleGraph.between (Fin.castSucc '' (↑A : Set (Fin M)))
      (Fin.castSucc '' (↑B : Set (Fin M))) ⊤ := by
  have hres_eq : (symmDiff G G').comap Fin.castSucc
      = (SimpleGraph.between (Fin.castSucc '' (↑A : Set (Fin M)))
          (Fin.castSucc '' (↑B : Set (Fin M))) ⊤).comap Fin.castSucc := by
    rw [k22_code_shortening_density_comap_symmDiff,
      k22_code_shortening_density_comap_between]
    exact hAB
  have hiso1 : ∀ i : Fin M, ¬ (symmDiff G G').Adj (Fin.castSucc i) (Fin.last M) := by
    intro i
    rw [k22_code_shortening_density_symmDiff_adj]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h2 ((hnbh i).mp h1)
    · exact h2 ((hnbh i).mpr h1)
  have hiso2 : ∀ i : Fin M,
      ¬ (SimpleGraph.between (Fin.castSucc '' (↑A : Set (Fin M)))
          (Fin.castSucc '' (↑B : Set (Fin M))) ⊤).Adj (Fin.castSucc i) (Fin.last M) := by
    intro i h
    rw [SimpleGraph.between_adj] at h
    rcases h with ⟨_, h | h⟩
    · exact k22_code_shortening_density_last_notin B h.2
    · exact k22_code_shortening_density_last_notin A h.2
  exact k22_code_shortening_density_eq_of_res_eq _ _ hres_eq
    (fun i => ⟨fun h => absurd h (hiso1 i), fun h => absurd h (hiso2 i)⟩)

private lemma k22_code_shortening_density_max_fiber {α β : Type*} [Fintype β] [DecidableEq β]
    [Nonempty β] (f : α → β) (T : Finset α) :
    ∃ s : β, T.card ≤ (T.filter (fun a => f a = s)).card * Fintype.card β := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨Classical.arbitrary β, by simp [hT]⟩
  · have hRan : (T.image f).Nonempty := hT.image f
    obtain ⟨s0, hs0mem, hs0eq⟩ :=
      Finset.exists_mem_eq_sup' hRan (fun s => (T.filter (fun a => f a = s)).card)
    have hsum : T.card = ∑ s ∈ T.image f, (T.filter (fun a => f a = s)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T.image f)]
      intro a ha
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hle1 : ∑ s ∈ T.image f, (T.filter (fun a => f a = s)).card
        ≤ (T.image f).card * (T.filter (fun a => f a = s0)).card := by
      have hb : ∀ s ∈ T.image f,
          (T.filter (fun a => f a = s)).card ≤ (T.filter (fun a => f a = s0)).card := by
        intro s hs
        rw [← hs0eq]
        exact Finset.le_sup' (fun s => (T.filter (fun a => f a = s)).card) hs
      calc ∑ s ∈ T.image f, (T.filter (fun a => f a = s)).card
          ≤ ∑ s ∈ T.image f, (T.filter (fun a => f a = s0)).card := Finset.sum_le_sum hb
        _ = (T.image f).card * (T.filter (fun a => f a = s0)).card := by
            rw [Finset.sum_const, smul_eq_mul]
    refine ⟨s0, ?_⟩
    calc T.card = ∑ s ∈ T.image f, (T.filter (fun a => f a = s)).card := hsum
      _ ≤ (T.image f).card * (T.filter (fun a => f a = s0)).card := hle1
      _ ≤ Fintype.card β * (T.filter (fun a => f a = s0)).card :=
          Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ = (T.filter (fun a => f a = s0)).card * Fintype.card β := Nat.mul_comm _ _

private lemma k22_code_shortening_density_step (m : ℕ) (C : Set (SimpleGraph (Fin (m+1))))
    (hC : is_kst_code 2 2 (m+1) C) :
    ∃ D : Set (SimpleGraph (Fin m)), is_kst_code 2 2 m D ∧
      (C.ncard : ℝ) / 2 ^ ((m+1).choose 2) ≤ (D.ncard : ℝ) / 2 ^ (m.choose 2) := by
  classical
  set f : SimpleGraph (Fin (m+1)) → Set (Fin m) :=
    fun G => {i | G.Adj (Fin.castSucc i) (Fin.last m)} with hf
  set T : Finset (SimpleGraph (Fin (m+1))) := Finset.univ.filter (fun G => G ∈ C) with hT
  obtain ⟨s0, hs0⟩ := k22_code_shortening_density_max_fiber f T
  rw [Fintype.card_set, Fintype.card_fin] at hs0
  set S : Set (SimpleGraph (Fin (m+1))) := C ∩ {G | f G = s0} with hS
  have hTC : (↑T : Set (SimpleGraph (Fin (m+1)))) = C := by
    ext G; simp [hT]
  have hSC : S = ↑(T.filter (fun a => f a = s0)) := by
    ext G; simp [hS, hT, Set.mem_inter_iff]
  have hlast_eq : ∀ G1 ∈ S, ∀ G2 ∈ S, ∀ i : Fin m,
      G1.Adj (Fin.castSucc i) (Fin.last m) ↔ G2.Adj (Fin.castSucc i) (Fin.last m) := by
    intro G1 hG1 G2 hG2 i
    have h1 : f G1 = s0 := hG1.2
    have h2 : f G2 = s0 := hG2.2
    have h3 := congrArg (fun s : Set (Fin m) => i ∈ s) (h1.trans h2.symm)
    simpa [hf] using h3
  have hinj : Set.InjOn (fun G : SimpleGraph (Fin (m+1)) => G.comap Fin.castSucc) S := by
    intro G1 hG1 G2 hG2 heq
    exact k22_code_shortening_density_eq_of_res_eq G1 G2 heq (hlast_eq G1 hG1 G2 hG2)
  refine ⟨(fun G => G.comap Fin.castSucc) '' S, ?_, ?_⟩
  · rintro G1 G2 ⟨H1, hH1, rfl⟩ ⟨H2, hH2, rfl⟩ hGne A B hdisj hA hB hdiff
    have hHne : H1 ≠ H2 := by rintro rfl; exact hGne rfl
    have hstep : symmDiff H1 H2
        = SimpleGraph.between (↑(A.image Fin.castSucc) : Set (Fin (m+1)))
            (↑(B.image Fin.castSucc) : Set (Fin (m+1))) ⊤ := by
      simp only [Finset.coe_image]
      exact k22_code_shortening_density_transfer H1 H2
        (hlast_eq H1 hH1 H2 hH2) A B hdiff
    have hdisj' : Disjoint (A.image Fin.castSucc) (B.image Fin.castSucc) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_image] at hx hx'
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, hb2⟩ := hx'
      exact Finset.disjoint_left.mp hdisj ha (Fin.castSucc_inj.mp hb2 ▸ hb)
    have hA' : (A.image Fin.castSucc).card = 2 := by
      rw [Finset.card_image_of_injective _ (Fin.castSucc_injective m), hA]
    have hB' : (B.image Fin.castSucc).card = 2 := by
      rw [Finset.card_image_of_injective _ (Fin.castSucc_injective m), hB]
    exact hC hH1.1 hH2.1 hHne _ _ hdisj' hA' hB' hstep
  · have hCcard : (C.ncard : ℝ) = (T.card : ℝ) := by
      rw [← hTC, Set.ncard_coe_finset]
    have hScard : (S.ncard : ℝ) = ((T.filter (fun a => f a = s0)).card : ℝ) := by
      rw [hSC, Set.ncard_coe_finset]
    have hDcard : ((fun G : SimpleGraph (Fin (m+1)) => G.comap Fin.castSucc) '' S).ncard
        = S.ncard :=
      Set.InjOn.ncard_image hinj
    have hs0R : (T.card : ℝ) ≤ ((T.filter (fun a => f a = s0)).card : ℝ) * 2 ^ m := by
      exact_mod_cast hs0
    have hkey : (C.ncard : ℝ) ≤ (S.ncard : ℝ) * 2 ^ m := by
      rw [hCcard, hScard]
      exact hs0R
    rw [show (((fun G : SimpleGraph (Fin (m+1)) => G.comap Fin.castSucc) '' S).ncard : ℝ)
        = (S.ncard : ℝ) by rw [hDcard]]
    have hp2 : (0:ℝ) < 2 ^ (m.choose 2) := by positivity
    have h1 : (C.ncard : ℝ) / 2 ^ m ≤ (S.ncard : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ m)]
      linarith
    have h2 : (C.ncard : ℝ) / 2 ^ m / 2 ^ m.choose 2 ≤ (S.ncard : ℝ) / 2 ^ m.choose 2 :=
      div_le_div_of_nonneg_right h1 hp2.le
    have hchoose : (m+1).choose 2 = m.choose 2 + m := by
      have h := Nat.choose_succ_succ m 1
      simp [Nat.choose_one_right] at h
      omega
    calc (C.ncard : ℝ) / 2 ^ ((m+1).choose 2)
        = (C.ncard : ℝ) / 2 ^ m / 2 ^ m.choose 2 := by
          rw [hchoose, pow_add]; ring
      _ ≤ (S.ncard : ℝ) / 2 ^ m.choose 2 := h2

/-- Shortening preserves code density: any K_{2,2}-code on Fin N can be restricted to Fin n without decreasing density. -/
theorem k22_code_shortening_density (n N : ℕ) (hn : 4 ≤ n) (hle : n ≤ N)
    (C : Set (SimpleGraph (Fin N))) (hC : is_kst_code 2 2 N C) :
    ∃ D : Set (SimpleGraph (Fin n)),
      is_kst_code 2 2 n D ∧
      (C.ncard : ℝ) / (2 ^ (N.choose 2) : ℝ) ≤ (D.ncard : ℝ) / (2 ^ (n.choose 2) : ℝ) := by
  classical
  revert C
  refine Nat.le_induction (m := n) ?_ ?_ N hle
  · intro C hC
    exact ⟨C, hC, le_refl _⟩
  · intro k hk ih C hC
    obtain ⟨D', hD', hle'⟩ := k22_code_shortening_density_step k C hC
    obtain ⟨D, hD, hle2⟩ := ih D' hD'
    exact ⟨D, hD, hle'.trans hle2⟩
