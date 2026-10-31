import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.IsKstCode
import AFTD.Kb.Tcs.CardSimpleGraph

/-!
# kst_code_max_density_antitone

Topic: combinatorics   Node: 2139a81e7727

Provenance: helper lemma. step towards four_cycle_graph_code_asymptotic_density_eventually_ge

For all natural numbers s, t, n with 1 ≤ s and 1 ≤ t, the maximum density of a K_{s,t}-code is non-increasing in n: kst_code_max_density s t (n + 1) ≤ kst_code_max_density s t n.
-/

open Classical

noncomputable def kst_code_max_density_antitone_nhbd (n : ℕ) (G : SimpleGraph (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.Adj (Fin.castSucc v) (Fin.last n))

noncomputable def kst_code_max_density_antitone_restr (n : ℕ) (G : SimpleGraph (Fin (n+1))) : SimpleGraph (Fin n) :=
  G.comap (Fin.castSucc : Fin n → Fin (n+1))

private lemma kst_code_max_density_antitone_adj_symmDiff (n : ℕ) (G1 G2 : SimpleGraph (Fin (n+1)))
    (hN : kst_code_max_density_antitone_nhbd n G1 = kst_code_max_density_antitone_nhbd n G2) (u v : Fin (n+1)) :
    (symmDiff G1 G2).Adj u v ↔
      ∃ a b : Fin n, u = Fin.castSucc a ∧ v = Fin.castSucc b ∧
        (symmDiff (kst_code_max_density_antitone_restr n G1) (kst_code_max_density_antitone_restr n G2)).Adj a b := by
  have hNadj : ∀ a : Fin n, G1.Adj (Fin.castSucc a) (Fin.last n) ↔ G2.Adj (Fin.castSucc a) (Fin.last n) := by
    intro a
    have h1 : a ∈ kst_code_max_density_antitone_nhbd n G1 ↔ G1.Adj (Fin.castSucc a) (Fin.last n) := by simp [kst_code_max_density_antitone_nhbd]
    have h2 : a ∈ kst_code_max_density_antitone_nhbd n G2 ↔ G2.Adj (Fin.castSucc a) (Fin.last n) := by simp [kst_code_max_density_antitone_nhbd]
    rw [← h1, hN, h2]
  have hNadj' : ∀ a : Fin n, G1.Adj (Fin.last n) (Fin.castSucc a) ↔ G2.Adj (Fin.last n) (Fin.castSucc a) := by
    intro a
    exact (SimpleGraph.adj_comm G1 _ _).trans ((hNadj a).trans (SimpleGraph.adj_comm G2 _ _).symm)
  simp only [symmDiff, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, SimpleGraph.comap_adj, kst_code_max_density_antitone_restr]
  rcases Fin.eq_castSucc_or_eq_last u with ⟨a, rfl⟩ | rfl <;>
  rcases Fin.eq_castSucc_or_eq_last v with ⟨b, rfl⟩ | rfl
  · constructor
    · intro h; exact ⟨a, b, rfl, rfl, h⟩
    · rintro ⟨a', b', h1, h2, h3⟩
      rw [Fin.castSucc_inj] at h1 h2
      subst h1; subst h2; exact h3
  · constructor
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; exact h2 ((hNadj a).mp h1)
      · exfalso; exact h2 ((hNadj a).mpr h1)
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last b' h2.symm).elim
  · constructor
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; exact h2 ((hNadj' b).mp h1)
      · exfalso; exact h2 ((hNadj' b).mpr h1)
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last a' h1.symm).elim
  · constructor
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 (SimpleGraph.irrefl G1)
      · exact absurd h1 (SimpleGraph.irrefl G2)
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last a' h1.symm).elim

private lemma kst_code_max_density_antitone_between_lift (n : ℕ) (A B : Finset (Fin n)) (u v : Fin (n+1)) :
    (SimpleGraph.between ((A.image Fin.castSucc : Finset (Fin (n+1))) : Set _)
       ((B.image Fin.castSucc : Finset (Fin (n+1))) : Set _) ⊤).Adj u v ↔
      ∃ a b : Fin n, u = Fin.castSucc a ∧ v = Fin.castSucc b ∧
        (SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) ⊤).Adj a b := by
  have hmemA : ∀ a, (Fin.castSucc a ∈ ((A.image Fin.castSucc : Finset (Fin (n+1))) : Set _)) ↔ a ∈ A := by
    intro a; simp [Fin.castSucc_inj]
  have hmemB : ∀ a, (Fin.castSucc a ∈ ((B.image Fin.castSucc : Finset (Fin (n+1))) : Set _)) ↔ a ∈ B := by
    intro a; simp [Fin.castSucc_inj]
  have hlastA : Fin.last n ∉ ((A.image Fin.castSucc : Finset (Fin (n+1))) : Set _) := by
    simp [Fin.castSucc_ne_last]
  have hlastB : Fin.last n ∉ ((B.image Fin.castSucc : Finset (Fin (n+1))) : Set _) := by
    simp [Fin.castSucc_ne_last]
  simp only [SimpleGraph.between_adj, SimpleGraph.top_adj]
  rcases Fin.eq_castSucc_or_eq_last u with ⟨a, rfl⟩ | rfl <;>
  rcases Fin.eq_castSucc_or_eq_last v with ⟨b, rfl⟩ | rfl
  · rw [hmemA a, hmemB b, hmemA b, hmemB a]
    constructor
    · intro h
      exact ⟨a, b, rfl, rfl, fun hab => h.1 (by rw [hab]), h.2⟩
    · rintro ⟨a', b', h1, h2, h3⟩
      have ha : a = a' := Fin.castSucc_injective n h1
      have hb : b = b' := Fin.castSucc_injective n h2
      cases ha; cases hb
      exact ⟨fun h => h3.1 (Fin.castSucc_injective n h), h3.2⟩
  · constructor
    · intro h
      rcases h.2 with ⟨_, hb⟩ | ⟨_, ha⟩
      · exact (hlastB hb).elim
      · exact (hlastA ha).elim
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last b' h2.symm).elim
  · constructor
    · intro h
      rcases h.2 with ⟨ha, _⟩ | ⟨hb, _⟩
      · exact (hlastA ha).elim
      · exact (hlastB hb).elim
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last a' h1.symm).elim
  · constructor
    · intro h; exact (h.1 rfl).elim
    · rintro ⟨a', b', h1, h2, h3⟩
      exact (Fin.castSucc_ne_last a' h1.symm).elim

private lemma kst_code_max_density_antitone_symmDiff_eq_between (n : ℕ) (G1 G2 : SimpleGraph (Fin (n+1)))
    (hN : kst_code_max_density_antitone_nhbd n G1 = kst_code_max_density_antitone_nhbd n G2) (A B : Finset (Fin n))
    (heq : symmDiff (kst_code_max_density_antitone_restr n G1) (kst_code_max_density_antitone_restr n G2) =
      SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) ⊤) :
    symmDiff G1 G2 =
      SimpleGraph.between ((A.image Fin.castSucc : Finset (Fin (n+1))) : Set _)
        ((B.image Fin.castSucc : Finset (Fin (n+1))) : Set _) ⊤ := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [kst_code_max_density_antitone_adj_symmDiff n G1 G2 hN u v, kst_code_max_density_antitone_between_lift n A B u v]
  simp only [heq]

private lemma kst_code_max_density_antitone_restr_injOn (n : ℕ) (N : Finset (Fin n)) :
    Set.InjOn (kst_code_max_density_antitone_restr n)
      {G : SimpleGraph (Fin (n+1)) | kst_code_max_density_antitone_nhbd n G = N} := by
  intro G1 h1 G2 h2 hrestr
  have hN : kst_code_max_density_antitone_nhbd n G1 = kst_code_max_density_antitone_nhbd n G2 := h1.trans h2.symm
  have hbot : symmDiff (kst_code_max_density_antitone_restr n G1) (kst_code_max_density_antitone_restr n G2) = ⊥ := by
    rw [hrestr, symmDiff_self]
  have hzero : symmDiff G1 G2 = ⊥ := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    rw [kst_code_max_density_antitone_adj_symmDiff n G1 G2 hN u v, hbot]
    simp
  exact symmDiff_eq_bot.mp hzero

private lemma kst_code_max_density_antitone_code_transfer (s t n : ℕ) (C : Set (SimpleGraph (Fin (n+1))))
    (hC : is_kst_code s t (n+1) C) (G1 G2 : SimpleGraph (Fin (n+1)))
    (hG1 : G1 ∈ C) (hG2 : G2 ∈ C) (hN : kst_code_max_density_antitone_nhbd n G1 = kst_code_max_density_antitone_nhbd n G2)
    (hne : kst_code_max_density_antitone_restr n G1 ≠ kst_code_max_density_antitone_restr n G2)
    (A B : Finset (Fin n)) (hdisj : Disjoint A B) (hA : A.card = s) (hB : B.card = t) :
    symmDiff (kst_code_max_density_antitone_restr n G1) (kst_code_max_density_antitone_restr n G2) ≠
      SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) ⊤ := by
  intro heq
  have hgraph := kst_code_max_density_antitone_symmDiff_eq_between n G1 G2 hN A B heq
  have hGne : G1 ≠ G2 := by
    intro h; exact hne (by rw [h])
  have hdisj' : Disjoint (A.image Fin.castSucc) (B.image Fin.castSucc) :=
    (Finset.disjoint_image (Fin.castSucc_injective n)).mpr hdisj
  have hA' : (A.image Fin.castSucc).card = s := by
    rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n), hA]
  have hB' : (B.image Fin.castSucc).card = t := by
    rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n), hB]
  exact hC hG1 hG2 hGne (A.image Fin.castSucc) (B.image Fin.castSucc) hdisj' hA' hB' hgraph

private lemma kst_code_max_density_antitone_exists_smaller_code (s t n : ℕ) (C : Set (SimpleGraph (Fin (n+1))))
    (hC : is_kst_code s t (n+1) C) :
    ∃ D : Set (SimpleGraph (Fin n)), is_kst_code s t n D ∧
      (C.ncard : ℝ) / 2 ^ n ≤ (D.ncard : ℝ) := by
  classical
  let fib : Finset (Fin n) → Set (SimpleGraph (Fin (n+1))) :=
    fun N => {G | G ∈ C ∧ kst_code_max_density_antitone_nhbd n G = N}
  have hcover : C = ⋃ N, fib N := by
    ext G
    constructor
    · intro hG
      exact Set.mem_iUnion.mpr ⟨kst_code_max_density_antitone_nhbd n G, hG, rfl⟩
    · intro hG
      obtain ⟨N, hGN, -⟩ := Set.mem_iUnion.mp hG
      exact hGN
  have hsum : C.ncard ≤ ∑ N : Finset (Fin n), (fib N).ncard := by
    rw [hcover]
    exact Set.ncard_iUnion_le_of_fintype fib
  obtain ⟨N₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
    (fun N => (fib N).ncard) ⟨∅, Finset.mem_univ ∅⟩
  have hsum_le : ∑ N : Finset (Fin n), (fib N).ncard ≤ 2^n * (fib N₀).ncard := by
    calc ∑ N : Finset (Fin n), (fib N).ncard
        ≤ ∑ _N : Finset (Fin n), (fib N₀).ncard :=
          Finset.sum_le_sum (fun N _ => hmax N (Finset.mem_univ N))
      _ = 2^n * (fib N₀).ncard := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
  have hcard : C.ncard ≤ 2^n * (fib N₀).ncard := hsum.trans hsum_le
  refine ⟨kst_code_max_density_antitone_restr n '' fib N₀, ?_, ?_⟩
  · intro G1 G2 hG1 hG2 hne A B hdisj hA hB
    obtain ⟨H1, hH1, rfl⟩ := hG1
    obtain ⟨H2, hH2, rfl⟩ := hG2
    exact kst_code_max_density_antitone_code_transfer s t n C hC H1 H2 hH1.1 hH2.1
      (hH1.2.trans hH2.2.symm) hne A B hdisj hA hB
  · have hinj : Set.InjOn (kst_code_max_density_antitone_restr n) (fib N₀) :=
      (kst_code_max_density_antitone_restr_injOn n N₀).mono (fun G hG => hG.2)
    rw [Set.InjOn.ncard_image hinj]
    have hcardR : (C.ncard : ℝ) ≤ 2^n * ((fib N₀).ncard : ℝ) := by exact_mod_cast hcard
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2^n)]
    calc (C.ncard : ℝ) ≤ 2^n * ((fib N₀).ncard : ℝ) := hcardR
      _ = ((fib N₀).ncard : ℝ) * 2^n := by ring

private lemma kst_code_max_density_antitone_density_le_one (n : ℕ) (C : Set (SimpleGraph (Fin n))) :
    (C.ncard : ℝ) / 2 ^ n.choose 2 ≤ 1 := by
  have huniv : (Set.univ : Set (SimpleGraph (Fin n))).ncard = 2 ^ n.choose 2 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_simpleGraph, Fintype.card_fin]
  have hle : C.ncard ≤ 2 ^ n.choose 2 := by
    rw [← huniv]
    exact Set.ncard_le_ncard (Set.subset_univ C) (Set.toFinite _)
  rw [div_le_one (by positivity : (0:ℝ) < 2 ^ n.choose 2)]
  exact_mod_cast hle

private lemma kst_code_max_density_antitone_le_max_density (s t n : ℕ) (D : Set (SimpleGraph (Fin n)))
    (hD : is_kst_code s t n D) :
    (D.ncard : ℝ) / 2 ^ n.choose 2 ≤
      ⨆ C, ⨆ (_ : is_kst_code s t n C), (C.ncard : ℝ) / 2 ^ n.choose 2 := by
  have hbdd : BddAbove (Set.range (fun C : Set (SimpleGraph (Fin n)) =>
      ⨆ (_ : is_kst_code s t n C), (C.ncard : ℝ) / 2 ^ n.choose 2)) := by
    refine ⟨1, ?_⟩
    rintro x ⟨C, rfl⟩
    exact Real.iSup_le (fun hC => kst_code_max_density_antitone_density_le_one n C) (by norm_num)
  calc (D.ncard : ℝ) / 2 ^ n.choose 2
      = ⨆ (_ : is_kst_code s t n D), (D.ncard : ℝ) / 2 ^ n.choose 2 := by rw [ciSup_pos hD]
    _ ≤ ⨆ C, ⨆ (_ : is_kst_code s t n C), (C.ncard : ℝ) / 2 ^ n.choose 2 := le_ciSup hbdd D

/-- For all natural numbers s, t, n with 1 ≤ s and 1 ≤ t, the maximum density of a K_{s,t}-code is non-increasing in n: kst_code_max_density s t (n + 1) ≤ kst_code_max_density s t n. -/
theorem kst_code_max_density_antitone (s t n : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    kst_code_max_density s t (n + 1) ≤ kst_code_max_density s t n := by
  classical
  rw [kst_code_max_density]
  refine ciSup_le (fun C => ?_)
  by_cases hC : is_kst_code s t (n+1) C
  · rw [ciSup_pos hC]
    obtain ⟨D, hD, hle⟩ := kst_code_max_density_antitone_exists_smaller_code s t n C hC
    have hchoose : (n+1).choose 2 = n.choose 2 + n := by
      have h := Nat.choose_succ_succ n 1
      simp [Nat.choose_one_right] at h
      omega
    calc (C.ncard : ℝ) / 2 ^ (n + 1).choose 2
        = ((C.ncard : ℝ) / 2 ^ n) / 2 ^ n.choose 2 := by
          rw [hchoose, pow_add]; ring
      _ ≤ (D.ncard : ℝ) / 2 ^ n.choose 2 := by gcongr
      _ ≤ ⨆ D, ⨆ (_ : is_kst_code s t n D), (D.ncard : ℝ) / 2 ^ n.choose 2 :=
          kst_code_max_density_antitone_le_max_density s t n D hD
  · rw [show (⨆ (_ : is_kst_code s t (n+1) C), (C.ncard : ℝ) / 2 ^ (n+1).choose 2) = 0 from by simp [hC]]
    exact Real.iSup_nonneg (fun C => Real.iSup_nonneg (fun h => by positivity))
