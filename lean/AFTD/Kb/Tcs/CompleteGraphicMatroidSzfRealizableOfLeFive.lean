import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphicMatroidSzfRealizable
import AFTD.Kb.Tcs.SzfMultiForced
import AFTD.Kb.Tcs.CompleteGraphCycleClosure
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# complete_graphic_matroid_szf_realizable_of_le_five

Topic: graphs   Node: ab0b1092c0a8

Provenance: formalization of a published result. Source: arXiv:2611.15741 Proposition 4.4 (the paper's K_4, K_5 graphs are only in a figure; the witnesses here were found by search, experiment 27629)

For 1 ≤ n ≤ 5 the cycle matroid M(K_n) is SZF-realizable by some multigraph on E(K_n).
-/

theorem kn_szf_cl_sub {n : ℕ} (S : Set (⊤ : SimpleGraph (Fin n)).edgeSet) :
    S ⊆ complete_graph_cycle_closure n S := by
  rintro ⟨e, he⟩ hS
  induction e using Sym2.ind with
  | h a b =>
    refine ⟨a, b, rfl, SimpleGraph.Adj.reachable ?_⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨_, hS, rfl⟩, by simpa using he⟩

theorem kn_szf_cl_tri {n : ℕ} (S : Set (⊤ : SimpleGraph (Fin n)).edgeSet)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : (⟨s(a, b), by simpa using hab⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈
      complete_graph_cycle_closure n S)
    (h2 : (⟨s(b, c), by simpa using hbc⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈
      complete_graph_cycle_closure n S) :
    (⟨s(a, c), by simpa using hac⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈
      complete_graph_cycle_closure n S := by
  obtain ⟨x, y, hxy, r1⟩ := h1
  obtain ⟨z, w, hzw, r2⟩ := h2
  have r1' : (SimpleGraph.fromEdgeSet (Subtype.val '' S)).Reachable a b := by
    rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact r1
    · exact r1.symm
  have r2' : (SimpleGraph.fromEdgeSet (Subtype.val '' S)).Reachable b c := by
    rcases Sym2.eq_iff.1 hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact r2
    · exact r2.symm
  exact ⟨a, c, rfl, r1'.trans r2'⟩

theorem kn_szf_cl_least {n : ℕ} (S T : Set (⊤ : SimpleGraph (Fin n)).edgeSet) (hST : S ⊆ T)
    (hT : ∀ (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c),
      (⟨s(a, b), by simpa using hab⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ T →
      (⟨s(b, c), by simpa using hbc⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ T →
      (⟨s(a, c), by simpa using hac⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ T) :
    complete_graph_cycle_closure n S ⊆ T := by
  rintro ⟨e, he⟩ ⟨a, b, hab, hr⟩
  simp only at hab
  subst hab
  have key : ∀ c, (SimpleGraph.fromEdgeSet (Subtype.val '' S)).Reachable a c →
      ∀ h : a ≠ c, (⟨s(a, c), by simpa using h⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ T := by
    intro c hc
    rw [SimpleGraph.reachable_iff_reflTransGen] at hc
    induction hc with
    | refl => intro h; exact absurd rfl h
    | @tail c d _ hcd ih =>
      intro had
      rw [SimpleGraph.fromEdgeSet_adj] at hcd
      obtain ⟨⟨x, hx, hxv⟩, hcd'⟩ := hcd
      have hdS : (⟨s(c, d), by simpa using hcd'⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ T := by
        have : x = ⟨s(c, d), by simpa using hcd'⟩ := Subtype.ext hxv
        subst this
        exact hST hx
      by_cases hac : a = c
      · subst hac
        exact hdS
      · exact hT a c d hac hcd' had (ih hac) hdS
  exact key b hr (by simpa using he)

theorem kn_szf_least {V : Type*} (μ : V → V → ℕ) (S T : Set V) (hST : S ⊆ T)
    (hT : ∀ u w, μ u w = 1 → (∀ x, x ≠ w → μ u x ≠ 0 → x ∈ T) → w ∈ T) :
    szf_multigraph_closure μ S ⊆ T := by
  intro v hv
  induction hv with
  | init v hv => exact hST hv
  | step u w h1 _ ih => exact hT u w h1 ih

theorem kn_szf_eq_of {n : ℕ} (μ : (⊤ : SimpleGraph (Fin n)).edgeSet →
      (⊤ : SimpleGraph (Fin n)).edgeSet → ℕ)
    (H1 : ∀ u w, μ u w = 1 → w ∈ complete_graph_cycle_closure n {x | x ≠ w ∧ μ u x ≠ 0})
    (H2 : ∀ (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c),
      (⟨s(a, c), by simpa using hac⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈
        szf_multigraph_closure μ
          {⟨s(a, b), by simpa using hab⟩, ⟨s(b, c), by simpa using hbc⟩})
    (S : Set (⊤ : SimpleGraph (Fin n)).edgeSet) :
    szf_multigraph_closure μ S = complete_graph_cycle_closure n S := by
  apply Set.Subset.antisymm
  · apply kn_szf_least μ S _ (kn_szf_cl_sub S)
    intro u w h1 hw
    exact kn_szf_cl_least _ _ (fun x hx => hw x hx.1 hx.2)
      (fun a b c hab hbc hac => kn_szf_cl_tri S a b c hab hbc hac) (H1 u w h1)
  · apply kn_szf_cl_least S _ (fun v hv => SzfMultiForced.init v hv)
    intro a b c hab hbc hac h1 h2
    exact kn_szf_least μ _ (szf_multigraph_closure μ S) (by
        rintro x (rfl | rfl)
        · exact h1
        · exact h2)
      (fun u w h hx => SzfMultiForced.step u w h hx) (H2 a b c hab hbc hac)

theorem kn_szf_adj {n : ℕ} (μ : (⊤ : SimpleGraph (Fin n)).edgeSet →
      (⊤ : SimpleGraph (Fin n)).edgeSet → ℕ) (u w : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (a b : Fin n) (hab : a ≠ b)
    (hne : (⟨s(a, b), by simpa using hab⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ≠ w)
    (hμ : μ u ⟨s(a, b), by simpa using hab⟩ ≠ 0) :
    (SimpleGraph.fromEdgeSet (Subtype.val '' {x | x ≠ w ∧ μ u x ≠ 0})).Adj a b := by
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨_, ⟨hne, hμ⟩, rfl⟩, hab⟩

theorem kn_szf_realizable_of_table {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℕ)
    (hF : ∀ a₁ a₂ b₁ b₂, F a₁ a₂ b₁ b₂ = F a₂ a₁ b₁ b₂ ∧ F a₁ a₂ b₁ b₂ = F a₁ a₂ b₂ b₁)
    (hsymm : ∀ i j k l, F i j k l = F k l i j)
    (H1c : ∀ i j k l : Fin n, i ≠ j → k ≠ l → F i j k l = 1 →
      (∃ p, p ≠ k ∧ p ≠ l ∧ F i j k p ≠ 0 ∧ F i j p l ≠ 0) ∨
      (∃ p q, p ≠ k ∧ p ≠ l ∧ q ≠ k ∧ q ≠ l ∧ p ≠ q ∧
        F i j k p ≠ 0 ∧ F i j p q ≠ 0 ∧ F i j q l ≠ 0))
    (H2c : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c → ∃ i j, i ≠ j ∧ F i j a c = 1 ∧
      ∀ k l, k ≠ l → F i j k l ≠ 0 →
        (k = a ∧ l = c ∨ k = c ∧ l = a) ∨ (k = a ∧ l = b ∨ k = b ∧ l = a) ∨
          (k = b ∧ l = c ∨ k = c ∧ l = b)) :
    complete_graphic_matroid_szf_realizable n := by
  refine ⟨fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1, ?_, kn_szf_eq_of _ ?_ ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    induction u using Sym2.ind with
    | h i j =>
      induction v using Sym2.ind with
      | h k l => simpa using hsymm i j k l
  · rintro ⟨u, hu⟩ ⟨w, hw⟩ h
    induction u using Sym2.ind with
    | h i j =>
      induction w using Sym2.ind with
      | h k l =>
        have hij : i ≠ j := by simpa using hu
        have hkl : k ≠ l := by simpa using hw
        simp only [Sym2.lift₂_mk] at h
        refine ⟨k, l, rfl, ?_⟩
        have hne : ∀ (a b : Fin n) (hab : a ≠ b), (a ≠ k ∨ b ≠ l) → (a ≠ l ∨ b ≠ k) →
            (⟨s(a, b), by simpa using hab⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ≠
              ⟨s(k, l), hw⟩ := by
          intro a b hab h1 h2 heq
          have := Sym2.eq_iff.1 (congrArg Subtype.val heq)
          tauto
        rcases H1c i j k l hij hkl h with ⟨p, hpk, hpl, h1, h2⟩ |
            ⟨p, q, hpk, hpl, hqk, hql, hpq, h1, h2, h3⟩
        · refine (kn_szf_adj (fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1) ⟨s(i, j), hu⟩ _ k p (Ne.symm hpk) (hne k p (Ne.symm hpk) (Or.inr hpl) (Or.inl hkl)) ?_).reachable.trans
            (kn_szf_adj (fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1) ⟨s(i, j), hu⟩ _ p l hpl (hne p l hpl (Or.inl hpk) (Or.inl hpl)) ?_).reachable
          · simpa using h1
          · simpa using h2
        · refine ((kn_szf_adj (fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1) ⟨s(i, j), hu⟩ _ k p (Ne.symm hpk) (hne k p (Ne.symm hpk) (Or.inr hpl) (Or.inl hkl)) ?_).reachable.trans
            (kn_szf_adj (fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1) ⟨s(i, j), hu⟩ _ p q hpq (hne p q hpq (Or.inl hpk) (Or.inl hpl)) ?_).reachable).trans
            (kn_szf_adj (fun u v => Sym2.lift₂ ⟨F, hF⟩ u.1 v.1) ⟨s(i, j), hu⟩ _ q l hql (hne q l hql (Or.inl hqk) (Or.inl hql)) ?_).reachable
          · simpa using h1
          · simpa using h2
          · simpa using h3
  · intro a b c hab hbc hac
    obtain ⟨i, j, hij, h1, h2⟩ := H2c a b c hab hbc hac
    refine SzfMultiForced.step ⟨s(i, j), by simpa using hij⟩ _ (by simpa using h1) ?_
    rintro ⟨x, hx⟩ hxne hx0
    induction x using Sym2.ind with
    | h k l =>
      have hkl : k ≠ l := by simpa using hx
      simp only [Sym2.lift₂_mk] at hx0
      apply SzfMultiForced.init
      rcases h2 k l hkl hx0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact absurd rfl hxne
      · exact absurd (Subtype.ext Sym2.eq_swap) hxne
      · exact Or.inl rfl
      · exact Or.inl (Subtype.ext Sym2.eq_swap)
      · exact Or.inr rfl
      · exact Or.inr (Subtype.ext Sym2.eq_swap)

/-- Edge code of `s(a, b)`. -/
def kn_szf_code {n : ℕ} (a b : Fin n) : ℕ := 2 ^ a.val + 2 ^ b.val

def kn_szf_row5 : ℕ → List ℕ
  | 3 => [3, 5, 6]
  | 5 => [3, 9, 10]
  | 9 => [5, 9, 12]
  | 17 => [6, 10, 12]
  | 6 => [3, 17, 18]
  | 10 => [5, 17, 20]
  | 18 => [6, 18, 20]
  | 12 => [9, 17, 24]
  | 20 => [10, 18, 24]
  | 24 => [12, 20, 24]
  | _ => []

def kn_szf_row4 : ℕ → List ℕ
  | 3 => [3, 5, 6]
  | 5 => [3, 9, 10]
  | 9 => [5, 9, 6, 10]
  | 6 => [3, 9, 6, 12]
  | 10 => [5, 9, 12]
  | 12 => [6, 10, 12]
  | _ => []

def kn_szf_row3 : ℕ → List ℕ
  | 3 => [3, 5, 6]
  | 5 => [3, 5, 6]
  | 6 => [3, 5, 6]
  | _ => []

def kn_szf_table {n : ℕ} (row : ℕ → List ℕ) (i j k l : Fin n) : ℕ :=
  if kn_szf_code k l ∈ row (kn_szf_code i j) then 1 else 0

theorem kn_szf_table_symm {n : ℕ} (row : ℕ → List ℕ) (a₁ a₂ b₁ b₂ : Fin n) :
    kn_szf_table row a₁ a₂ b₁ b₂ = kn_szf_table row a₂ a₁ b₁ b₂ ∧
      kn_szf_table row a₁ a₂ b₁ b₂ = kn_szf_table row a₁ a₂ b₂ b₁ := by
  unfold kn_szf_table kn_szf_code
  exact ⟨by rw [Nat.add_comm (2 ^ (a₂ : ℕ))], by rw [Nat.add_comm (2 ^ (b₂ : ℕ))]⟩

theorem complete_graphic_matroid_szf_realizable_of_le_five (n : ℕ) (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    complete_graphic_matroid_szf_realizable n := by
  interval_cases n
  · exact kn_szf_realizable_of_table (kn_szf_table fun _ => []) (kn_szf_table_symm _)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact kn_szf_realizable_of_table (kn_szf_table fun _ => []) (kn_szf_table_symm _)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact kn_szf_realizable_of_table (kn_szf_table kn_szf_row3) (kn_szf_table_symm _)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact kn_szf_realizable_of_table (kn_szf_table kn_szf_row4) (kn_szf_table_symm _)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact kn_szf_realizable_of_table (kn_szf_table kn_szf_row5) (kn_szf_table_symm _)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
