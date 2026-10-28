import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode

/-!
# is_kst_code_even_edge_graphs

Topic: combinatorics   Node: b4f5be46d22f

Provenance: helper lemma. arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Proposition 3.2

Let s and t be odd natural numbers, and let n be a natural number. The set of simple graphs on vertex set [n] with an even number of edges is a K_{s,t}-code.
-/

lemma is_kst_code_even_edge_graphs_even_card_symmDiff {α : Type*} [DecidableEq α] (s t : Finset α)
    (hs : Even s.card) (ht : Even t.card) : Even (symmDiff s t).card := by
  have hd : Disjoint (s \ t) (t \ s) := disjoint_sdiff_sdiff
  have h1 : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
    change (s \ t ∪ t \ s).card = (s \ t).card + (t \ s).card
    exact Finset.card_union_of_disjoint hd
  have h2 : s.card = (s \ t).card + (s ∩ t).card := (Finset.card_sdiff_add_card_inter s t).symm
  have h3 : t.card = (t \ s).card + (s ∩ t).card := by
    rw [Finset.inter_comm]
    exact (Finset.card_sdiff_add_card_inter t s).symm
  rw [Nat.even_iff] at hs ht ⊢
  omega

lemma is_kst_code_even_edge_graphs_edgeFinset_symmDiff {V : Type*} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) :
    open Classical in (symmDiff G₁ G₂).edgeFinset = symmDiff G₁.edgeFinset G₂.edgeFinset := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_symmDiff,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
  change e ∈ (G₁ \ G₂ ⊔ G₂ \ G₁).edgeSet ↔ _
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_sdiff]
  rfl

lemma is_kst_code_even_edge_graphs_card_edgeFinset_between_top {V : Type*} [Fintype V] [DecidableEq V]
    (s t : Finset V) (h : Disjoint s t) :
    open Classical in ((⊤ : SimpleGraph V).between (s : Set V) (t : Set V)).edgeFinset.card = s.card * t.card := by
  classical
  let f : V × V → Sym2 V := fun (u, v) => s(u, v)
  have hinj : ∀ x ∈ s ×ˢ t, ∀ y ∈ s ×ˢ t, f x = f y → x = y := by
    rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
    rw [Finset.mem_product] at h₁ h₂
    simp only [f, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · have hu₁ : u₁ ∈ s ∩ t := Finset.mem_inter.mpr ⟨h₁.1, h₂.2⟩
      rw [Finset.disjoint_iff_inter_eq_empty.mp h] at hu₁
      exact False.elim (Finset.notMem_empty _ hu₁)
  have himg : ((⊤ : SimpleGraph V).between (s : Set V) (t : Set V)).edgeFinset =
      (s ×ˢ t).image f := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, Finset.mem_image]
    induction' e using Sym2.ind with u v
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.between_adj, SimpleGraph.top_adj]
    constructor
    · rintro ⟨hne, (⟨hu, hv⟩ | ⟨hu, hv⟩)⟩
      · refine ⟨(u, v), ?_, rfl⟩
        rw [Finset.mem_product]
        exact ⟨hu, hv⟩
      · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
        rw [Finset.mem_product]
        exact ⟨hv, hu⟩
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      rw [Finset.mem_product] at hab
      simp only [f, Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨?_, Or.inl ⟨hab.1, hab.2⟩⟩
        rintro rfl
        have hab_inter : a ∈ s ∩ t := Finset.mem_inter.mpr ⟨hab.1, hab.2⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp h] at hab_inter
        exact Finset.notMem_empty _ hab_inter
      · refine ⟨?_, Or.inr ⟨hab.2, hab.1⟩⟩
        rintro rfl
        have hab_inter : b ∈ s ∩ t := Finset.mem_inter.mpr ⟨hab.1, hab.2⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp h] at hab_inter
        exact Finset.notMem_empty _ hab_inter
  rw [himg, Finset.card_image_of_injOn hinj, Finset.card_product]

/-- The family of graphs with an even number of edges is a K_{s,t}-code when s and t are odd. -/
theorem is_kst_code_even_edge_graphs (s t n : ℕ) (hs : Odd s) (ht : Odd t) :
    is_kst_code s t n (open Classical in {G : SimpleGraph (Fin n) | Even G.edgeFinset.card}) := by
  classical
  intro G G' hG hG' _hdiff A B hAB hA hB heq
  change Even G.edgeFinset.card at hG
  change Even G'.edgeFinset.card at hG'
  have heven : Even (symmDiff G G').edgeFinset.card := by
    rw [is_kst_code_even_edge_graphs_edgeFinset_symmDiff]
    exact is_kst_code_even_edge_graphs_even_card_symmDiff G.edgeFinset G'.edgeFinset hG hG'
  have heq_finset : (symmDiff G G').edgeFinset =
      ((⊤ : SimpleGraph (Fin n)).between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset := by
    apply Finset.ext
    intro e
    simp [SimpleGraph.mem_edgeFinset, heq]
  have heven' : Even ((⊤ : SimpleGraph (Fin n)).between (A : Set (Fin n)) (B : Set (Fin n))).edgeFinset.card := by
    rwa [← heq_finset]
  rw [is_kst_code_even_edge_graphs_card_edgeFinset_between_top A B hAB, hA, hB] at heven'
  have hodd : Odd (s * t) := Odd.mul hs ht
  exact (Nat.not_odd_iff_even.mpr heven') hodd
