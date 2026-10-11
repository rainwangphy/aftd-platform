import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree
import AFTD.Kb.Tcs.G

/-!
# simple_graph_triangle_degree_compl

Topic: graphs   Node: 2143c30c2f55

Provenance: formalization of a published result. Source: arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Lemma 2.1 (first part); stated over ℚ so that N r / 2 and the subtraction are exact.

Let G be an r-regular simple graph on N vertices. For every vertex v, td_{Ḡ}(v) = C(N − r − 1, 2) − N r / 2 + r² − td_G(v), where Ḡ is the complement of G.
-/

theorem triangle_compl_two_mul_card_clique_pairs {V : Type*} [DecidableEq V] (S : Finset V)
    (R : V → V → Prop) [DecidableRel R] :
    2 * ((S.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y)).card =
      (S.offDiag.filter (fun p => R p.1 p.2 ∧ R p.2 p.1)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : V × V => ({p.1, p.2} : Finset V))
    (t := (S.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y))]
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨hts, hcl⟩ := Finset.mem_filter.1 ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hts
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    have hfib : ((S.offDiag.filter fun p => R p.1 p.2 ∧ R p.2 p.1).filter
        fun p => ({p.1, p.2} : Finset V) = {a, b}) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hx, hy, hxy⟩, hr⟩, heq⟩
        have hx' : x ∈ ({a, b} : Finset V) := heq ▸ (by simp)
        have hy' : y ∈ ({a, b} : Finset V) := heq ▸ (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
        rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨hsub (by simp), hsub (by simp), hab⟩,
            hcl _ (by simp) _ (by simp) hab, hcl _ (by simp) _ (by simp) hab.symm⟩, rfl⟩
        · exact ⟨⟨⟨hsub (by simp), hsub (by simp), hab.symm⟩,
            hcl _ (by simp) _ (by simp) hab.symm, hcl _ (by simp) _ (by simp) hab⟩,
            Finset.pair_comm _ _⟩
    rw [hfib, Finset.card_pair (by simp [hab])]
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨hx, hy, hxy⟩, hr1, hr2⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair hxy⟩, ?_⟩
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · intro z hz w hw hzw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz hw
      rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> simp_all

def triangle_compl_adj_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ := ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0

theorem triangle_compl_adj_count_union_left {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S S' T : Finset V) (h : Disjoint S S') :
    triangle_compl_adj_count G (S ∪ S') T = triangle_compl_adj_count G S T + triangle_compl_adj_count G S' T := by
  unfold triangle_compl_adj_count; rw [Finset.sum_union h]

theorem triangle_compl_adj_count_union_right {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S T T' : Finset V) (h : Disjoint T T') :
    triangle_compl_adj_count G S (T ∪ T') = triangle_compl_adj_count G S T + triangle_compl_adj_count G S T' := by
  unfold triangle_compl_adj_count; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_union h

theorem triangle_compl_adj_count_comm {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : triangle_compl_adj_count G S T = triangle_compl_adj_count G T S := by
  unfold triangle_compl_adj_count; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp [G.adj_comm]

theorem triangle_compl_adj_count_univ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : triangle_compl_adj_count G S Finset.univ = ∑ x ∈ S, G.degree x := by
  unfold triangle_compl_adj_count
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  simp

theorem triangle_compl_adj_count_self {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    triangle_compl_adj_count G S S = 2 * ((S.powersetCard 2).filter
      (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card := by
  have h2 := triangle_compl_two_mul_card_clique_pairs S G.Adj
  have h : S.offDiag.filter (fun p => G.Adj p.1 p.2 ∧ G.Adj p.2 p.1) =
      (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨hx, hy, -⟩, h, -⟩; exact ⟨⟨hx, hy⟩, h⟩
    · rintro ⟨⟨hx, hy⟩, h⟩; exact ⟨⟨hx, hy, h.ne⟩, h, h.symm⟩
  have h3 : triangle_compl_adj_count G S S =
      (S.offDiag.filter (fun p => G.Adj p.1 p.2 ∧ G.Adj p.2 p.1)).card := by
    rw [h, Finset.card_filter, Finset.sum_product]
    rfl
  rw [h3]
  convert h2.symm

theorem triangle_compl_adj_count_singleton_nbr {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    triangle_compl_adj_count G (G.neighborFinset v) {v} = G.degree v := by
  unfold triangle_compl_adj_count
  simp only [Finset.sum_singleton]
  rw [Finset.sum_congr rfl (g := fun _ => 1), Finset.sum_const, smul_eq_mul, mul_one,
    G.card_neighborFinset_eq_degree]
  intro x hx
  rw [SimpleGraph.mem_neighborFinset] at hx
  simp [hx.symm]

theorem triangle_compl_adj_count_singleton_self {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : triangle_compl_adj_count G {v} {v} = 0 := by
  simp [triangle_compl_adj_count]

theorem triangle_compl_adj_count_nonnbr_singleton {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (B : Finset V) (hB : ∀ x ∈ B, ¬ G.Adj x v) :
    triangle_compl_adj_count G B {v} = 0 := by
  unfold triangle_compl_adj_count
  simp only [Finset.sum_singleton]
  exact Finset.sum_eq_zero fun x hx => by simp [hB x hx]

theorem triangle_compl_pair_clique_iff {V : Type*} [DecidableEq V] (R : V → V → Prop) {a b : V}
    (hab : a ≠ b) :
    (∀ x ∈ ({a, b} : Finset V), ∀ y ∈ ({a, b} : Finset V), x ≠ y → R x y) ↔ R a b ∧ R b a := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl) b (Or.inr rfl) hab, h b (Or.inr rfl) a (Or.inl rfl) hab.symm⟩
  · rintro ⟨h1, h2⟩ x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h1
    · exact h2
    · exact absurd rfl hxy

theorem simple_graph_triangle_degree_compl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r N : ℕ) (hN : Fintype.card V = N)
    (hreg : G.IsRegularOfDegree r) (v : V) :
    (simple_graph_triangle_degree Gᶜ v : ℚ) =
      ((N - r - 1).choose 2 : ℚ) - (N * r : ℚ) / 2 + (r : ℚ) ^ 2 -
        simple_graph_triangle_degree G v := by
  set A := G.neighborFinset v with hA
  set B := Gᶜ.neighborFinset v with hB
  have hBeq : B = Finset.univ \ insert v A := by
    ext x
    simp only [hB, hA, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj, Finset.mem_sdiff,
      Finset.mem_univ, Finset.mem_insert, true_and]
    constructor
    · rintro ⟨hne, hna⟩; rintro (rfl | h)
      · exact hne rfl
      · exact hna h
    · intro h; exact ⟨fun e => h (Or.inl e.symm), fun e => h (Or.inr e)⟩
  have hvA : v ∉ A := by simp [hA]
  have hcardA : A.card = r := by rw [hA, G.card_neighborFinset_eq_degree, hreg v]
  have hcardB : B.card = N - r - 1 := by
    rw [hBeq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hN,
      Finset.card_insert_of_notMem hvA, hcardA]
    omega
  have hdisjAB : Disjoint A B := by
    rw [hBeq]; exact Finset.disjoint_sdiff.mono_left (Finset.subset_insert _ _)
  have hdisjv : Disjoint {v} (A ∪ B) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_union, not_or]
    exact ⟨hvA, by rw [hBeq]; simp⟩
  have huniv : (Finset.univ : Finset V) = {v} ∪ (A ∪ B) := by
    ext x; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, true_iff]
    by_cases h1 : x = v
    · exact Or.inl h1
    · by_cases h2 : x ∈ A
      · exact Or.inr (Or.inl h2)
      · right; right; rw [hBeq]; simp [h1, h2]
  have hBnv : ∀ x ∈ B, ¬ G.Adj x v := by
    intro x hx h; rw [hBeq] at hx; simp at hx
    exact hx.2 (by rw [hA, SimpleGraph.mem_neighborFinset]; exact h.symm)
  -- the counts
  set eA := ((A.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card
  set eB := ((B.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card
  have htdG : simple_graph_triangle_degree G v = eA := rfl
  have hfilt : (B.powersetCard 2).filter
        (fun s => ¬ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Gᶜ.Adj x y) =
      (B.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y) := by
    apply Finset.filter_congr
    intro s hs
    obtain ⟨-, hc⟩ := Finset.mem_powersetCard.1 hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
    rw [triangle_compl_pair_clique_iff _ hab, triangle_compl_pair_clique_iff _ hab]
    simp only [SimpleGraph.compl_adj]
    constructor
    · intro h
      by_contra hn
      apply h
      refine ⟨⟨hab, fun h1 => hn ⟨h1, h1.symm⟩⟩, ⟨hab.symm, fun h2 => hn ⟨h2.symm, h2⟩⟩⟩
    · rintro ⟨h1, -⟩ ⟨⟨-, h2⟩, -⟩
      exact h2 h1
  have htdC : simple_graph_triangle_degree Gᶜ v + eB = (N - r - 1).choose 2 := by
    calc simple_graph_triangle_degree Gᶜ v + eB
        = ((B.powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Gᶜ.Adj x y)).card +
          ((B.powersetCard 2).filter
            (fun s => ¬ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Gᶜ.Adj x y)).card := by
          rw [hfilt]; rfl
      _ = (B.powersetCard 2).card := Finset.card_filter_add_card_filter_not _
      _ = _ := by rw [Finset.card_powersetCard, hcardB]
  have e1 : triangle_compl_adj_count G Finset.univ Finset.univ = N * r := by
    rw [triangle_compl_adj_count_univ, Finset.sum_congr rfl (fun x _ => hreg x), Finset.sum_const,
      Finset.card_univ, hN, smul_eq_mul]
  have e2 : triangle_compl_adj_count G A Finset.univ = r * r := by
    rw [triangle_compl_adj_count_univ, Finset.sum_congr rfl (fun x _ => hreg x), Finset.sum_const, hcardA,
      smul_eq_mul]
  have e3 : triangle_compl_adj_count G A Finset.univ = triangle_compl_adj_count G A {v} + (triangle_compl_adj_count G A A + triangle_compl_adj_count G A B) := by
    calc triangle_compl_adj_count G A Finset.univ = triangle_compl_adj_count G A ({v} ∪ (A ∪ B)) := by rw [← huniv]
      _ = _ := by rw [triangle_compl_adj_count_union_right _ _ _ _ hdisjv, triangle_compl_adj_count_union_right _ _ _ _ hdisjAB]
  have e4 : triangle_compl_adj_count G Finset.univ Finset.univ =
      triangle_compl_adj_count G {v} Finset.univ + (triangle_compl_adj_count G A Finset.univ + triangle_compl_adj_count G B Finset.univ) := by
    calc triangle_compl_adj_count G Finset.univ Finset.univ = triangle_compl_adj_count G ({v} ∪ (A ∪ B)) Finset.univ := by rw [← huniv]
      _ = _ := by rw [triangle_compl_adj_count_union_left _ _ _ _ hdisjv, triangle_compl_adj_count_union_left _ _ _ _ hdisjAB]
  have e5 : triangle_compl_adj_count G B Finset.univ = triangle_compl_adj_count G B {v} + (triangle_compl_adj_count G B A + triangle_compl_adj_count G B B) := by
    calc triangle_compl_adj_count G B Finset.univ = triangle_compl_adj_count G B ({v} ∪ (A ∪ B)) := by rw [← huniv]
      _ = _ := by rw [triangle_compl_adj_count_union_right _ _ _ _ hdisjv, triangle_compl_adj_count_union_right _ _ _ _ hdisjAB]
  have e6 : triangle_compl_adj_count G {v} Finset.univ = r := by
    rw [triangle_compl_adj_count_univ, Finset.sum_singleton, hreg v]
  have e7 : triangle_compl_adj_count G A {v} = r := by
    rw [hA, triangle_compl_adj_count_singleton_nbr, hreg v]
  have e8 : triangle_compl_adj_count G B {v} = 0 := triangle_compl_adj_count_nonnbr_singleton G v B hBnv
  have e9 : triangle_compl_adj_count G B A = triangle_compl_adj_count G A B := triangle_compl_adj_count_comm G B A
  have eAA : triangle_compl_adj_count G A A = 2 * eA := triangle_compl_adj_count_self G A
  have eBB : triangle_compl_adj_count G B B = 2 * eB := triangle_compl_adj_count_self G B
  have key1 : N * r = r + r * r + triangle_compl_adj_count G A B + 2 * eB := by
    rw [← e1, e4, e6, e2, e5, e8, e9, eBB]; ring
  have key2 : r * r = r + 2 * eA + triangle_compl_adj_count G A B := by
    rw [← e2, e3, e7, eAA]; ring
  have q1 : (N : ℚ) * r = r + r * r + (triangle_compl_adj_count G A B : ℚ) + 2 * eB := by exact_mod_cast key1
  have q2 : (r : ℚ) * r = r + 2 * eA + (triangle_compl_adj_count G A B : ℚ) := by exact_mod_cast key2
  have q3 : (simple_graph_triangle_degree Gᶜ v : ℚ) + eB = ((N - r - 1).choose 2 : ℕ) := by
    exact_mod_cast htdC
  rw [htdG]
  linarith
