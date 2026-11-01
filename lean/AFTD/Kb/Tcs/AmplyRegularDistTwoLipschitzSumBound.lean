import AFTD.Prelude
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# amply_regular_dist_two_lipschitz_sum_bound

Topic: graphs   Node: ea02ff119cd7

Provenance: helper lemma. step towards amply_regular_diameter_bound_qpk

Scale-two Lipschitz estimate of arXiv:2610.36620, Section 3.1 (inequality (21) with gain B ≥ μ): let G be amply regular with parameters (k, ℓ, μ) with μ > 1 and ℓ ≤ μ, and let p, q be vertices at distance 2. Then for every 1-Lipschitz f : V → ℝ the two neighbourhood sums over N(p) and N(q) differ by at most 2(k − μ). Equivalently (Kantorovich duality) the Ollivier–Ricci curvature of the pair (p, q) is at least μ/k. Tight for the hypercube Q_n (k = n, ℓ = 0, μ = 2) and for K_{m,m}; the hypothesis μ > 1 is needed (large cycles, μ = 1, are counterexamples).
-/

/-- Distance-two 1-Lipschitz estimate for amply regular graphs: |Σ_{N(p)} f − Σ_{N(q)} f| ≤ 2(k − μ) whenever dist p q = 2, μ > 1 and ℓ ≤ μ. -/
theorem amply_regular_dist_two_lipschitz_sum_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k ℓ μ : ℕ} (hG : IsAmplyRegular G k ℓ μ) (hμ1 : 1 < μ) (hμℓ : ℓ ≤ μ)
    {p q : V} (hpq : G.dist p q = 2) (f : V → ℝ)
    (hf : ∀ a b : V, |f a - f b| ≤ (G.dist a b : ℝ)) :
    |∑ z ∈ G.neighborFinset p, f z - ∑ z ∈ G.neighborFinset q, f z| ≤ 2 * ((k - μ : ℕ) : ℝ) := by
  classical
  have key : ∀ (p0 q0 : V), G.dist p0 q0 = 2 →
      (∑ z ∈ G.neighborFinset q0 \ G.neighborFinset p0, f z)
        - (∑ z ∈ G.neighborFinset p0 \ G.neighborFinset q0, f z) ≤ 2 * ((k - μ : ℕ) : ℝ) := by
    intro p0 q0 hpq
    set C := G.neighborFinset p0 ∩ G.neighborFinset q0 with hCdef
    set X := G.neighborFinset p0 \ G.neighborFinset q0 with hXdef
    set Y := G.neighborFinset q0 \ G.neighborFinset p0 with hYdef
    have interCard : ∀ a b : V,
        (G.neighborFinset a ∩ G.neighborFinset b).card = Fintype.card (G.commonNeighbors a b) := by
      intro a b
      rw [← Set.toFinset_card]; congr 1; ext x
      simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_neighborFinset]
    have hcn_adj : ∀ a b : V, G.Adj a b → (G.neighborFinset a ∩ G.neighborFinset b).card = ℓ := by
      intro a b hab; rw [interCard]; exact hG.adj_commonNeighbors hab
    have hcn_dist : ∀ a b : V, G.dist a b = 2 →
        (G.neighborFinset a ∩ G.neighborFinset b).card = μ := by
      intro a b hab; rw [interCard]; exact hG.dist_two_commonNeighbors hab
    have dist2 : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c → a ≠ c → G.dist a c = 2 := by
      intro a b c hab hbc hac hne
      have hle : G.dist a c ≤ 2 := by
        have h := SimpleGraph.dist_le
          (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc SimpleGraph.Walk.nil) : G.Walk a c)
        simpa using h
      have hreach : G.Reachable a c :=
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc SimpleGraph.Walk.nil)).reachable
      have hgt : 1 < G.dist a c := hreach.one_lt_dist_of_ne_of_not_adj hne hac
      omega
    have hNp : (G.neighborFinset p0).card = k := by
      rw [G.card_neighborFinset_eq_degree, hG.regular.degree_eq p0]
    have hNq : (G.neighborFinset q0).card = k := by
      rw [G.card_neighborFinset_eq_degree, hG.regular.degree_eq q0]
    have hC_card : C.card = μ := by
      rw [hCdef, interCard, hG.dist_two_commonNeighbors hpq]
    have hCne : C.Nonempty := Finset.card_pos.mp (by rw [hC_card]; omega)
    obtain ⟨z, hzC⟩ := hCne
    have hzNp : z ∈ G.neighborFinset p0 := (Finset.mem_inter.mp (hCdef ▸ hzC)).1
    have hzNq : z ∈ G.neighborFinset q0 := (Finset.mem_inter.mp (hCdef ▸ hzC)).2
    have hzp : G.Adj z p0 := ((G.mem_neighborFinset p0 z).mp hzNp).symm
    have hzq : G.Adj z q0 := ((G.mem_neighborFinset q0 z).mp hzNq).symm
    have hpq_adj : ¬ G.Adj p0 q0 := by
      intro h; have : G.dist p0 q0 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
    set Z := G.neighborFinset z \ ({p0, q0} : Finset V) with hZdef
    have hNp_split : G.neighborFinset p0 = X ∪ C := by
      rw [hXdef, hCdef, Finset.sdiff_union_inter]
    have hNq_split : G.neighborFinset q0 = Y ∪ C := by
      rw [hYdef, hCdef, Finset.inter_comm, Finset.sdiff_union_inter]
    have hXC : Disjoint X C := by
      rw [hXdef, hCdef, Finset.disjoint_left]; intro a ha hb
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
    have hYC : Disjoint Y C := by
      rw [hYdef, hCdef, Finset.disjoint_left]; intro a ha hb
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).1
    have hXmem : ∀ w : V, w ∈ X ↔ G.Adj w p0 ∧ ¬ G.Adj w q0 := by
      intro w; rw [hXdef]; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    have hYmem : ∀ w : V, w ∈ Y ↔ G.Adj w q0 ∧ ¬ G.Adj w p0 := by
      intro w; rw [hYdef]; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    have hXval : ∀ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ)
        = ((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if x ∈ Z then 1 else 0) := by
      intro x hx
      have hxp : G.Adj x p0 := ((hXmem x).mp hx).1
      have hxq : ¬ G.Adj x q0 := ((hXmem x).mp hx).2
      have hxNq : x ∉ G.neighborFinset q0 := fun h => hxq ((G.mem_neighborFinset q0 x).mp h).symm
      have hxNp_ne : x ≠ p0 := fun h => G.irrefl (h ▸ hxp)
      have hxq_ne : x ≠ q0 := fun h => hpq_adj (h ▸ hxp).symm
      have hxmem : x ∉ ({p0, q0} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxNp_ne, hxq_ne⟩
      have hxne_z : x ≠ z := fun h => hxNq (h ▸ hzNq)
      have hrel : (G.neighborFinset x ∩ Z).card + 1
          = (G.neighborFinset x ∩ G.neighborFinset z).card := by
        have hunion : G.neighborFinset x ∩ G.neighborFinset z
            = (G.neighborFinset x ∩ Z) ∪ {p0} := by
          rw [hZdef]; ext w
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff,
            SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨hxw, hzw⟩
            by_cases hwp : w = p0
            · exact Or.inr hwp
            · refine Or.inl ⟨hxw, hzw, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hwp, fun h => hxq (h ▸ hxw)⟩
          · rintro (⟨hxw, hzw, -⟩ | rfl)
            · exact ⟨hxw, hzw⟩
            · exact ⟨hxp, hzp⟩
        rw [hunion, Finset.card_union_of_disjoint, Finset.card_singleton]
        rw [Finset.disjoint_singleton_right]; rw [hZdef]; simp
      by_cases hxZ : x ∈ Z
      · have hxNz : x ∈ G.neighborFinset z := (Finset.mem_sdiff.mp (hZdef ▸ hxZ)).1
        have hxz : G.Adj x z := ((G.mem_neighborFinset z x).mp hxNz).symm
        have hcn : (G.neighborFinset x ∩ G.neighborFinset z).card = ℓ := hcn_adj x z hxz
        have hcard : (G.neighborFinset x ∩ Z).card = ℓ - 1 := by omega
        rw [hcard, if_pos hxZ, Nat.cast_sub (by omega : 1 ≤ ℓ)]
        push_cast; ring
      · have hxNz : x ∉ G.neighborFinset z := by
          intro h; exact hxZ (by rw [hZdef, Finset.mem_sdiff]; exact ⟨h, hxmem⟩)
        have hxz_adj : ¬ G.Adj x z := fun h => hxNz ((G.mem_neighborFinset z x).mpr h.symm)
        have hdist : G.dist x z = 2 := dist2 x p0 z hxp hzp.symm hxz_adj hxne_z
        have hcn : (G.neighborFinset x ∩ G.neighborFinset z).card = μ := hcn_dist x z hdist
        have hcard : (G.neighborFinset x ∩ Z).card = μ - 1 := by omega
        rw [hcard, if_neg hxZ, Nat.cast_sub (by omega : 1 ≤ μ)]
        push_cast; ring
    have hXbound : ∀ x ∈ X, (G.neighborFinset x ∩ Z).card ≤ μ - 1 := by
      intro x hx
      have hv := hXval x hx
      have hμ1' : 1 ≤ μ := by omega
      have kk : ((G.neighborFinset x ∩ Z).card : ℝ) ≤ (μ:ℝ) - 1 := by
        rw [hv]
        by_cases hxZ : x ∈ Z
        · rw [if_pos hxZ]
          have hℓμ : (ℓ:ℝ) ≤ (μ:ℝ) := by exact_mod_cast hμℓ
          linarith
        · rw [if_neg hxZ]; linarith
      have kk2 : ((G.neighborFinset x ∩ Z).card : ℝ) ≤ ((μ - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hμ1']; simpa using kk
      exact Nat.cast_le.mp kk2
    have hYval : ∀ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ)
        = ((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if y ∈ Z then 1 else 0) := by
      intro y hy
      have hyq : G.Adj y q0 := ((hYmem y).mp hy).1
      have hyp : ¬ G.Adj y p0 := ((hYmem y).mp hy).2
      have hyNp : y ∉ G.neighborFinset p0 := fun h => hyp ((G.mem_neighborFinset p0 y).mp h).symm
      have hyNq_ne : y ≠ q0 := fun h => G.irrefl (h ▸ hyq)
      have hyp_ne : y ≠ p0 := fun h => hpq_adj (h ▸ hyq)
      have hymem : y ∉ ({p0, q0} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hyp_ne, hyNq_ne⟩
      have hyne_z : y ≠ z := fun h => hyNp (h ▸ hzNp)
      have hrel : (G.neighborFinset y ∩ Z).card + 1
          = (G.neighborFinset y ∩ G.neighborFinset z).card := by
        have hunion : G.neighborFinset y ∩ G.neighborFinset z
            = (G.neighborFinset y ∩ Z) ∪ {q0} := by
          rw [hZdef]; ext w
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff,
            SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨hyw, hzw⟩
            by_cases hwq : w = q0
            · exact Or.inr hwq
            · refine Or.inl ⟨hyw, hzw, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h => hyp (h ▸ hyw), hwq⟩
          · rintro (⟨hyw, hzw, -⟩ | rfl)
            · exact ⟨hyw, hzw⟩
            · exact ⟨hyq, hzq⟩
        rw [hunion, Finset.card_union_of_disjoint, Finset.card_singleton]
        rw [Finset.disjoint_singleton_right]; rw [hZdef]; simp
      by_cases hyZ : y ∈ Z
      · have hyNz : y ∈ G.neighborFinset z := (Finset.mem_sdiff.mp (hZdef ▸ hyZ)).1
        have hyz : G.Adj y z := ((G.mem_neighborFinset z y).mp hyNz).symm
        have hcn : (G.neighborFinset y ∩ G.neighborFinset z).card = ℓ := hcn_adj y z hyz
        have hcard : (G.neighborFinset y ∩ Z).card = ℓ - 1 := by omega
        rw [hcard, if_pos hyZ, Nat.cast_sub (by omega : 1 ≤ ℓ)]
        push_cast; ring
      · have hyNz : y ∉ G.neighborFinset z := by
          intro h; exact hyZ (by rw [hZdef, Finset.mem_sdiff]; exact ⟨h, hymem⟩)
        have hyz_adj : ¬ G.Adj y z := fun h => hyNz ((G.mem_neighborFinset z y).mpr h.symm)
        have hdist : G.dist y z = 2 := dist2 y q0 z hyq hzq.symm hyz_adj hyne_z
        have hcn : (G.neighborFinset y ∩ G.neighborFinset z).card = μ := hcn_dist y z hdist
        have hcard : (G.neighborFinset y ∩ Z).card = μ - 1 := by omega
        rw [hcard, if_neg hyZ, Nat.cast_sub (by omega : 1 ≤ μ)]
        push_cast; ring
    have hYbound : ∀ y ∈ Y, (G.neighborFinset y ∩ Z).card ≤ μ - 1 := by
      intro y hy
      have hv := hYval y hy
      have hμ1' : 1 ≤ μ := by omega
      have kk : ((G.neighborFinset y ∩ Z).card : ℝ) ≤ (μ:ℝ) - 1 := by
        rw [hv]
        by_cases hyZ : y ∈ Z
        · rw [if_pos hyZ]
          have hℓμ : (ℓ:ℝ) ≤ (μ:ℝ) := by exact_mod_cast hμℓ
          linarith
        · rw [if_neg hyZ]; linarith
      have kk2 : ((G.neighborFinset y ∩ Z).card : ℝ) ≤ ((μ - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hμ1']; simpa using kk
      exact Nat.cast_le.mp kk2
    have sum_swap : ∀ (A B : Finset V) (g : V → ℝ),
        (∑ a ∈ A, ∑ b ∈ G.neighborFinset a ∩ B, g b)
          = ∑ b ∈ B, ((G.neighborFinset b ∩ A).card : ℝ) * g b := by
      intro A B g
      have step1 : (∑ a ∈ A, ∑ b ∈ G.neighborFinset a ∩ B, g b)
          = ∑ a ∈ A, ∑ b ∈ B, (if G.Adj a b then g b else 0) := by
        apply Finset.sum_congr rfl; intro a _
        have hfil : G.neighborFinset a ∩ B = B.filter (G.Adj a) := by
          ext w; simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
        rw [hfil, Finset.sum_filter]
      rw [step1, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b _
      rw [← Finset.sum_filter]
      have hset : A.filter (fun a => G.Adj a b) = G.neighborFinset b ∩ A := by
        ext a; simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
      rw [hset, Finset.sum_const, nsmul_eq_mul]
    have hac : ∀ u : V, (G.neighborFinset u ∩ G.neighborFinset p0).card
        = (G.neighborFinset u ∩ X).card + (G.neighborFinset u ∩ C).card := by
      intro u
      conv_lhs => rw [hNp_split]
      rw [Finset.inter_union_distrib_left]
      have hd : Disjoint (G.neighborFinset u ∩ X) (G.neighborFinset u ∩ C) := by
        rw [Finset.disjoint_left]; intro a ha hb
        exact (Finset.disjoint_left.mp hXC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
      rw [Finset.card_union_of_disjoint hd]
    have hbc : ∀ u : V, (G.neighborFinset u ∩ G.neighborFinset q0).card
        = (G.neighborFinset u ∩ Y).card + (G.neighborFinset u ∩ C).card := by
      intro u
      conv_lhs => rw [hNq_split]
      rw [Finset.inter_union_distrib_left]
      have hd : Disjoint (G.neighborFinset u ∩ Y) (G.neighborFinset u ∩ C) := by
        rw [Finset.disjoint_left]; intro a ha hb
        exact (Finset.disjoint_left.mp hYC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
      rw [Finset.card_union_of_disjoint hd]
    have hcoef : ∀ u ∈ Z, ((G.neighborFinset u ∩ X).card : ℝ) - ((G.neighborFinset u ∩ Y).card : ℝ)
        = ((ℓ:ℝ) - μ) * (if u ∈ X then 1 else 0) + ((μ:ℝ) - ℓ) * (if u ∈ Y then 1 else 0) := by
      intro u hu
      have hu0 : u ∈ G.neighborFinset z \ ({p0, q0} : Finset V) := hZdef ▸ hu
      obtain ⟨huNz, humem⟩ := Finset.mem_sdiff.mp hu0
      have huz : G.Adj u z := ((G.mem_neighborFinset z u).mp huNz).symm
      have hune_p : u ≠ p0 := fun h => humem (by simp [h])
      have hune_q : u ≠ q0 := fun h => humem (by simp [h])
      have hcnp : ((G.neighborFinset u ∩ G.neighborFinset p0).card : ℝ)
          = ((G.neighborFinset u ∩ X).card : ℝ) + ((G.neighborFinset u ∩ C).card : ℝ) := by
        rw [hac u]; push_cast; ring
      have hcnq : ((G.neighborFinset u ∩ G.neighborFinset q0).card : ℝ)
          = ((G.neighborFinset u ∩ Y).card : ℝ) + ((G.neighborFinset u ∩ C).card : ℝ) := by
        rw [hbc u]; push_cast; ring
      have hdiff : ((G.neighborFinset u ∩ X).card : ℝ) - ((G.neighborFinset u ∩ Y).card : ℝ)
          = ((G.neighborFinset u ∩ G.neighborFinset p0).card : ℝ)
            - ((G.neighborFinset u ∩ G.neighborFinset q0).card : ℝ) := by
        rw [hcnp, hcnq]; ring
      have hcp : ((G.neighborFinset u ∩ G.neighborFinset p0).card : ℝ)
          = if G.Adj u p0 then (ℓ:ℝ) else (μ:ℝ) := by
        by_cases hadj : G.Adj u p0
        · rw [if_pos hadj, hcn_adj u p0 hadj]
        · rw [if_neg hadj, hcn_dist u p0 (dist2 u z p0 huz hzp hadj hune_p)]
      have hcq : ((G.neighborFinset u ∩ G.neighborFinset q0).card : ℝ)
          = if G.Adj u q0 then (ℓ:ℝ) else (μ:ℝ) := by
        by_cases hadj : G.Adj u q0
        · rw [if_pos hadj, hcn_adj u q0 hadj]
        · rw [if_neg hadj, hcn_dist u q0 (dist2 u z q0 huz hzq hadj hune_q)]
      rw [hdiff, hcp, hcq]
      by_cases hp : G.Adj u p0
      · by_cases hq : G.Adj u q0
        · have e1 : ¬ (u ∈ X) := fun h => ((hXmem u).mp h).2 hq
          have e2 : ¬ (u ∈ Y) := fun h => ((hYmem u).mp h).2 hp
          simp only [if_pos hp, if_pos hq, if_neg e1, if_neg e2]; ring
        · have e1 : u ∈ X := (hXmem u).mpr ⟨hp, hq⟩
          have e2 : ¬ (u ∈ Y) := fun h => ((hYmem u).mp h).2 hp
          simp only [if_pos hp, if_neg hq, if_pos e1, if_neg e2]; ring
      · by_cases hq : G.Adj u q0
        · have e1 : ¬ (u ∈ X) := fun h => hp ((hXmem u).mp h).1
          have e2 : u ∈ Y := (hYmem u).mpr ⟨hq, hp⟩
          simp only [if_neg hp, if_pos hq, if_neg e1, if_pos e2]; ring
        · have e1 : ¬ (u ∈ X) := fun h => hp ((hXmem u).mp h).1
          have e2 : ¬ (u ∈ Y) := fun h => hq ((hYmem u).mp h).1
          simp only [if_neg hp, if_neg hq, if_neg e1, if_neg e2]; ring
    have hterm : ∀ u ∈ Z, ((G.neighborFinset u ∩ X).card : ℝ) * f u
        - ((G.neighborFinset u ∩ Y).card : ℝ) * f u
        = ((ℓ:ℝ) - μ) * (if u ∈ X then f u else 0) + ((μ:ℝ) - ℓ) * (if u ∈ Y then f u else 0) := by
      intro u hu
      have hc := hcoef u hu
      have hst : ((G.neighborFinset u ∩ X).card : ℝ) * f u
          - ((G.neighborFinset u ∩ Y).card : ℝ) * f u
          = (((G.neighborFinset u ∩ X).card : ℝ) - ((G.neighborFinset u ∩ Y).card : ℝ)) * f u := by
        ring
      rw [hst, hc]
      by_cases hx : u ∈ X
      · by_cases hy : u ∈ Y
        · simp only [hx, hy, if_true, if_false]; ring
        · simp only [hx, hy, if_true, if_false]; ring
      · by_cases hy : u ∈ Y
        · simp only [hx, hy, if_true, if_false]; ring
        · simp only [hx, hy, if_true, if_false]; ring
    have haxp : ∀ x, (((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if x ∈ Z then 1 else 0)) * f x
        = ((μ:ℝ) - 1) * f x + ((ℓ:ℝ) - μ) * (if x ∈ Z then f x else 0) := by
      intro x; by_cases hxZ : x ∈ Z <;> simp only [hxZ, if_true, if_false] <;> ring
    have hA : (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
        + (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
        = ((∑ y ∈ Y, f y) - (∑ x ∈ X, f x)) * ((μ:ℝ) - 1) := by
      have e1 : (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
          = (∑ u ∈ Z, ((G.neighborFinset u ∩ X).card : ℝ) * f u)
            - (∑ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ) * f x) := by
        have ha : (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
            = (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, f w)
              - (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, f x) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro x hx
          rw [Finset.sum_sub_distrib]
        have hb : (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, f x)
            = ∑ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ) * f x := by
          apply Finset.sum_congr rfl; intro x hx
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [ha, hb, sum_swap X Z f]
      have e2 : (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
          = (∑ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ) * f y)
            - (∑ u ∈ Z, ((G.neighborFinset u ∩ Y).card : ℝ) * f u) := by
        have ha : (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
            = (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, f y)
              - (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, f w) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro y hy
          rw [Finset.sum_sub_distrib]
        have hb : (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, f y)
            = ∑ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ) * f y := by
          apply Finset.sum_congr rfl; intro y hy
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [ha, hb, sum_swap Y Z f]
      have e3 : (∑ u ∈ Z, ((G.neighborFinset u ∩ X).card : ℝ) * f u)
          - (∑ u ∈ Z, ((G.neighborFinset u ∩ Y).card : ℝ) * f u)
          = ((ℓ:ℝ) - μ) * (∑ x ∈ X ∩ Z, f x) + ((μ:ℝ) - ℓ) * (∑ y ∈ Y ∩ Z, f y) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.inter_comm Z X, Finset.inter_comm Z Y]
      have e4 : (∑ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ) * f x)
          = ((μ:ℝ) - 1) * (∑ x ∈ X, f x) + ((ℓ:ℝ) - μ) * (∑ x ∈ X ∩ Z, f x) := by
        rw [show (∑ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ) * f x)
            = ∑ x ∈ X, (((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if x ∈ Z then 1 else 0)) * f x
            from Finset.sum_congr rfl (fun x hx => by rw [hXval x hx])]
        rw [show (∑ x ∈ X, (((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if x ∈ Z then 1 else 0)) * f x)
            = ∑ x ∈ X, (((μ:ℝ) - 1) * f x + ((ℓ:ℝ) - μ) * (if x ∈ Z then f x else 0))
            from Finset.sum_congr rfl (fun x _ => haxp x)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_mem]
      have e5 : (∑ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ) * f y)
          = ((μ:ℝ) - 1) * (∑ y ∈ Y, f y) + ((ℓ:ℝ) - μ) * (∑ y ∈ Y ∩ Z, f y) := by
        rw [show (∑ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ) * f y)
            = ∑ y ∈ Y, (((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if y ∈ Z then 1 else 0)) * f y
            from Finset.sum_congr rfl (fun y hy => by rw [hYval y hy])]
        rw [show (∑ y ∈ Y, (((μ:ℝ) - 1) + ((ℓ:ℝ) - μ) * (if y ∈ Z then 1 else 0)) * f y)
            = ∑ y ∈ Y, (((μ:ℝ) - 1) * f y + ((ℓ:ℝ) - μ) * (if y ∈ Z then f y else 0))
            from Finset.sum_congr rfl (fun y _ => haxp y)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_mem]
      rw [e1, e2]
      linear_combination e3 - e4 + e5
    have hbound1 : (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
        ≤ ((X.card : ℝ)) * ((μ:ℝ) - 1) := by
      calc (∑ x ∈ X, ∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
          ≤ ∑ x ∈ X, ((G.neighborFinset x ∩ Z).card : ℝ) * 1 := by
            apply Finset.sum_le_sum; intro x hx
            calc (∑ w ∈ G.neighborFinset x ∩ Z, (f w - f x))
                ≤ ∑ w ∈ G.neighborFinset x ∩ Z, (1:ℝ) := by
                  apply Finset.sum_le_sum; intro w hw
                  have hxw : G.Adj x w := (G.mem_neighborFinset x w).mp (Finset.mem_inter.mp hw).1
                  have hd : G.dist w x = 1 := by
                    rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_eq_one_iff_adj.mpr hxw
                  have hb := hf w x
                  rw [hd] at hb; push_cast at hb
                  linarith [abs_le.mp hb]
              _ = ((G.neighborFinset x ∩ Z).card : ℝ) * 1 := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ X, ((μ - 1 : ℕ) : ℝ) := by
            apply Finset.sum_le_sum; intro x hx
            have hb := hXbound x hx
            have : ((G.neighborFinset x ∩ Z).card : ℝ) * 1 ≤ ((μ - 1 : ℕ) : ℝ) * 1 := by
              apply mul_le_mul_of_nonneg_right _ (by norm_num)
              exact_mod_cast hb
            simpa using this
        _ = ((X.card : ℝ)) * ((μ:ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ μ)]
            ring
    have hbound2 : (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
        ≤ ((Y.card : ℝ)) * ((μ:ℝ) - 1) := by
      calc (∑ y ∈ Y, ∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
          ≤ ∑ y ∈ Y, ((G.neighborFinset y ∩ Z).card : ℝ) * 1 := by
            apply Finset.sum_le_sum; intro y hy
            calc (∑ w ∈ G.neighborFinset y ∩ Z, (f y - f w))
                ≤ ∑ w ∈ G.neighborFinset y ∩ Z, (1:ℝ) := by
                  apply Finset.sum_le_sum; intro w hw
                  have hyw : G.Adj y w := (G.mem_neighborFinset y w).mp (Finset.mem_inter.mp hw).1
                  have hd : G.dist w y = 1 := by
                    rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_eq_one_iff_adj.mpr hyw
                  have hb := hf w y
                  rw [hd] at hb; push_cast at hb
                  linarith [abs_le.mp hb]
              _ = ((G.neighborFinset y ∩ Z).card : ℝ) * 1 := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ Y, ((μ - 1 : ℕ) : ℝ) := by
            apply Finset.sum_le_sum; intro y hy
            have hb := hYbound y hy
            have : ((G.neighborFinset y ∩ Z).card : ℝ) * 1 ≤ ((μ - 1 : ℕ) : ℝ) * 1 := by
              apply mul_le_mul_of_nonneg_right _ (by norm_num)
              exact_mod_cast hb
            simpa using this
        _ = ((Y.card : ℝ)) * ((μ:ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ μ)]
            ring
    have hμpos : (0:ℝ) < (μ:ℝ) - 1 := by
      have : (1:ℝ) < (μ:ℝ) := by exact_mod_cast hμ1
      linarith
    have hXc : ((X.card : ℝ)) = ((k - μ : ℕ) : ℝ) := by
      rw [hXdef, Finset.card_sdiff, Finset.inter_comm, interCard,
        hG.dist_two_commonNeighbors hpq, hNp]
    have hYc : ((Y.card : ℝ)) = ((k - μ : ℕ) : ℝ) := by
      rw [hYdef, Finset.card_sdiff, interCard, hG.dist_two_commonNeighbors hpq, hNq]
    have hle := add_le_add hbound1 hbound2
    rw [hXc, hYc, hA] at hle
    have hg : (∑ y ∈ Y, f y) - (∑ x ∈ X, f x)
        = (∑ z ∈ G.neighborFinset q0 \ G.neighborFinset p0, f z)
          - (∑ z ∈ G.neighborFinset p0 \ G.neighborFinset q0, f z) := by
      rw [hYdef, hXdef]
    rw [hg] at hle
    nlinarith [hμpos, hle]
  have h1 := key p q hpq
  have h2 := key q p (by rw [SimpleGraph.dist_comm]; exact hpq)
  have hsub : (∑ z ∈ G.neighborFinset p, f z) - (∑ z ∈ G.neighborFinset q, f z)
      = (∑ z ∈ G.neighborFinset p \ G.neighborFinset q, f z)
        - (∑ z ∈ G.neighborFinset q \ G.neighborFinset p, f z) := by
    have hs1 := Finset.sum_sdiff (s₁ := G.neighborFinset p ∩ G.neighborFinset q)
      (s₂ := G.neighborFinset p) (f := f) Finset.inter_subset_left
    have hs2 := Finset.sum_sdiff (s₁ := G.neighborFinset p ∩ G.neighborFinset q)
      (s₂ := G.neighborFinset q) (f := f) Finset.inter_subset_right
    rw [show G.neighborFinset p \ (G.neighborFinset p ∩ G.neighborFinset q)
        = G.neighborFinset p \ G.neighborFinset q from by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto] at hs1
    rw [show G.neighborFinset q \ (G.neighborFinset p ∩ G.neighborFinset q)
        = G.neighborFinset q \ G.neighborFinset p from by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto] at hs2
    linarith
  rw [abs_le, hsub]
  exact ⟨by linarith, h2⟩
