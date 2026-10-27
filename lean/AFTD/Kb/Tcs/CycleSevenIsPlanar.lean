import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsPlanar
import AFTD.Kb.Tcs.SimpleGraphIsMinor

/-!
# cycle_seven_is_planar

Topic: graphs   Node: a0b29dd89daf

Provenance: helper lemma. folklore; OP-537

The 7-cycle graph C_7 is planar.
-/

private lemma cycle_seven_is_planar_neighbor_bound (x : Fin 7) (t : Finset (Fin 7))
    (h : ∀ y ∈ t, (SimpleGraph.cycleGraph 7).Adj x y) : t.card ≤ 2 := by
  revert x t
  decide

private lemma cycle_seven_is_planar_sum_ncard_le {ι : Type} [Fintype ι] (B : ι → Set (Fin 7))
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    (∑ i, (B i).ncard) ≤ 7 := by
  have hfin : ∀ i, (B i).Finite := fun i => Set.toFinite _
  have hpd : Pairwise (Function.onFun Disjoint B) := hdisj
  rw [← finsum_eq_sum_of_fintype (fun i => (B i).ncard)]
  rw [← Set.ncard_iUnion_of_finite hfin hpd]
  calc (⋃ i, B i).ncard ≤ (Set.univ : Set (Fin 7)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 7 := by simp

private lemma cycle_seven_is_planar_exists_singleton {ι : Type} [Fintype ι]
    (hcard : 7 < 2 * Fintype.card ι) (B : ι → Set (Fin 7))
    (hne : ∀ i, (B i).Nonempty) (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    ∃ i, ∃ x, B i = {x} := by
  by_contra h
  push Not at h
  have h2 : ∀ i, 2 ≤ (B i).ncard := by
    intro i
    have hpos : 1 ≤ (B i).ncard := (Set.ncard_pos (Set.toFinite _)).mpr (hne i)
    have hne1 : (B i).ncard ≠ 1 := by
      intro h1
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      exact h i a ha
    omega
  have hsum2 : (∑ _i : ι, (2:ℕ)) = 2 * Fintype.card ι := by
    simp [Finset.sum_const, Nat.mul_comm]
  have hge : 2 * Fintype.card ι ≤ ∑ i, (B i).ncard := by
    have hle : (∑ _i : ι, (2:ℕ)) ≤ ∑ i, (B i).ncard := Finset.sum_le_sum (fun i _ => h2 i)
    rwa [hsum2] at hle
  have hle := cycle_seven_is_planar_sum_ncard_le B hdisj
  omega

private lemma cycle_seven_is_planar_not_K5 :
    ¬ simple_graph_is_minor (⊤ : SimpleGraph (Fin 5)) (SimpleGraph.cycleGraph 7) := by
  classical
  rintro ⟨B, hconn, hdisj, hadj⟩
  have hne : ∀ i, (B i).Nonempty := fun i => Set.nonempty_coe_sort.mp (hconn i).nonempty
  obtain ⟨u, x, hx⟩ := cycle_seven_is_planar_exists_singleton (ι := Fin 5) (by norm_num) B hne hdisj
  have hwit : ∀ v : Fin 5, v ≠ u → ∃ y ∈ B v, (SimpleGraph.cycleGraph 7).Adj x y := by
    intro v hv
    obtain ⟨x', hx'u, y, hyv, hadj'⟩ := hadj u v (by simpa using hv.symm)
    have hx' : x' = x := by
      have h1 : x' ∈ ({x} : Set (Fin 7)) := hx ▸ hx'u
      simpa using h1
    exact ⟨y, hyv, by simpa [hx'] using hadj'⟩
  set f : Fin 5 → Fin 7 := fun v => if h : v = u then x else Classical.choose (hwit v h) with hfdef
  have hf_spec : ∀ v (hv : v ≠ u), f v ∈ B v ∧ (SimpleGraph.cycleGraph 7).Adj x (f v) := by
    intro v hv
    have heq : f v = Classical.choose (hwit v hv) := by simp [hfdef, hv]
    rw [heq]
    exact Classical.choose_spec (hwit v hv)
  have hinj : Set.InjOn f ↑(Finset.univ.erase u) := by
    intro v hv w hw hvw
    have hv' : v ≠ u := by simpa using hv
    have hw' : w ≠ u := by simpa using hw
    by_contra hne
    have h1 : f v ∈ B v := (hf_spec v hv').1
    have h2 : f w ∈ B w := (hf_spec w hw').1
    have h3 : f v ∈ B w := by rw [hvw]; exact h2
    exact (Set.disjoint_left.mp (hdisj v w hne)) h1 h3
  have hcard : ((Finset.univ.erase u).image f).card = 4 := by
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hall : ∀ y ∈ (Finset.univ.erase u).image f, (SimpleGraph.cycleGraph 7).Adj x y := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (hf_spec v (by simpa using hv)).2
  have := cycle_seven_is_planar_neighbor_bound x _ hall
  omega

private lemma cycle_seven_is_planar_K33_aux
    (B : Fin 3 ⊕ Fin 3 → Set (Fin 7))
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hadj : ∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v →
      ∃ x ∈ B u, ∃ y ∈ B v, (SimpleGraph.cycleGraph 7).Adj x y)
    (u : Fin 3 ⊕ Fin 3) (x : Fin 7) (hx : B u = {x})
    (g : Fin 3 → Fin 3 ⊕ Fin 3) (hg_inj : Function.Injective g)
    (hg_adj : ∀ j, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u (g j)) : False := by
  classical
  have key : ∀ j : Fin 3, ∃ y ∈ B (g j), (SimpleGraph.cycleGraph 7).Adj x y := by
    intro j
    obtain ⟨x', hx'u, y, hyv, hadj'⟩ := hadj u (g j) (hg_adj j)
    have hx' : x' = x := by
      have h1 : x' ∈ ({x} : Set (Fin 7)) := hx ▸ hx'u
      simpa using h1
    exact ⟨y, hyv, by simpa [hx'] using hadj'⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h1 : f i ∈ B (g i) := (hf i).1
    have h2 : f j ∈ B (g j) := (hf j).1
    have h3 : f i ∈ B (g j) := by rw [hij]; exact h2
    have hgij : g i ≠ g j := fun h => hne (hg_inj h)
    exact (Set.disjoint_left.mp (hdisj _ _ hgij)) h1 h3
  have hcard : (Finset.univ.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hall : ∀ y ∈ Finset.univ.image f, (SimpleGraph.cycleGraph 7).Adj x y := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hf j).2
  have hb := cycle_seven_is_planar_neighbor_bound x _ hall
  omega

private lemma cycle_seven_is_planar_not_K33 :
    ¬ simple_graph_is_minor (completeBipartiteGraph (Fin 3) (Fin 3)) (SimpleGraph.cycleGraph 7) := by
  classical
  rintro ⟨B, hconn, hdisj, hadj⟩
  have hne : ∀ i, (B i).Nonempty := fun i => Set.nonempty_coe_sort.mp (hconn i).nonempty
  obtain ⟨u, x, hx⟩ := cycle_seven_is_planar_exists_singleton (ι := Fin 3 ⊕ Fin 3) (by simp) B hne hdisj
  rcases u with a | b
  · exact cycle_seven_is_planar_K33_aux B hdisj hadj (Sum.inl a) x hx
      (fun j => (Sum.inr j : Fin 3 ⊕ Fin 3)) (by intro i j h; simpa using h) (by simp)
  · exact cycle_seven_is_planar_K33_aux B hdisj hadj (Sum.inr b) x hx
      (fun j => (Sum.inl j : Fin 3 ⊕ Fin 3)) (by intro i j h; simpa using h) (by simp)

/-- The 7-cycle graph is planar. -/
theorem cycle_seven_is_planar : simple_graph_is_planar (SimpleGraph.cycleGraph 7) := ⟨cycle_seven_is_planar_not_K5, cycle_seven_is_planar_not_K33⟩
