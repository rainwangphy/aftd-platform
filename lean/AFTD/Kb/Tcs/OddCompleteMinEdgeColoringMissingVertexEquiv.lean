import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.CompleteGraphLineGraphColorable

/-!
# odd_complete_min_edge_coloring_missing_vertex_equiv

Topic: graphs   Node: 39e93dd8ca35

Provenance: helper lemma. Matching normalization used in arXiv:2610.22142, Section 3, and needed for the proposed OP-306 n=279 canonical seal-event count.

In a minimum proper coloring of an odd complete graph, every color misses exactly one vertex, and these missing vertices give a bijection from colors to vertices.
-/

theorem wild_kn_color_card_at {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (v : Fin n) (i0 : Fin k) :
    ((Finset.univ.erase v).image
      (fun x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0)).card = n - 1 := by
  rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  intro a ha b hb hab
  have ha' := Ne.symm (Finset.ne_of_mem_erase ha)
  have hb' := Ne.symm (Finset.ne_of_mem_erase hb)
  simp only [dif_pos ha', dif_pos hb'] at hab
  exact wild_kn_same_color c ha' hb' hab

/-- No colour class is a perfect matching of an odd complete graph. -/
theorem wild_kn_color_missed_of_odd {n k : ℕ} (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (i0 : Fin k) :
    ∃ v : Fin n, ∀ x (hx : v ≠ x), c ⟨s(v, x), wild_kn_mem hx⟩ ≠ i0 := by
  classical
  by_contra hno
  simp only [not_exists, not_forall, not_not] at hno
  choose partner hpne hpi using hno
  have hpp : ∀ v, partner (partner v) = v := by
    intro v
    have h1 := hpi (partner v)
    have h2 := hpi v
    have h2' : c ⟨s(partner v, v), wild_kn_mem (Ne.symm (hpne v))⟩ = i0 := by
      rw [← h2]; congr 2; exact Sym2.eq_swap
    exact wild_kn_same_color c (hpne (partner v)) (Ne.symm (hpne v)) (h1.trans h2'.symm)
  let e : Fin n → Sym2 (Fin n) := fun v => s(v, partner v)
  have hfib : ∀ v, (Finset.univ.filter fun w => e w = e v) = {v, partner v} := by
    intro v
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, e, Sym2.eq_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, hpp v⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (f := e) (s := Finset.univ)
    (t := Finset.univ.image e) (fun x _ => Finset.mem_image_of_mem e (Finset.mem_univ x))
  have h2 : ∀ b ∈ Finset.univ.image e, (Finset.univ.filter fun a => e a = b).card = 2 := by
    intro b hb
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hfib v, Finset.card_pair (hpne v)]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hsum
  omega

theorem odd_complete_min_edge_coloring_missing_vertex_equiv (n k : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k) (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) : ∃ m : Fin k ≃ Fin n, ∀ (i : Fin k) (v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), by simpa using hvw⟩ ≠ i) ↔ v = m i := by
  classical
  have hkn : k ≤ n := by
    have := (complete_graph_line_graph_colorable n hn).chromaticNumber_le
    rw [hk] at this
    exact_mod_cast this
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let i0 := c ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), wild_kn_mem h01⟩
  let col : Fin n → Fin n → Fin k := fun v x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0
  have hcol : ∀ v x (h : v ≠ x), col v x = c ⟨s(v, x), wild_kn_mem h⟩ := fun v x h => dif_pos h
  let Cv : Fin n → Finset (Fin k) := fun v => (Finset.univ.erase v).image (col v)
  have hCv : ∀ v, (Cv v).card = n - 1 := fun v => wild_kn_color_card_at c v i0
  -- a missed colour at each vertex
  have hmiss : ∀ v, ∃ i, i ∉ Cv v := by
    intro v
    obtain ⟨e, he⟩ := wild_kn_exists_missing_color_of_odd hn hodd c v
    refine ⟨c e, fun h => ?_⟩
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 h
    have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
    rw [hcol v x hx'] at hxc
    exact he x hx' hxc
  have hkn' : n ≤ k := by
    obtain ⟨i, hi⟩ := hmiss ⟨0, by omega⟩
    have : Cv ⟨0, by omega⟩ ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.2
      ⟨Finset.subset_univ _, fun h => hi (h ▸ Finset.mem_univ i)⟩
    have := Finset.card_lt_card this
    rw [hCv, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hk' : k = n := le_antisymm hkn hkn'
  subst hk'
  -- exactly one missed colour at each vertex
  have huniq : ∀ v i j, i ∉ Cv v → j ∉ Cv v → i = j := by
    intro v i j hi hj
    by_contra hij
    have hsub : Cv v ⊆ (Finset.univ.erase i).erase j := by
      intro x hx
      refine Finset.mem_erase.2 ⟨fun h => hj (h ▸ hx), Finset.mem_erase.2 ⟨fun h => hi (h ▸ hx), Finset.mem_univ _⟩⟩
    have := Finset.card_le_card hsub
    rw [hCv, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  choose miss hmissv using hmiss
  have hmissing : ∀ (i : Fin k) (v : Fin k), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ i ∉ Cv v := by
    intro i v
    constructor
    · intro h hi
      obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 hi
      have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
      rw [hcol v x hx'] at hxc
      exact h x hx' hxc
    · intro h w hvw hc
      exact h (Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨Ne.symm hvw, Finset.mem_univ _⟩,
        by rw [hcol v w hvw, hc]⟩)
  have hsurj : Function.Surjective miss := by
    intro i
    obtain ⟨v, hv⟩ := wild_kn_color_missed_of_odd hodd c i
    exact ⟨v, huniq v _ _ (hmissv v) ((hmissing i v).1 hv)⟩
  have hbij : Function.Bijective miss := (Finite.injective_iff_surjective.2 hsurj) |> fun h => ⟨h, hsurj⟩
  let E := Equiv.ofBijective miss hbij
  refine ⟨E.symm, fun i v => ?_⟩
  rw [hmissing i v, Equiv.eq_symm_apply]
  constructor
  · intro h
    exact huniq v _ _ (hmissv v) h
  · intro h
    rw [← h]
    exact hmissv v
