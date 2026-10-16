import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# wild_number_complete_graph_min_proper_coloring_ge

Topic: graphs   Node: c93948043b0b

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Theorem 3.4. ⌈n/2⌉ is written (n + 1) / 2 in ℕ; a minimum proper colouring is a colouring of the line graph by Fin k with k = χ'(K_n) = chromatic number of the line graph.

Let n ≥ 3 and let ρ be a minimum proper edge colouring of K_n (a proper colouring with χ'(K_n) colours). Then wld_ρ(K_n) ≥ ⌊4⌈n/2⌉/3⌋.
-/

theorem wild_kn_mem {n : ℕ} {u v : Fin n} (h : u ≠ v) : s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := by
  simpa using h

theorem wild_kn_same_color {n k : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    {u v w : Fin n} (hv : u ≠ v) (hw : u ≠ w)
    (h : c ⟨s(u, v), wild_kn_mem hv⟩ = c ⟨s(u, w), wild_kn_mem hw⟩) : v = w := by
  by_contra hne
  apply c.valid _ h
  refine ⟨fun h' => hne ?_, ⟨u, by simp, by simp⟩⟩
  have := congrArg Subtype.val h'
  simp only [Sym2.eq_iff] at this
  rcases this with ⟨-, h1⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h2.trans h1

/-- In a graph where u and v have no neighbours outside {u, v}, everything reachable from u is u or v. -/
theorem wild_kn_closed_pair {V : Type*} (G : SimpleGraph V) (u v : V)
    (hu : ∀ x, G.Adj u x → x = v) (hv : ∀ x, G.Adj v x → x = u) {y : V} (hy : G.Reachable u y) :
    y = u ∨ y = v := by
  obtain ⟨p⟩ := hy
  have key : ∀ a b (p : G.Walk a b), (a = u ∨ a = v) → b = u ∨ b = v := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (hu _ h)
      · exact Or.inl (hv _ h)
  exact key _ _ p (Or.inl rfl)

theorem wild_kn_exists_missing_color_of_odd {n k : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) (u : Fin n) :
    ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet, ∀ x (hx : u ≠ x), c ⟨s(u, x), wild_kn_mem hx⟩ ≠ c e := by
  classical
  by_contra hno
  push_neg at hno
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let i0 := c ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), wild_kn_mem h01⟩
  let col : Fin n → Fin n → Fin k := fun v x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0
  have hcol : ∀ v x (h : v ≠ x), col v x = c ⟨s(v, x), wild_kn_mem h⟩ := fun v x h => dif_pos h
  let Cv : Fin n → Finset (Fin k) := fun v => (Finset.univ.erase v).image (col v)
  have hCv : ∀ v, (Cv v).card = n - 1 := by
    intro v
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    intro a ha b hb hab
    have ha' := Ne.symm (Finset.ne_of_mem_erase ha)
    have hb' := Ne.symm (Finset.ne_of_mem_erase hb)
    rw [hcol v a ha', hcol v b hb'] at hab
    exact wild_kn_same_color c ha' hb' hab
  -- every colour used anywhere is a colour at u, so every vertex sees all of them
  have hsub : ∀ v, Cv v ⊆ Cv u := by
    intro v j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hj
    have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
    obtain ⟨y, hy, hyc⟩ := hno ⟨s(v, x), wild_kn_mem hx'⟩
    refine Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨Ne.symm hy, Finset.mem_univ _⟩, ?_⟩
    rw [hcol u y hy, hcol v x hx']
    exact hyc
  have heq : ∀ v, Cv v = Cv u := fun v =>
    Finset.eq_of_subset_of_card_le (hsub v) (by rw [hCv, hCv])
  have hi0 : i0 ∈ Cv u := by
    rw [← heq ⟨0, by omega⟩]
    refine Finset.mem_image.2 ⟨⟨1, by omega⟩, Finset.mem_erase.2 ⟨Ne.symm h01, Finset.mem_univ _⟩, ?_⟩
    rw [hcol _ _ h01]
  have hall : ∀ v, ∃ x, ∃ hx : v ≠ x, c ⟨s(v, x), wild_kn_mem hx⟩ = i0 := by
    intro v
    rw [← heq v] at hi0
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 hi0
    have hx' := Ne.symm (Finset.ne_of_mem_erase hx)
    exact ⟨x, hx', by rw [← hcol v x hx']; exact hxc⟩
  choose partner hpne hpi using hall
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

theorem wild_number_complete_graph_min_proper_coloring_ge (n k : ℕ) (hn : 3 ≤ n)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    4 * ((n + 1) / 2) / 3 ≤ simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c := by
  classical
  -- the class of colour i together with W
  let G' : Finset (Sym2 (Fin n)) → Fin k → SimpleGraph (Fin n) := fun W i =>
    SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, c ⟨f, hf⟩ = i} ∪ ↑W)
  have hG'adj : ∀ W i x y, (G' W i).Adj x y ↔ x ≠ y ∧
      ((∃ h : x ≠ y, c ⟨s(x, y), wild_kn_mem h⟩ = i) ∨ s(x, y) ∈ W) := by
    intro W i x y
    simp only [G', SimpleGraph.fromEdgeSet_adj, Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨h | h, hxy⟩
      · exact ⟨hxy, Or.inl ⟨hxy, h.2⟩⟩
      · exact ⟨hxy, Or.inr h⟩
    · rintro ⟨hxy, ⟨h, hc⟩ | h⟩
      · exact ⟨Or.inl ⟨wild_kn_mem h, hc⟩, hxy⟩
      · exact ⟨Or.inr h, hxy⟩
  -- a third vertex always exists
  have third : ∀ u v : Fin n, ∃ w, w ≠ u ∧ w ≠ v := by
    intro u v
    by_contra h
    push_neg at h
    have : (Finset.univ : Finset (Fin n)) ⊆ {u, v} := fun w _ => by
      by_cases hw : w = u
      · simp [hw]
      · simp [h w hw]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := Finset.card_le_two (a := u) (b := v)
    omega
  have hlow : ∀ W : Finset (Sym2 (Fin n)),
      simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W →
        4 * ((n + 1) / 2) / 3 ≤ W.card := by
    intro W hW
    have conn : ∀ (u v : Fin n) (huv : u ≠ v), (G' W (c ⟨s(u, v), wild_kn_mem huv⟩)).Connected :=
      fun u v huv => hW.2 ⟨s(u, v), wild_kn_mem huv⟩
    -- (F) a closed pair contradicts connectivity
    have no_closed : ∀ (u v : Fin n) (huv : u ≠ v),
        (∀ x, (G' W (c ⟨s(u, v), wild_kn_mem huv⟩)).Adj u x → x = v) →
        (∀ x, (G' W (c ⟨s(u, v), wild_kn_mem huv⟩)).Adj v x → x = u) → False := by
      intro u v huv h1 h2
      obtain ⟨w, hwu, hwv⟩ := third u v
      rcases wild_kn_closed_pair _ u v h1 h2 ((conn u v huv).preconnected u w) with h | h
      · exact hwu h
      · exact hwv h
    let touched : Finset (Fin n) := Finset.univ.filter fun v => ∃ f ∈ W, v ∈ f
    -- (F1) at most one vertex is untouched
    have F1 : n - 1 ≤ touched.card := by
      have : (Finset.univ.filter fun v => v ∉ touched).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u hu v hv
        by_contra huv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, touched, not_exists,
          not_and] at hu hv
        apply no_closed u v huv
        · intro x hx
          rw [hG'adj] at hx
          obtain ⟨hux, ⟨h, hc⟩ | hw⟩ := hx
          · exact wild_kn_same_color c h huv hc
          · exact absurd (Sym2.mem_mk_left u x) (hu _ hw)
        · intro x hx
          rw [hG'adj] at hx
          obtain ⟨hvx, ⟨h, hc⟩ | hw⟩ := hx
          · have hc' : c ⟨s(v, x), wild_kn_mem h⟩ = c ⟨s(v, u), wild_kn_mem (Ne.symm huv)⟩ := by
              rw [hc]; congr 2; exact Sym2.eq_swap
            exact wild_kn_same_color c h (Ne.symm huv) hc'
          · exact absurd (Sym2.mem_mk_left v x) (hv _ hw)
      have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun v => v ∈ touched)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have htt : (Finset.univ.filter fun v => v ∈ touched) = touched := by
        ext v; simp
      rw [htt] at hsplit
      omega
    -- (F1') for odd n every vertex is touched
    have F1' : n % 2 = 1 → n ≤ touched.card := by
      intro hodd
      have : touched = Finset.univ := by
        rw [Finset.eq_univ_iff_forall]
        intro u
        by_contra hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, touched, not_exists,
          not_and] at hu
        obtain ⟨e, he⟩ := wild_kn_exists_missing_color_of_odd hn hodd c u
        obtain ⟨w, hwu, -⟩ := third u u
        obtain ⟨p⟩ := (hW.2 e).preconnected u w
        cases p with
        | nil => exact hwu rfl
        | cons h _ =>
          have h' : (G' W (c e)).Adj u _ := h
          rw [hG'adj] at h'
          obtain ⟨-, ⟨hx, hc⟩ | hw⟩ := h'
          · exact he _ hx hc
          · exact hu _ hw (Sym2.mem_mk_left _ _)
      rw [this, Finset.card_univ, Fintype.card_fin]
    -- degrees in W
    let d : Fin n → ℕ := fun v => (W.filter fun f => v ∈ f).card
    have hhand : ∑ v, d v = 2 * W.card := by
      simp only [d, Finset.card_filter]
      rw [Finset.sum_comm]
      rw [mul_comm, Finset.card_eq_sum_ones, Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfE : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := hW.1 (Finset.mem_coe.2 hf)
      induction f using Sym2.ind with
      | h a b =>
        have hab : a ≠ b := by simpa using hfE
        rw [← Finset.card_filter, one_mul]
        have : (Finset.univ.filter fun v => v ∈ s(a, b)) = {a, b} := by
          ext v; simp
        rw [this, Finset.card_pair hab]
    -- a leaf's edge is shared with no other leaf
    let L : Finset (Fin n) := Finset.univ.filter fun v => d v = 1
    let Bg : Finset (Fin n) := Finset.univ.filter fun v => 2 ≤ d v
    have htouch : touched = L ∪ Bg := by
      ext v
      simp only [touched, L, Bg, d, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨f, hf, hvf⟩
        have : 1 ≤ (W.filter fun f => v ∈ f).card :=
          Finset.card_pos.2 ⟨f, Finset.mem_filter.2 ⟨hf, hvf⟩⟩
        omega
      · intro h
        have : 0 < (W.filter fun f => v ∈ f).card := by omega
        obtain ⟨f, hf⟩ := Finset.card_pos.1 this
        exact ⟨f, (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2⟩
    have hdisj : Disjoint L Bg := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      simp only [L, Bg, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
      omega
    have hdeg : L.card + 2 * Bg.card ≤ ∑ v, d v := by
      calc L.card + 2 * Bg.card = ∑ v ∈ L, 1 + ∑ v ∈ Bg, 2 := by simp [mul_comm]
        _ ≤ ∑ v ∈ L, d v + ∑ v ∈ Bg, d v := by
          gcongr with v hv v hv
          · simp only [L, Finset.mem_filter] at hv; omega
          · simp only [Bg, Finset.mem_filter] at hv; omega
        _ = ∑ v ∈ L ∪ Bg, d v := (Finset.sum_union hdisj).symm
        _ ≤ ∑ v, d v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hleaf : ∀ v ∈ L, ∃ f, W.filter (fun f => v ∈ f) = {f} := by
      intro v hv
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, d] at hv
      exact Finset.card_eq_one.1 hv
    haveI : Nonempty (Sym2 (Fin n)) := ⟨s(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    choose! ef hef using hleaf
    have hLW : L.card ≤ W.card := by
      refine Finset.card_le_card_of_injOn ef (fun v hv => ?_) (fun u hu v hv huv => ?_)
      · have := (Finset.mem_filter.1 ((hef v hv).symm ▸ Finset.mem_singleton_self (ef v))).1
        exact this
      · by_contra hne
        have hu' := (Finset.mem_filter.1 ((hef u hu).symm ▸ Finset.mem_singleton_self (ef u)))
        have hv' := (Finset.mem_filter.1 ((hef v hv).symm ▸ Finset.mem_singleton_self (ef v)))
        -- ef u = s(u, v)
        have huvf : ef u = s(u, v) := by
          have h1 : u ∈ ef u := hu'.2
          have h2 : v ∈ ef u := huv ▸ hv'.2
          have hE : ef u ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := hW.1 (Finset.mem_coe.2 hu'.1)
          revert h1 h2 hE
          induction ef u using Sym2.ind with
          | h a b =>
            intro h1 h2 hE
            have hab : a ≠ b := by simpa using hE
            simp only [Sym2.mem_iff] at h1 h2
            rw [Sym2.eq_iff]
            rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
            · exact absurd rfl hne
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
            · exact absurd rfl hne
        have only : ∀ w, w ∈ L → ∀ f ∈ W, w ∈ f → f = ef w := by
          intro w hw f hf hwf
          have : f ∈ W.filter (fun f => w ∈ f) := Finset.mem_filter.2 ⟨hf, hwf⟩
          rw [hef w hw] at this
          exact Finset.mem_singleton.1 this
        apply no_closed u v hne
        · intro x hx
          rw [hG'adj] at hx
          obtain ⟨hux, ⟨h, hc⟩ | hw⟩ := hx
          · exact wild_kn_same_color c h hne hc
          · have := only u hu _ hw (Sym2.mem_mk_left u x)
            rw [huvf, Sym2.eq_iff] at this
            rcases this with ⟨-, h⟩ | ⟨h1, -⟩
            · exact h
            · exact absurd h1 hne
        · intro x hx
          rw [hG'adj] at hx
          obtain ⟨hvx, ⟨h, hc⟩ | hw⟩ := hx
          · have hc' : c ⟨s(v, x), wild_kn_mem h⟩ = c ⟨s(v, u), wild_kn_mem (Ne.symm hne)⟩ := by
              rw [hc]; congr 2; exact Sym2.eq_swap
            exact wild_kn_same_color c h (Ne.symm hne) hc'
          · have := only v hv _ hw (Sym2.mem_mk_left v x)
            rw [← huv, huvf, Sym2.eq_iff] at this
            rcases this with ⟨h1, -⟩ | ⟨-, h⟩
            · exact absurd h1.symm hne
            · exact h
    have htc : touched.card = L.card + Bg.card := by
      rw [htouch, Finset.card_union_of_disjoint hdisj]
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · omega
    · have := F1' h1
      omega
  -- the edge set of K_n is colour-connecting, so the infimum is over a nonempty set
  have hne : (Finset.univ.filter fun f : Sym2 (Fin n) => f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet).card ∈
      {k | ∃ W : Finset (Sym2 (Fin n)), W.card = k ∧
        simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W} := by
    refine ⟨_, rfl, ?_, fun e => ?_⟩
    · intro f hf; simpa using hf
    · haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      refine SimpleGraph.connected_top.mono ?_
      intro a b hab
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨Or.inr (by simpa using hab), hab⟩
  exact le_csInf ⟨_, hne⟩ fun j ⟨W, hj, hW⟩ => by rw [← hj]; exact hlow W hW
