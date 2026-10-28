import AFTD.Prelude
import AFTD.Kb.Tcs.WildPartitionOfResourceBounds
import AFTD.Kb.Tcs.WildPartitionLargeOrderResourceBounds
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition

/-!
# wild_number_complete_graph_large_eq

Topic: graphs   Node: 1dc7548594fa

Provenance: original. Related work: arXiv:2610.22142, Section 6 conjecture, Theorem 3.4 lower bound, Theorem 3.5 equality for 3<=n<=12, and Section 3.3.3 odd-to-even restriction lemma. Prior AFTD n=279 and the uniform n=3 mod 6 result are the baselines here. Literature checked 2026-10-28 at https://arxiv.org/abs/2610.22142 and searches for the title and sufficiently large wild-number sharpness. No later universal sharpness result was found. The threshold is sufficient and is not claimed optimal.

For every integer n>=30000001, every natural number k equal to the chromatic number of the line graph of K_n, and every proper edge coloring c of K_n with color set Fin k, the wild number of c equals floor(4*ceil(n/2)/3). Thus the minimum-proper-coloring conjecture holds for every complete graph of order at least 30000001.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem wsc_missing_vertex_equiv_of_le (n k : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (hkn : k ≤ n) (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) : ∃ m : Fin k ≃ Fin n, ∀ (i : Fin k) (v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), by simpa using hvw⟩ ≠ i) ↔ v = m i := by
  classical
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let i0 := c ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), wild_kn_mem h01⟩
  let col : Fin n → Fin n → Fin k := fun v x => if h : v ≠ x then c ⟨s(v, x), wild_kn_mem h⟩ else i0
  have hcol : ∀ v x (h : v ≠ x), col v x = c ⟨s(v, x), wild_kn_mem h⟩ := fun v x h => dif_pos h
  let Cv : Fin n → Finset (Fin k) := fun v => (Finset.univ.erase v).image (col v)
  have hCv : ∀ v, (Cv v).card = n - 1 := fun v => w279_color_card_at c v i0
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
    obtain ⟨v, hv⟩ := w279_color_missed_of_odd hodd c i
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


lemma wsc_last_ne_cast {n : ℕ} (v : Fin n) : Fin.last n ≠ v.castSucc := by
  intro h
  have he := congrArg Fin.val h
  have hv := v.isLt
  simp only [Fin.val_last, Fin.val_castSucc] at he
  omega

noncomputable def wsc_extend_pair {n : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (m : Fin n ≃ Fin n) (i0 : Fin n) : Option (Fin n) → Option (Fin n) → Fin n
  | none, none => i0
  | none, some v => m.symm v
  | some v, none => m.symm v
  | some v, some w => if h : v ≠ w then c ⟨s(v,w), wild_kn_mem h⟩ else i0

lemma wsc_extend_pair_symm {n : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (m : Fin n ≃ Fin n) (i0 : Fin n) (a b : Option (Fin n)) :
    wsc_extend_pair c m i0 a b = wsc_extend_pair c m i0 b a := by
  cases a with
  | none => cases b <;> rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      by_cases h : a ≠ b
      · simp only [wsc_extend_pair, dif_pos h, dif_pos (Ne.symm h)]
        exact w279_c_swap c h
      · have hab : a = b := not_ne_iff.mp h
        subst b
        simp [wsc_extend_pair]

lemma wsc_extend_pair_row {n : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n))
    (m : Fin n ≃ Fin n) (i0 : Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
    (v a b : Option (Fin n)) (hva : v ≠ a) (hvb : v ≠ b)
    (hc : wsc_extend_pair c m i0 v a = wsc_extend_pair c m i0 v b) : a = b := by
  cases v with
  | none =>
    cases a with
    | none => exact (hva rfl).elim
    | some a =>
      cases b with
      | none => exact (hvb rfl).elim
      | some b =>
        exact congrArg some (m.symm.injective hc)
  | some v =>
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have hvb' : v ≠ b := by simpa using hvb
        have hmiss := (hm (m.symm v) v).2 (by simp)
        simp only [wsc_extend_pair, dif_pos hvb'] at hc
        exact (hmiss b hvb' hc.symm).elim
    | some a =>
      have hva' : v ≠ a := by simpa using hva
      cases b with
      | none =>
        have hmiss := (hm (m.symm v) v).2 (by simp)
        simp only [wsc_extend_pair, dif_pos hva'] at hc
        exact (hmiss a hva' hc).elim
      | some b =>
        have hvb' : v ≠ b := by simpa using hvb
        simp only [wsc_extend_pair, dif_pos hva', dif_pos hvb'] at hc
        exact congrArg some (wild_kn_same_color c hva' hvb' hc)

lemma wsc_even_colorable (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Colorable n := by
  obtain ⟨c⟩ := w279_colorable n hn
  obtain ⟨m, hm⟩ := wsc_missing_vertex_equiv_of_le n n hn hodd le_rfl c
  let i0 : Fin n := ⟨0, by omega⟩
  let col : Sym2 (Option (Fin n)) → Fin n := Sym2.lift
    ⟨wsc_extend_pair c m i0, wsc_extend_pair_symm c m i0⟩
  have hc : (⊤ : SimpleGraph (Option (Fin n))).lineGraph.Colorable n := by
    refine ⟨SimpleGraph.Coloring.mk (fun e => col e.val) ?_⟩
    intro e₁ e₂ h hcol
    rw [SimpleGraph.lineGraph_adj_iff_exists] at h
    obtain ⟨hne, v, h1, h2⟩ := h
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp h1
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp h2
    have hva : v ≠ a := by have hh := e₁.property; rw [ha] at hh; simpa using hh
    have hvb : v ≠ b := by have hh := e₂.property; rw [hb] at hh; simpa using hh
    have hpair : wsc_extend_pair c m i0 v a = wsc_extend_pair c m i0 v b := by
      simpa only [col, ha, hb, Sym2.lift_mk] using hcol
    have hab := wsc_extend_pair_row c m i0 hm v a b hva hvb hpair
    apply hne
    apply Subtype.ext
    rw [ha, hb, hab]
  obtain ⟨cc⟩ := hc
  exact ⟨cc.comap (SimpleGraph.Iso.completeGraph (finSuccEquivLast (n := n))).lineGraph.toHom⟩

lemma wsc_even_min_colors {n k : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hk : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin k)) : k = n := by
  have hup : k ≤ n := by
    have hi := (wsc_even_colorable n hn hodd).chromaticNumber_le
    rw [hk] at hi
    exact_mod_cast hi
  have hkpos : 0 < k := by
    have hi := c ⟨s(⟨0, by omega⟩,⟨1, by omega⟩), wild_kn_mem (by simp [Fin.ext_iff])⟩
    have h := hi.isLt
    omega
  have hcard := w279_color_card_at c (Fin.last n) ⟨0, hkpos⟩
  have hlo := Finset.card_le_univ
    ((Finset.univ.erase (Fin.last n)).image (fun x => if h : Fin.last n ≠ x then c ⟨s(Fin.last n,x), wild_kn_mem h⟩ else ⟨0,hkpos⟩))
  rw [hcard, Fintype.card_fin] at hlo
  omega

noncomputable def wsc_restrict_color {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin k)) :
    (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k) :=
  c.comap (SimpleGraph.Embedding.completeGraph (⟨Fin.castSucc, Fin.castSucc_injective n⟩ : Fin n ↪ Fin (n+1))).toCopy.toLineGraphEmbedding.toHom

lemma wsc_restrict_pair {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin k))
    (u v : Fin n) (huv : u ≠ v) :
    wsc_restrict_color c ⟨s(u,v), wild_kn_mem huv⟩ =
      c ⟨s(u.castSucc,v.castSucc), wild_kn_mem (by simpa using huv)⟩ := rfl

lemma wsc_color_at_last {n : ℕ}
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin n)) (i : Fin n) :
    ∃ v : Fin n, c ⟨s(Fin.last n,v.castSucc), wild_kn_mem (wsc_last_ne_cast _)⟩ = i := by
  let f : Fin n → Fin n := fun v => c ⟨s(Fin.last n,v.castSucc), wild_kn_mem (wsc_last_ne_cast _)⟩
  have hi : Function.Injective f := by
    intro u v huv
    exact Fin.castSucc_injective n (wild_kn_same_color c (wsc_last_ne_cast _) (wsc_last_ne_cast _) huv)
  exact Finite.surjective_of_injective hi i

lemma wsc_color_used {n : ℕ} (hn : 3 ≤ n)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v,w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
    (i : Fin n) : ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet, c e = i := by
  let v : Fin n := if (m i).val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hv : v ≠ m i := by dsimp only [v]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  obtain ⟨h, hh⟩ := w279_pc_spec c m hm i v hv
  exact ⟨⟨s(v,w279_pc c i v), wild_kn_mem h⟩, hh⟩

lemma wsc_even_upper_of_partition {n q : ℕ} (hn : 0 < n)
    (c : (⊤ : SimpleGraph (Fin (n+1))).lineGraph.Coloring (Fin n))
    (p : Fin n → Fin q) (roots : Fin q → Fin n) (hroot : ∀ t, p (roots t) = t)
    (hcut : ∀ (i : Fin n) (S : Finset (Fin q)), S.Nonempty → S ≠ Finset.univ →
      ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧
        wsc_restrict_color c ⟨s(u,v), wild_kn_mem huv⟩ = i) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin (n+1))) c ≤ n-q := by
  classical
  let pp : Fin (n+1) → Fin (q+1) := Fin.lastCases (Fin.last q) (fun v => (p v).castSucc)
  let rr : Fin (q+1) → Fin (n+1) := Fin.lastCases (Fin.last n) (fun t => (roots t).castSucc)
  have hpp : ∀ t, pp (rr t) = t := by
    intro t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp [pp,rr]
    · simp [pp,rr,hroot]
  have hu := simple_graph_wild_number_le_of_block_cut_condition (n := n+1) (q := q+1) (by omega) c pp rr hpp ?_
  · simpa only [Nat.add_sub_add_right] using hu
  · intro e S hS hSu
    let T : Finset (Fin q) := Finset.univ.filter fun t => t.castSucc ∈ S
    have hTmem : ∀ t : Fin q, t ∈ T ↔ t.castSucc ∈ S := by simp [T]
    by_cases hT0 : T = ∅
    · have hlast : Fin.last q ∈ S := by
        obtain ⟨s, hs⟩ := hS
        revert hs
        refine Fin.lastCases ?_ (fun t => ?_) s
        · exact id
        · intro ht
          have : t ∈ T := (hTmem t).2 ht
          simpa [hT0] using this
      obtain ⟨v, hv⟩ := wsc_color_at_last c (c e)
      refine ⟨Fin.last n, v.castSucc, wsc_last_ne_cast v, ?_, ?_, hv⟩
      · simpa [pp] using hlast
      · simp only [pp, Fin.lastCases_castSucc]
        intro hmem
        have : p v ∈ T := (hTmem _).2 hmem
        simpa [hT0] using this
    · by_cases hTu : T = Finset.univ
      · have hlast : Fin.last q ∉ S := by
          intro hs
          apply hSu
          apply Finset.eq_univ_of_forall
          intro s
          refine Fin.lastCases hs (fun t => ?_) s
          exact (hTmem t).1 (by simp [hTu])
        obtain ⟨v, hv⟩ := wsc_color_at_last c (c e)
        refine ⟨v.castSucc, Fin.last n, by simp, ?_, ?_, ?_⟩
        · simp only [pp, Fin.lastCases_castSucc]
          exact (hTmem _).1 (by simp [hTu])
        · simpa [pp] using hlast
        · exact (w279_c_swap c (wsc_last_ne_cast v)).symm.trans hv
      · obtain ⟨u, v, huv, hu, hv, hc⟩ := hcut (c e) T (Finset.nonempty_iff_ne_empty.2 hT0) hTu
        refine ⟨u.castSucc, v.castSucc, by simpa using huv, ?_, ?_, ?_⟩
        · simp only [pp, Fin.lastCases_castSucc]
          exact (hTmem _).1 hu
        · simp only [pp, Fin.lastCases_castSucc]
          exact fun h => hv ((hTmem _).2 h)
        · exact hc
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

lemma wsc_upper_sized (q : ℕ) (a : Fin 3) (hq : 10000000 ≤ q) (hodd : (3*q+a.val) % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin (3*q+a.val))).lineGraph.Coloring (Fin (3*q+a.val)))
    (m : Fin (3*q+a.val) ≃ Fin (3*q+a.val))
    (hm : ∀ (i v : Fin (3*q+a.val)), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin (3*q+a.val))) c ≤ 2*q+a.val := by
  have hq3 : 3 ≤ q := by omega
  let b := wsc_blk hq3 a
  let r := wsc_root hq3 a
  have hr : ∀ t, b (r t) = t := wsc_root_blk hq3 a
  have hb : ∀ T : Finset (Fin q), 3*T.card ≤ (wsc_pos b T).card ∧
      (wsc_pos b T).card ≤ 3*T.card+((3*q+a.val)-3*q) := by
    intro T
    simpa only [Nat.add_sub_cancel_left] using wsc_card_pos_bounds hq3 a T
  have hp := wsc_pos_mass hq hodd (by omega) (by have := a.isLt; omega) b hb c m hm
  have hv := wsc_vert_mass hq hodd (by omega) (by have := a.isLt; omega) b hb c m hm
  have hu := wsc_upper c (by omega) b r hr hp hv
  have he : 3*q+a.val-q = 2*q+a.val := by omega
  simpa only [he] using hu

theorem wild_number_complete_graph_large_odd_eq (n k : ℕ) (hn : 30000000 ≤ n) (hodd : n % 2 = 1)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4*((n+1)/2)/3 := by
  obtain ⟨q, a, rfl⟩ : ∃ (q : ℕ) (a : Fin 3), n = 3*q+a.val := by
    exact ⟨n/3, ⟨n%3, Nat.mod_lt n (by omega)⟩, by change n = 3*(n/3)+n%3; omega⟩
  have hq : 10000000 ≤ q := by have := a.isLt; omega
  obtain ⟨m, hm⟩ := w279_missing_vertex_equiv (3*q+a.val) k (by omega) hodd hk c
  have hk' : k = 3*q+a.val := by simpa using Fintype.card_congr m
  subst k
  have hu := wsc_upper_sized q a hq hodd c m hm
  have hl := wild_number_complete_graph_min_proper_coloring_ge (3*q+a.val) (3*q+a.val) (by omega) hk c
  have he : 4*((3*q+a.val+1)/2)/3 = 2*q+a.val := by have := a.isLt; omega
  rw [he] at hl ⊢
  exact le_antisymm hu hl

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

lemma wsc_sized_partition (q : ℕ) (a : Fin 3) (hq : 10000000 ≤ q) (hodd : (3*q+a.val) % 2 = 1)
    (c : (⊤ : SimpleGraph (Fin (3*q+a.val))).lineGraph.Coloring (Fin (3*q+a.val)))
    (m : Fin (3*q+a.val) ≃ Fin (3*q+a.val))
    (hm : ∀ (i v : Fin (3*q+a.val)), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ (p : Fin (3*q+a.val) → Fin q) (roots : Fin q → Fin (3*q+a.val)), (∀ t, p (roots t) = t) ∧
      ∀ (e : (⊤ : SimpleGraph (Fin (3*q+a.val))).edgeSet) (S : Finset (Fin q)), S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin (3*q+a.val)) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v), wild_kn_mem huv⟩ = c e := by
  have hq3 : 3 ≤ q := by omega
  let b := wsc_blk hq3 a
  let r := wsc_root hq3 a
  have hr : ∀ t, b (r t) = t := wsc_root_blk hq3 a
  have hb : ∀ T : Finset (Fin q), 3*T.card ≤ (wsc_pos b T).card ∧
      (wsc_pos b T).card ≤ 3*T.card+((3*q+a.val)-3*q) := by
    intro T
    simpa only [Nat.add_sub_cancel_left] using wsc_card_pos_bounds hq3 a T
  have hp := wsc_pos_mass hq hodd (by omega) (by have := a.isLt; omega) b hb c m hm
  have hv := wsc_vert_mass hq hodd (by omega) (by have := a.isLt; omega) b hb c m hm
  exact wild_partition_of_resource_bounds c (by omega) b r hr hp hv

theorem wild_number_complete_graph_large_eq (n k : ℕ) (hn : 30000001 ≤ n)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4*((n+1)/2)/3 := by
  by_cases hodd : n % 2 = 1
  · exact wild_number_complete_graph_large_odd_eq n k (by omega) hodd hk c
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm3 : 3 ≤ m := by omega
  have hmOdd : m % 2 = 1 := by omega
  have hk' : k = m := wsc_even_min_colors hm3 hmOdd hk c
  subst k
  obtain ⟨q, a, rfl⟩ : ∃ (q : ℕ) (a : Fin 3), m = 3*q+a.val := by
    exact ⟨m/3, ⟨m%3, Nat.mod_lt m (by omega)⟩, by change m = 3*(m/3)+m%3; omega⟩
  have hq : 10000000 ≤ q := by have := a.isLt; omega
  let cc := wsc_restrict_color c
  obtain ⟨miss, hmiss⟩ := wsc_missing_vertex_equiv_of_le (3*q+a.val) (3*q+a.val) hm3 hmOdd le_rfl cc
  obtain ⟨p, roots, hroots, hcuts⟩ := wsc_sized_partition q a hq hmOdd cc miss hmiss
  have hcut : ∀ (i : Fin (3*q+a.val)) (S : Finset (Fin q)), S.Nonempty → S ≠ Finset.univ →
      ∃ (u v : Fin (3*q+a.val)) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ cc ⟨s(u,v), wild_kn_mem huv⟩ = i := by
    intro i S hS hSu
    obtain ⟨e, he⟩ := wsc_color_used hm3 cc miss hmiss i
    obtain ⟨u, v, huv, hu, hv, hc⟩ := hcuts e S hS hSu
    exact ⟨u, v, huv, hu, hv, hc.trans he⟩
  have hu := wsc_even_upper_of_partition (by omega) c p roots hroots hcut
  have hl := wild_number_complete_graph_min_proper_coloring_ge (3*q+a.val+1) (3*q+a.val) (by omega) hk c
  have he : 3*q+a.val-q = 4*((3*q+a.val+1+1)/2)/3 := by have := a.isLt; omega
  rw [he] at hu
  exact le_antisymm hu hl
