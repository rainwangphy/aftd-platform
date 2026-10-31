import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimalTernaryLineCover
import AFTD.Kb.Tcs.TernaryAffineHyperplane
import AFTD.Kb.Tcs.LatinHypercubeIsAffine
import AFTD.Kb.Tcs.Zmod3PermIsAffine
import AFTD.Kb.Tcs.NowhereZeroAffineIsConstant
import AFTD.Kb.Tcs.IsTernaryLineCover

/-!
# ternary_minimal_line_cover_minimum_card_eq_hyperplane

Topic: combinatorics   Node: 96f23ed2e3e6

Provenance: helper lemma. step towards op_668_ternary_line_cover_first_gap_and_repair

For every natural number n ≥ 1 and every inclusion-minimal ternary line cover B in (Fin n → ZMod 3) with cardinality 3^(n - 1), B is an affine hyperplane for some normal vector a with all coordinates nonzero and some scalar b.
-/

open Classical in
theorem ternary_minimal_line_cover_minimum_card_eq_hyperplane_proj_inj (m : ℕ) (B : Finset (Fin (m + 1) → ZMod 3))
    (hcover : is_ternary_line_cover (m + 1) B) (hcard : B.card = 3 ^ m) (i : Fin (m + 1)) :
    Set.InjOn (fun (v : Fin (m+1) → ZMod 3) (k : Fin m) => v (Fin.succAbove i k)) (↑B) := by
  set πi : (Fin (m + 1) → ZMod 3) → (Fin m → ZMod 3) := fun v k => v (Fin.succAbove i k) with hπi
  have hsurj : ∀ d : Fin m → ZMod 3, ∃ v ∈ B, πi v = d := by
    intro d
    obtain ⟨t, ht⟩ := hcover i (Fin.insertNth (α := fun _ => ZMod 3) i 0 d)
    refine ⟨Function.update (Fin.insertNth (α := fun _ => ZMod 3) i 0 d) i t, ht, ?_⟩
    funext k
    rw [hπi]; simp only
    rw [Function.update_of_ne (Fin.succAbove_ne i k), Fin.insertNth_apply_succAbove]
  have himage : Finset.image πi B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro d
    obtain ⟨v, hv, hvd⟩ := hsurj d
    exact Finset.mem_image.mpr ⟨v, hv, hvd⟩
  have hcardimg : (Finset.image πi B).card = B.card := by rw [himage, hcard]; simp
  exact Finset.injOn_of_card_image_eq hcardimg

open Classical in
theorem ternary_minimal_line_cover_minimum_card_eq_hyperplane_line_unique (m : ℕ) (B : Finset (Fin (m + 1) → ZMod 3))
    (hcover : is_ternary_line_cover (m + 1) B) (hcard : B.card = 3 ^ m) :
    ∀ (i : Fin (m+1)) (c : Fin (m+1) → ZMod 3) (t t' : ZMod 3),
      Function.update c i t ∈ B → Function.update c i t' ∈ B → t = t' := by
  intro i c t t' ht ht'
  have hinj := ternary_minimal_line_cover_minimum_card_eq_hyperplane_proj_inj m B hcover hcard i
  have hkey : Function.update c i t = Function.update c i t' := by
    apply hinj ht ht'
    funext k
    simp only [Function.update_of_ne (Fin.succAbove_ne i k)]
  have : Function.update c i t i = Function.update c i t' i := by rw [hkey]
  simpa using this

open Classical in
theorem ternary_minimal_line_cover_minimum_card_eq_hyperplane_succ (m : ℕ) (B : Finset (Fin (m+1) → ZMod 3))
    (hcover : is_ternary_line_cover (m+1) B) (hcard : B.card = 3^m) :
    ∃ (A : Fin (m+1) → ZMod 3) (_hA : ∀ i, A i ≠ 0) (b : ZMod 3),
      B = ternary_affine_hyperplane (m+1) A b := by
  have hsm := ternary_minimal_line_cover_minimum_card_eq_hyperplane_line_unique m B hcover hcard
  set f : (Fin m → ZMod 3) → ZMod 3 := fun d => (hcover 0 (Fin.insertNth (α := fun _ => ZMod 3) 0 0 d)).choose with hf_def
  have hf_mem : ∀ d, Fin.insertNth (α := fun _ => ZMod 3) 0 (f d) d ∈ B := by
    intro d
    have h := (hcover 0 (Fin.insertNth (α := fun _ => ZMod 3) 0 0 d)).choose_spec
    rw [Fin.update_insertNth] at h
    exact h
  have hgraph : ∀ x ∈ B, x = Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Fin.tail x)) (Fin.tail x) := by
    intro x hx
    have hx' : Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Fin.tail x)) (Fin.tail x) ∈ B := hf_mem _
    have hinj0 := ternary_minimal_line_cover_minimum_card_eq_hyperplane_proj_inj m B hcover hcard (0 : Fin (m+1))
    apply hinj0 hx hx'
    funext k
    change x (Fin.succAbove 0 k) = Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Fin.tail x)) (Fin.tail x) (Fin.succAbove 0 k)
    rw [Fin.insertNth_apply_succAbove]
    rfl
  have hLatin_inj : ∀ (j : Fin m) (d : Fin m → ZMod 3), Function.Injective (fun t => f (Function.update d j t)) := by
    intro j d t t' htt'
    have hx : Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t) ∈ B := hf_mem _
    have hx' : Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t')) (Function.update d j t') ∈ B := hf_mem _
    let c : Fin (m+1) → ZMod 3 := Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t)) (Fin.succ j) 0
    have hxs : (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t)) (Fin.succ j) = t := by
      rw [Fin.insertNth_zero', Fin.cons_succ]; rw [Function.update_apply]; simp
    have hxs' : (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t')) (Function.update d j t')) (Fin.succ j) = t' := by
      rw [Fin.insertNth_zero', Fin.cons_succ]; rw [Function.update_apply]; simp
    have hbase : Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t)) (Fin.succ j) 0
               = Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t')) (Function.update d j t')) (Fin.succ j) 0 := by
      funext a
      obtain (rfl | ⟨k, rfl⟩) := Fin.eq_zero_or_eq_succ a
      · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)), Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
        rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]; exact htt'
      · rw [Function.update_apply, Function.update_apply]
        by_cases hk : k = j
        · subst hk; simp
        · rw [if_neg (by simp [hk]), if_neg (by simp [hk])]
          rw [Fin.insertNth_zero', Fin.cons_succ, Fin.insertNth_zero', Fin.cons_succ]
          rw [Function.update_of_ne hk, Function.update_of_ne hk]
    have hc : c = Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t)) (Fin.succ j) 0 := rfl
    have hxc : Function.update c (Fin.succ j) t = Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t)) (Function.update d j t) := by
      rw [hc, Function.update_idem]; exact Function.update_eq_self_iff.mpr hxs.symm
    have hxc' : Function.update c (Fin.succ j) t' = Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Function.update d j t')) (Function.update d j t') := by
      rw [hc, hbase, Function.update_idem]; exact Function.update_eq_self_iff.mpr hxs'.symm
    have hm1 : Function.update c (Fin.succ j) t ∈ B := hxc ▸ hx
    have hm2 : Function.update c (Fin.succ j) t' ∈ B := hxc' ▸ hx'
    exact hsm (Fin.succ j) c t t' hm1 hm2
  have hLatin_surj : ∀ (j : Fin m) (d : Fin m → ZMod 3), Function.Surjective (fun t => f (Function.update d j t)) := by
    intro j d s
    obtain ⟨t0, ht0⟩ := hcover (Fin.succ j) (Fin.insertNth (α := fun _ => ZMod 3) 0 s d)
    refine ⟨t0, ?_⟩
    have hw0 : (Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 s d) (Fin.succ j) t0) 0 = s := by
      rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)), Fin.insertNth_apply_same]
    have htail : Fin.tail (Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 s d) (Fin.succ j) t0) = Function.update d j t0 := by
      funext k
      show (Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 s d) (Fin.succ j) t0) (Fin.succ k) = Function.update d j t0 k
      rw [Function.update_apply, Function.update_apply]
      by_cases hk : k = j
      · subst hk; simp
      · rw [if_neg (by simp [hk]), if_neg (by simp [hk])]
        rw [Fin.insertNth_zero', Fin.cons_succ]
    have hg := hgraph _ ht0
    have h1 : (Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 s d) (Fin.succ j) t0) 0 = f (Fin.tail (Function.update (Fin.insertNth (α := fun _ => ZMod 3) 0 s d) (Fin.succ j) t0)) := by
      rw [hg, Fin.insertNth_zero']; exact Fin.cons_zero _ _
    rw [hw0, htail] at h1
    exact h1.symm
  have hLatin : ∀ (j : Fin m) (d : Fin m → ZMod 3), Function.Bijective (fun t => f (Function.update d j t)) :=
    fun j d => ⟨hLatin_inj j d, hLatin_surj j d⟩
  obtain ⟨a, ha, b, hf_aff⟩ := latin_hypercube_is_affine m f hLatin
  refine ⟨Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (fun j => - a j), ?_, b, ?_⟩
  · intro i
    obtain (rfl | ⟨j, rfl⟩) := Fin.eq_zero_or_eq_succ i
    · rw [Fin.cons_zero]; exact one_ne_zero
    · rw [Fin.cons_succ]; exact neg_ne_zero.mpr (ha j)
  · have hS : ∀ x : Fin (m+1) → ZMod 3,
        ∑ i, Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (fun j => - a j) i * x i
          = x 0 - ∑ j : Fin m, a j * Fin.tail x j := by
      intro x
      rw [Fin.sum_univ_succ]
      have h0 : Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (fun j => - a j) 0 = 1 := Fin.cons_zero _ _
      have hs : ∀ j : Fin m, Fin.cons (α := fun _ => ZMod 3) (1 : ZMod 3) (fun j => - a j) (Fin.succ j) = - a j := fun j => Fin.cons_succ _ _ j
      simp only [h0, hs]
      have ht : ∀ j : Fin m, x (Fin.succ j) = Fin.tail x j := fun j => rfl
      simp only [ht, neg_mul]
      rw [Finset.sum_neg_distrib]; ring
    apply Finset.ext
    intro x
    simp only [ternary_affine_hyperplane, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rw [hS]
      have hx0 : x 0 = f (Fin.tail x) := by
        have h := hgraph x hx
        conv_lhs => rw [h]
        rw [Fin.insertNth_zero', Fin.cons_zero]
      rw [hx0, hf_aff (Fin.tail x)]; ring
    · intro hx
      have hx' : x 0 - ∑ j, a j * Fin.tail x j = b := by rw [← hS]; exact hx
      have hx0 : x 0 = f (Fin.tail x) := by
        rw [hf_aff (Fin.tail x)]; rw [← hx']; ring
      have hxeq : x = Fin.insertNth (α := fun _ => ZMod 3) 0 (f (Fin.tail x)) (Fin.tail x) := by
        rw [Fin.insertNth_zero']; rw [← hx0, Fin.cons_self_tail]
      rw [hxeq]; exact hf_mem _

/-- Every inclusion-minimal ternary line cover of minimum cardinality 3^(n - 1) is an affine hyperplane ternary_affine_hyperplane n a b with all coordinates of a nonzero. -/
theorem ternary_minimal_line_cover_minimum_card_eq_hyperplane (n : ℕ) (hn : 1 ≤ n) (B : Finset (Fin n → ZMod 3)) (hB : is_minimal_ternary_line_cover n B) (hcard : B.card = 3 ^ (n - 1)) : ∃ (a : Fin n → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3), B = ternary_affine_hyperplane n a b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcard' : B.card = 3 ^ m := by simpa using hcard
  exact ternary_minimal_line_cover_minimum_card_eq_hyperplane_succ m B hB.1 hcard'
