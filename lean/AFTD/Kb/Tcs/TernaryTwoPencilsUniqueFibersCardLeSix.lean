import AFTD.Prelude
import AFTD.Kb.Tcs.Bit

/-!
# ternary_two_pencils_unique_fibers_card_le_six

Topic: combinatorics   Node: 7d8132071070

Provenance: helper lemma. Supporting finite obstruction for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185. This is only a normalized seven-column helper, not the conjecture or the complete case w_3(3)=13.

Take the seven residue columns x,y,z,y+z,y-z,x+z,x-z in F3^3, with the first three lifted to the exact standard basis modulo 9. Allow every lift modulo 9 of the remaining four columns, encoded by four ternary digits in each coordinate. At most six nonempty residue fibers of Boolean subset sums have a unique vector sum modulo 9.
-/

/-!
Computable mirrors and sanity lemmas for the seven-column residue pattern
x,y,z,y+z,y-z,x+z,x-z. Provenance: supporting finite certificate for OP-259,
arXiv:2610.19965 Question 3.1, developed in IN-185. The residue, reference,
and missing-value table lemmas check the data; the mask lemmas connect the
finite certificate to the set of nonempty unique lifted fibers.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Three normalized seven-term residue patterns in the ternary cube. -/
def ternary_two_pencils_rows : Fin 3 → Fin 7 → Fin 3 → ℕ :=
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 2], ![1, 0, 1], ![1, 0, 2]], ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 2], ![1, 0, 1], ![2, 0, 1]], ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 2], ![1, 1, 0], ![2, 1, 0]]]

def ternary_two_pencils_residue : Fin 3 → Fin 128 → ℕ :=
  ![![0, 9, 3, 12, 1, 10, 4, 13, 4, 13, 7, 16, 5, 14, 8, 17, 5, 14, 8, 17, 3, 12, 6, 15, 6, 15, 0, 9, 7, 16, 1, 10, 10, 19, 13, 22, 11, 20, 14, 23, 14, 23, 17, 26, 12, 21, 15, 24, 12, 21, 15, 24, 13, 22, 16, 25, 16, 25, 10, 19, 17, 26, 11, 20, 11, 20, 14, 23, 9, 18, 12, 21, 12, 21, 15, 24, 13, 22, 16, 25, 13, 22, 16, 25, 14, 23, 17, 26, 17, 26, 11, 20, 15, 24, 9, 18, 18, 0, 21, 3, 19, 1, 22, 4, 22, 4, 25, 7, 23, 5, 26, 8, 23, 5, 26, 8, 21, 3, 24, 6, 24, 6, 18, 0, 25, 7, 19, 1], ![0, 9, 3, 12, 1, 10, 4, 13, 4, 13, 7, 16, 5, 14, 8, 17, 5, 14, 8, 17, 3, 12, 6, 15, 6, 15, 0, 9, 7, 16, 1, 10, 10, 19, 13, 22, 11, 20, 14, 23, 14, 23, 17, 26, 12, 21, 15, 24, 12, 21, 15, 24, 13, 22, 16, 25, 16, 25, 10, 19, 17, 26, 11, 20, 19, 1, 22, 4, 20, 2, 23, 5, 23, 5, 26, 8, 21, 3, 24, 6, 21, 3, 24, 6, 22, 4, 25, 7, 25, 7, 19, 1, 26, 8, 20, 2, 2, 11, 5, 14, 0, 9, 3, 12, 3, 12, 6, 15, 4, 13, 7, 16, 4, 13, 7, 16, 5, 14, 8, 17, 8, 17, 2, 11, 6, 15, 0, 9], ![0, 9, 3, 12, 1, 10, 4, 13, 4, 13, 7, 16, 5, 14, 8, 17, 5, 14, 8, 17, 3, 12, 6, 15, 6, 15, 0, 9, 7, 16, 1, 10, 12, 21, 15, 24, 13, 22, 16, 25, 16, 25, 10, 19, 17, 26, 11, 20, 17, 26, 11, 20, 15, 24, 9, 18, 9, 18, 12, 21, 10, 19, 13, 22, 21, 3, 24, 6, 22, 4, 25, 7, 25, 7, 19, 1, 26, 8, 20, 2, 26, 8, 20, 2, 24, 6, 18, 0, 18, 0, 21, 3, 19, 1, 22, 4, 6, 15, 0, 9, 7, 16, 1, 10, 1, 10, 4, 13, 2, 11, 5, 14, 2, 11, 5, 14, 0, 9, 3, 12, 3, 12, 6, 15, 4, 13, 7, 16]]

def ternary_two_pencils_reference : Fin 3 → Fin 27 → Fin 128 :=
  ![![0, 4, 0, 2, 6, 12, 22, 10, 14, 1, 5, 36, 3, 7, 13, 23, 11, 15, 69, 33, 37, 45, 35, 39, 47, 55, 43], ![0, 4, 69, 2, 6, 12, 22, 10, 14, 1, 5, 36, 3, 7, 13, 23, 11, 15, 0, 33, 37, 45, 35, 39, 47, 55, 43], ![0, 4, 79, 2, 6, 12, 22, 10, 14, 1, 5, 46, 3, 7, 13, 23, 11, 15, 55, 43, 47, 33, 37, 0, 35, 39, 45]]

def ternary_two_pencils_missing : Fin 3 → ℕ := ![2, 18, 23]

/-- u encodes four ternary lift digits; the first three columns are an exact basis. -/
def ternary_two_pencils_scalar_sum (k j : Fin 3) (u : Fin 81) (s : Fin 128) : ℕ :=
  ((List.finRange 7).foldl (fun z i => z + if s.val.testBit i.val then
    ternary_two_pencils_rows k i j +
      (if i.val < 3 then 0 else 3 * ((u.val / 3 ^ (i.val - 3)) % 3)) else 0) 0) % 9

/-- A scalar residue fiber is nonempty and all its subset values agree with its reference. -/
def ternary_two_pencils_good_fiber (k j : Fin 3) (u : Fin 81) (g : Fin 27) : Bool :=
  g.val != ternary_two_pencils_missing k &&
    (List.finRange 128).all (fun s =>
      ternary_two_pencils_residue k s != g.val ||
        ternary_two_pencils_scalar_sum k j u s ==
          ternary_two_pencils_scalar_sum k j u (ternary_two_pencils_reference k g))

/-- The bit mask of the scalar unique fibers. -/
def ternary_two_pencils_fiber_mask (k j : Fin 3) (u : Fin 81) : ℕ :=
  ((List.finRange 27).foldl (fun z g =>
    z ||| if ternary_two_pencils_good_fiber k j u g then 2 ^ g.val else 0) 0)

def ternary_two_pencils_profile_options : Fin 3 → Fin 3 → List ℕ :=
  ![![[0, 80, 136, 288, 263168, 263171, 263675, 524800, 524803, 525307, 1050624, 1050627, 1051131, 1838592, 134217216], [0, 80, 83, 136, 139, 288, 291, 504, 263168, 524800, 1050624, 1838675, 1838731, 1838883, 132379128], [0, 3, 80, 136, 219, 291, 368, 424, 263168, 524800, 787971, 788187, 788259, 1050627, 1050843, 1050915, 1313792, 1575424]], ![[0, 513, 1028, 2050, 3591, 262143, 1573377, 1573892, 1574914, 18874368, 41943040, 71303168, 133693953, 133694468, 133695490], [0, 513, 1028, 2050, 18874368, 20447232, 20450823, 41943040, 43515904, 43519495, 71303168, 72876032, 72879623, 132120576, 132379128], [0, 1028, 1541, 2050, 2563, 1572864, 1573377, 1575942, 20447232, 20447745, 20450310, 41943040, 60817408, 71303168, 90177536, 114819072, 114819585, 114822150]], ![[0, 2304, 16416, 131076, 149796, 262143, 6291456, 17301504, 33816576, 68159744, 68173856, 68288516, 125569280, 125583392, 125698052], [0, 2304, 18720, 131076, 147492, 17301504, 23592960, 33816576, 40108032, 68157440, 68173856, 68290820, 74448896, 74465312, 74582276, 119275520, 119291936, 119408900], [0, 2304, 16416, 131076, 6291456, 17301504, 33816576, 57409536, 57521883, 74448896, 74598692, 85458944, 85608740, 101974016, 102123812]]]

def ternary_residue_mask_card (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 27)).filter (fun i => m.testBit i.val)).card

theorem ternary_two_pencils_residue_table : ∀ k s,
    ternary_two_pencils_residue k s =
      (((List.finRange 7).foldl (fun z i => z + if s.val.testBit i.val then
        ternary_two_pencils_rows k i 0 else 0) 0) % 3) * 9 +
      (((List.finRange 7).foldl (fun z i => z + if s.val.testBit i.val then
        ternary_two_pencils_rows k i 1 else 0) 0) % 3) * 3 +
      (((List.finRange 7).foldl (fun z i => z + if s.val.testBit i.val then
        ternary_two_pencils_rows k i 2 else 0) 0) % 3) := by decide



theorem ternary_two_pencils_reference_table : ∀ k g,
    (g.val = ternary_two_pencils_missing k ∨
      ternary_two_pencils_residue k (ternary_two_pencils_reference k g) = g.val) := by decide




theorem ternary_two_pencils_missing_table : ∀ k s,
    ternary_two_pencils_residue k s ≠ ternary_two_pencils_missing k := by decide

theorem ternary_two_pencils_good_fiber_iff (k j : Fin 3) (u : Fin 81) (g : Fin 27) :
    ternary_two_pencils_good_fiber k j u g = true ↔
      g.val ≠ ternary_two_pencils_missing k ∧ ∀ s,
        ternary_two_pencils_residue k s = g.val →
          ternary_two_pencils_scalar_sum k j u s =
            ternary_two_pencils_scalar_sum k j u (ternary_two_pencils_reference k g) := by
  simp [ternary_two_pencils_good_fiber, List.all_eq_true, imp_iff_not_or]

theorem ternary_fiber_mask_fold_testBit (l : List (Fin 27)) (good : Fin 27 → Bool)
    (a i : ℕ) :
    (l.foldl (fun z g => z ||| if good g then 2 ^ g.val else 0) a).testBit i =
      (a.testBit i || l.any (fun g => good g && decide (g.val = i))) := by
  induction l generalizing a with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or]
    cases h : good g <;> simp [h, Nat.testBit_two_pow, Bool.or_assoc]

theorem ternary_two_pencils_fiber_mask_testBit (k j : Fin 3) (u : Fin 81) (g : Fin 27) :
    (ternary_two_pencils_fiber_mask k j u).testBit g.val =
      ternary_two_pencils_good_fiber k j u g := by
  rw [ternary_two_pencils_fiber_mask, ternary_fiber_mask_fold_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, _, hh, he⟩
    have he' : h = g := Fin.ext he
    subst h
    exact hh
  · intro hg
    exact ⟨g, by simp, hg, rfl⟩

/-- Fibers whose actual three-coordinate subset values are unique modulo 9. -/
def ternary_two_pencils_unique_fibers (k : Fin 3) (u v w : Fin 81) : Finset (Fin 27) :=
  Finset.univ.filter (fun g =>
    (∃ s, ternary_two_pencils_residue k s = g.val) ∧
    ∀ s t, ternary_two_pencils_residue k s = g.val →
      ternary_two_pencils_residue k t = g.val →
      ternary_two_pencils_scalar_sum k 0 u s = ternary_two_pencils_scalar_sum k 0 u t ∧
      ternary_two_pencils_scalar_sum k 1 v s = ternary_two_pencils_scalar_sum k 1 v t ∧
      ternary_two_pencils_scalar_sum k 2 w s = ternary_two_pencils_scalar_sum k 2 w t)

theorem ternary_two_pencils_unique_fibers_eq_mask (k : Fin 3) (u v w : Fin 81) :
    ternary_two_pencils_unique_fibers k u v w = Finset.univ.filter (fun g : Fin 27 =>
      (((ternary_two_pencils_fiber_mask k 0 u &&& ternary_two_pencils_fiber_mask k 1 v) &&&
          ternary_two_pencils_fiber_mask k 2 w).testBit g.val)) := by
  ext g
  simp only [ternary_two_pencils_unique_fibers, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.testBit_and, Bool.and_eq_true, ternary_two_pencils_fiber_mask_testBit,
    ternary_two_pencils_good_fiber_iff]
  have href : g.val ≠ ternary_two_pencils_missing k →
      ternary_two_pencils_residue k (ternary_two_pencils_reference k g) = g.val := by
    intro hg
    exact (ternary_two_pencils_reference_table k g).resolve_left hg
  constructor
  · rintro ⟨⟨s, hs⟩, hall⟩
    have hg : g.val ≠ ternary_two_pencils_missing k := by
      intro he
      exact ternary_two_pencils_missing_table k s (hs.trans he)
    have hh := fun t ht => hall t (ternary_two_pencils_reference k g) ht (href hg)
    exact ⟨⟨⟨hg, fun t ht => (hh t ht).1⟩, ⟨hg, fun t ht => (hh t ht).2.1⟩⟩,
      hg, fun t ht => (hh t ht).2.2⟩
  · rintro ⟨⟨⟨hg, h0⟩, ⟨_, h1⟩⟩, ⟨_, h2⟩⟩
    refine ⟨⟨ternary_two_pencils_reference k g, href hg⟩, ?_⟩
    intro s t hs ht
    exact ⟨(h0 s hs).trans (h0 t ht).symm, (h1 s hs).trans (h1 t ht).symm,
      (h2 s hs).trans (h2 t ht).symm⟩

theorem ternary_two_pencils_unique_fibers_card_le_six (u v w : Fin 81) :
    (ternary_two_pencils_unique_fibers 0 u v w).card ≤ 6 := by
  have ternary_two_pencils_profile_0_0 : ∀ u,
      ternary_two_pencils_fiber_mask 0 0 u ∈ ternary_two_pencils_profile_options 0 0 := by decide

  have ternary_two_pencils_profile_0_1 : ∀ u,
      ternary_two_pencils_fiber_mask 0 1 u ∈ ternary_two_pencils_profile_options 0 1 := by decide

  have ternary_two_pencils_profile_0_2 : ∀ u,
      ternary_two_pencils_fiber_mask 0 2 u ∈ ternary_two_pencils_profile_options 0 2 := by decide

  have ternary_two_pencils_profile_mem (j : Fin 3) (u : Fin 81) :
      ternary_two_pencils_fiber_mask 0 j u ∈ ternary_two_pencils_profile_options 0 j := by
    fin_cases j
    · exact ternary_two_pencils_profile_0_0 u
    · exact ternary_two_pencils_profile_0_1 u
    · exact ternary_two_pencils_profile_0_2 u

  have ternary_two_pencils_options_intersection :
      (ternary_two_pencils_profile_options 0 0).all (fun a =>
        (ternary_two_pencils_profile_options 0 1).all (fun b =>
          (ternary_two_pencils_profile_options 0 2).all (fun c =>
            decide (ternary_residue_mask_card ((a &&& b) &&& c) ≤ 6)))) = true := by decide


  have ternary_two_pencils_mask_intersection_card_le (u v w : Fin 81) :
      ternary_residue_mask_card
        ((ternary_two_pencils_fiber_mask 0 0 u &&& ternary_two_pencils_fiber_mask 0 1 v) &&&
          ternary_two_pencils_fiber_mask 0 2 w) ≤ 6 := by
    have h0 := (List.all_eq_true.mp ternary_two_pencils_options_intersection)
      _ (ternary_two_pencils_profile_mem 0 u)
    have h1 := (List.all_eq_true.mp h0) _ (ternary_two_pencils_profile_mem 1 v)
    have h2 := (List.all_eq_true.mp h1) _ (ternary_two_pencils_profile_mem 2 w)
    exact of_decide_eq_true h2

  rw [ternary_two_pencils_unique_fibers_eq_mask]
  exact ternary_two_pencils_mask_intersection_card_le u v w
