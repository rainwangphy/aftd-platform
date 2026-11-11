import AFTD.Prelude

/-!
# op861_no_right_equivariant_k6_r3

Topic: graphs   Node: 44fb8c2a2cba

Provenance: helper lemma. arXiv:2610.42094, Definition 1.2; a finite obstruction to rotation-equivariant selector constructions for OP-861, discovered in recorded computations 22111 and 22121.

There are no two selectors on the six-subsets of eleven cyclic colors that both choose available colors, differ on every pair of subsets intersecting in at most three points, and have the second selector commute with every cyclic rotation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

def op861_a_mask : Fin 6 → Nat := ![159, 287, 567, 231, 711, 683]
def op861_b_mask : Fin 5 → Nat := ![63, 95, 159, 207, 215]
def op861_a_col : Fin 6 → Fin 6 → Fin 11 := ![![0, 1, 2, 3, 4, 7], ![0, 1, 2, 3, 4, 8], ![0, 1, 2, 4, 5, 9], ![0, 1, 2, 5, 6, 7], ![0, 1, 2, 6, 7, 9], ![0, 1, 3, 5, 7, 9]]
def op861_b_col : Fin 5 → Fin 6 → Fin 11 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 7], ![0, 1, 2, 3, 6, 7], ![0, 1, 2, 4, 6, 7]]
def op861_bitset (m : Nat) : Finset (Fin 11) := Finset.univ.filter (fun i => m.testBit i.val)
def op861_fast_mask : Fin 6 → Fin 5 → Fin 6 → Nat := ![![![56, 48, 32, 33, 35, 7], ![60, 56, 48, 33, 35, 15], ![60, 56, 49, 35, 39, 31], ![60, 57, 51, 39, 31, 31], ![28, 57, 51, 46, 27, 23]], ![![28, 56, 48, 32, 33, 35], ![24, 48, 32, 32, 33, 7], ![28, 56, 49, 34, 37, 15], ![24, 49, 35, 38, 23, 15], ![24, 17, 35, 44, 19, 7]], ![![28, 24, 56, 48, 33, 35], ![28, 56, 56, 49, 35, 39], ![24, 25, 50, 36, 33, 7], ![27, 62, 52, 41, 39, 15], ![14, 61, 58, 19, 54, 45]], ![![56, 57, 59, 55, 39, 7], ![52, 40, 25, 59, 55, 6], ![54, 36, 8, 25, 59, 4], ![38, 4, 9, 27, 36, 8], ![36, 8, 25, 55, 4, 9]], ![![7, 15, 30, 28, 56, 56], ![6, 37, 10, 29, 26, 48], ![22, 36, 40, 25, 27, 33], ![54, 36, 41, 27, 52, 33], ![38, 37, 11, 30, 48, 41]], ![![14, 61, 30, 57, 62, 49], ![49, 30, 33, 62, 1, 2], ![6, 61, 14, 57, 30, 33], ![22, 61, 46, 57, 62, 37], ![33, 62, 1, 2, 6, 57]]]
def op861_fast (a : Fin 6) (b : Fin 5) (y x : Fin 6) : Bool := (op861_fast_mask a b y).testBit x.val
def op861_actual (a : Fin 6) (b : Fin 5) (y x : Fin 6) : Bool :=
  decide (((op861_bitset (op861_a_mask a)) ∩ (op861_bitset (op861_b_mask b)).image
    (fun z => z + (op861_a_col a x - op861_b_col b y))).card ≤ 3)
theorem op861_table_correct : ∀ (a : Fin 6) (b : Fin 5) (y x : Fin 6),
    op861_fast a b y x = op861_actual a b y x := by decide

def op861_blocked (a b c d e f : Fin 6) (j : Fin 5) (y : Fin 6) : Bool :=
  op861_fast 0 j y a || op861_fast 1 j y b || op861_fast 2 j y c ||
  op861_fast 3 j y d || op861_fast 4 j y e || op861_fast 5 j y f
def op861_block_all (a b c d e f : Fin 6) (j : Fin 5) : Bool :=
  op861_blocked a b c d e f j 0 && op861_blocked a b c d e f j 1 &&
  op861_blocked a b c d e f j 2 && op861_blocked a b c d e f j 3 &&
  op861_blocked a b c d e f j 4 && op861_blocked a b c d e f j 5
def op861_full_core (a b c d e f : Fin 6) : Bool :=
  op861_block_all a b c d e f 0 || op861_block_all a b c d e f 1 ||
  op861_block_all a b c d e f 2 || op861_block_all a b c d e f 3 ||
  op861_block_all a b c d e f 4


theorem op861_actual_core_0 : ∀ (b c d e f : Fin 6), op861_full_core 0 b c d e f = true := by decide

theorem op861_actual_core_1 : ∀ (b c d e f : Fin 6), op861_full_core 1 b c d e f = true := by decide

theorem op861_actual_core_2 : ∀ (b c d e f : Fin 6), op861_full_core 2 b c d e f = true := by decide

theorem op861_actual_core_3 : ∀ (b c d e f : Fin 6), op861_full_core 3 b c d e f = true := by decide

theorem op861_actual_core_4 : ∀ (b c d e f : Fin 6), op861_full_core 4 b c d e f = true := by decide

theorem op861_actual_core_5 : ∀ (b c d e f : Fin 6), op861_full_core 5 b c d e f = true := by decide


set_option maxHeartbeats 0
set_option maxRecDepth 8192

def op861_A (a : Fin 6) : Finset (Fin 11) := op861_bitset (op861_a_mask a)
def op861_B (b : Fin 5) : Finset (Fin 11) := op861_bitset (op861_b_mask b)

theorem op861_A_card : ∀ a : Fin 6, (op861_A a).card = 6 := by decide
theorem op861_B_card : ∀ b : Fin 5, (op861_B b).card = 6 := by decide
theorem op861_A_index : ∀ (a : Fin 6) (c : Fin 11), c ∈ op861_A a → ∃ x : Fin 6, op861_a_col a x = c := by decide
theorem op861_B_index : ∀ (b : Fin 5) (c : Fin 11), c ∈ op861_B b → ∃ y : Fin 6, op861_b_col b y = c := by decide

theorem op861_all_core (a b c d e f : Fin 6) : op861_full_core a b c d e f = true := by
  fin_cases a
  · exact op861_actual_core_0 b c d e f
  · exact op861_actual_core_1 b c d e f
  · exact op861_actual_core_2 b c d e f
  · exact op861_actual_core_3 b c d e f
  · exact op861_actual_core_4 b c d e f
  · exact op861_actual_core_5 b c d e f

theorem op861_core_implies_blocked (v : Fin 6 → Fin 6)
    (h : op861_full_core (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) = true) :
    ∃ j : Fin 5, ∀ y : Fin 6, ∃ a : Fin 6, op861_fast a j y (v a) = true := by
  simpa [op861_full_core, op861_block_all, op861_blocked,
    Fin.exists_fin_succ, Fin.forall_fin_succ, or_assoc, and_assoc] using h

theorem op861_no_right_equivariant_k6_r3 :
    ¬ ∃ (f g : Finset (Fin 11) → Fin 11),
      (∀ S, S.card = 6 → f S ∈ S) ∧
      (∀ T, T.card = 6 → g T ∈ T) ∧
      (∀ T d, T.card = 6 → g (T.image (fun z => z + d)) = g T + d) ∧
      (∀ S T, S.card = 6 → T.card = 6 → (S ∩ T).card ≤ 3 → f S ≠ g T) := by
  rintro ⟨f, g, hf, hg, heqv, hproper⟩
  have ha (a : Fin 6) : ∃ x : Fin 6, op861_a_col a x = f (op861_A a) :=
    op861_A_index a _ (hf _ (op861_A_card a))
  have hb (b : Fin 5) : ∃ y : Fin 6, op861_b_col b y = g (op861_B b) :=
    op861_B_index b _ (hg _ (op861_B_card b))
  let v : Fin 6 → Fin 6 := fun a => Classical.choose (ha a)
  let w : Fin 5 → Fin 6 := fun b => Classical.choose (hb b)
  have hv (a : Fin 6) : op861_a_col a (v a) = f (op861_A a) := Classical.choose_spec (ha a)
  have hw (b : Fin 5) : op861_b_col b (w b) = g (op861_B b) := Classical.choose_spec (hb b)
  have hcore := op861_all_core (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  obtain ⟨j, hj⟩ := op861_core_implies_blocked v hcore
  obtain ⟨a, hfast⟩ := hj (w j)
  have hactual : op861_actual a j (w j) (v a) = true := by
    simpa [op861_table_correct a j (w j) (v a)] using hfast
  let d : Fin 11 := op861_a_col a (v a) - op861_b_col j (w j)
  have hsmall : (op861_A a ∩ (op861_B j).image (fun z => z + d)).card ≤ 3 := by
    simpa [op861_actual, op861_A, op861_B, d] using hactual
  have hcard : ((op861_B j).image (fun z => z + d)).card = 6 := by
    rw [Finset.card_image_of_injective _ (fun x y h => add_right_cancel h), op861_B_card]
  have hs : f (op861_A a) = g ((op861_B j).image (fun z => z + d)) := by
    rw [heqv _ d (op861_B_card j), ← hv a, ← hw j]
    simp [d, add_comm]
  exact hproper _ _ (op861_A_card a) hcard hsmall hs
