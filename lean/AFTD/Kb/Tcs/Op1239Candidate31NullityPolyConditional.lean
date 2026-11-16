import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.PetrialNullityPoly

/-!
# op_1239_candidate31_nullity_poly_conditional

Topic: combinatorics   Node: fc3aa6a0352b

Provenance: helper lemma. Conditional 72-subforest certificate for OP-1239; computations 28669 and 28679.

For op_1239_candidate31, assuming the stated empty and one-vertex base cases and the stated finite-set cut and leaf identities, the nullity polynomial on vs71 is the displayed degree-seven polynomial.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance  aftdLocal_f7ffdc82f5cbb222_0 : DecidableRel op_1239_candidate31.Adj := by
  unfold op_1239_candidate31
  infer_instance
namespace Op1239Cert31
def vs0 : Finset (Fin 31) := {30}
def vs1 : Finset (Fin 31) := ∅
def vs2 : Finset (Fin 31) := {29, 30}
def vs3 : Finset (Fin 31) := {26, 29, 30}
def vs4 : Finset (Fin 31) := {26, 27, 29, 30}
def vs5 : Finset (Fin 31) := {26, 27, 28, 29, 30}
def vs6 : Finset (Fin 31) := {28}
def vs7 : Finset (Fin 31) := {27, 28}
def vs8 : Finset (Fin 31) := {27, 28, 29, 30}
def vs9 : Finset (Fin 31) := {24, 26, 27, 28, 29, 30}
def vs10 : Finset (Fin 31) := {24, 25, 26, 27, 28, 29, 30}
def vs11 : Finset (Fin 31) := {25}
def vs12 : Finset (Fin 31) := {25, 26, 27, 28, 29, 30}
def vs13 : Finset (Fin 31) := {21, 24, 25, 26, 27, 28, 29, 30}
def vs14 : Finset (Fin 31) := {21, 22, 24, 25, 26, 27, 28, 29, 30}
def vs15 : Finset (Fin 31) := {21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs16 : Finset (Fin 31) := {23}
def vs17 : Finset (Fin 31) := {22, 23}
def vs18 : Finset (Fin 31) := {22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs19 : Finset (Fin 31) := {0, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs20 : Finset (Fin 31) := {0, 11, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs21 : Finset (Fin 31) := {0, 11, 14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs22 : Finset (Fin 31) := {0, 11, 14, 16, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs23 : Finset (Fin 31) := {0, 11, 14, 16, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs24 : Finset (Fin 31) := {0, 11, 14, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs25 : Finset (Fin 31) := {20}
def vs26 : Finset (Fin 31) := {19, 20}
def vs27 : Finset (Fin 31) := {0, 11, 14, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs28 : Finset (Fin 31) := {0, 11, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs29 : Finset (Fin 31) := {0, 11, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs30 : Finset (Fin 31) := {16, 19, 20}
def vs31 : Finset (Fin 31) := {16, 17, 19, 20}
def vs32 : Finset (Fin 31) := {16, 17, 18, 19, 20}
def vs33 : Finset (Fin 31) := {0, 11, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs34 : Finset (Fin 31) := {0, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs35 : Finset (Fin 31) := {18}
def vs36 : Finset (Fin 31) := {17, 18}
def vs37 : Finset (Fin 31) := {17, 18, 19, 20}
def vs38 : Finset (Fin 31) := {14, 16, 17, 18, 19, 20}
def vs39 : Finset (Fin 31) := {14, 15, 16, 17, 18, 19, 20}
def vs40 : Finset (Fin 31) := {0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs41 : Finset (Fin 31) := {0, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs42 : Finset (Fin 31) := {0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs43 : Finset (Fin 31) := {15}
def vs44 : Finset (Fin 31) := {15, 16, 17, 18, 19, 20}
def vs45 : Finset (Fin 31) := {11, 14, 15, 16, 17, 18, 19, 20}
def vs46 : Finset (Fin 31) := {11, 12, 14, 15, 16, 17, 18, 19, 20}
def vs47 : Finset (Fin 31) := {11, 12, 13, 14, 15, 16, 17, 18, 19, 20}
def vs48 : Finset (Fin 31) := {11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs49 : Finset (Fin 31) := {0, 1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs50 : Finset (Fin 31) := {0, 1, 4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs51 : Finset (Fin 31) := {0, 1, 4, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs52 : Finset (Fin 31) := {0, 1, 4, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs53 : Finset (Fin 31) := {0, 1, 4, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs54 : Finset (Fin 31) := {10}
def vs55 : Finset (Fin 31) := {9, 10}
def vs56 : Finset (Fin 31) := {0, 1, 4, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs57 : Finset (Fin 31) := {0, 1, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs58 : Finset (Fin 31) := {0, 1, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs59 : Finset (Fin 31) := {6, 9, 10}
def vs60 : Finset (Fin 31) := {6, 7, 9, 10}
def vs61 : Finset (Fin 31) := {6, 7, 8, 9, 10}
def vs62 : Finset (Fin 31) := {0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs63 : Finset (Fin 31) := {0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs64 : Finset (Fin 31) := {8}
def vs65 : Finset (Fin 31) := {7, 8}
def vs66 : Finset (Fin 31) := {7, 8, 9, 10}
def vs67 : Finset (Fin 31) := {4, 6, 7, 8, 9, 10}
def vs68 : Finset (Fin 31) := {4, 5, 6, 7, 8, 9, 10}
def vs69 : Finset (Fin 31) := {0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs70 : Finset (Fin 31) := {0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
def vs71 : Finset (Fin 31) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}

end Op1239Cert31
open Op1239Cert31

theorem op_1239_candidate31_nullity_poly_conditional
  (hempty : petrial_nullity_poly (op_1239_candidate31.induce ((∅ : Finset (Fin 31)) : Set (Fin 31))) = 1)
  (hsingle : ∀ s : Finset (Fin 31), s.card = 1 → petrial_nullity_poly (op_1239_candidate31.induce (s : Set (Fin 31))) = 1 + Polynomial.X)
  (hcut : ∀ s t : Finset (Fin 31), Disjoint s t → (∀ a ∈ s, ∀ b ∈ t, ¬op_1239_candidate31.Adj a b) →
     petrial_nullity_poly (op_1239_candidate31.induce ((s ∪ t : Finset (Fin 31)) : Set (Fin 31))) =
     petrial_nullity_poly (op_1239_candidate31.induce (s : Set (Fin 31))) * petrial_nullity_poly (op_1239_candidate31.induce (t : Set (Fin 31))))
  (hleaf : ∀ (s : Finset (Fin 31)) (v u : Fin 31) (hv : v ∈ s) (hu : u ∈ s),
     (op_1239_candidate31.induce (s : Set (Fin 31))).degree ⟨v, hv⟩ = 1 → op_1239_candidate31.Adj v u →
     petrial_nullity_poly (op_1239_candidate31.induce (s : Set (Fin 31))) =
     petrial_nullity_poly (op_1239_candidate31.induce ((s.erase v : Finset (Fin 31)) : Set (Fin 31))) +
       2 * petrial_nullity_poly (op_1239_candidate31.induce (((s.erase v).erase u : Finset (Fin 31)) : Set (Fin 31)))) :
    petrial_nullity_poly (op_1239_candidate31.induce (vs71 : Set (Fin 31))) = (560820429 : Polynomial ℕ) + (876263103 : Polynomial ℕ) * Polynomial.X ^ 1 + (530790732 : Polynomial ℕ) * Polynomial.X ^ 2 + (156016800 : Polynomial ℕ) * Polynomial.X ^ 3 + (22309128 : Polynomial ℕ) * Polynomial.X ^ 4 + (1274976 : Polynomial ℕ) * Polynomial.X ^ 5 + (8416 : Polynomial ℕ) * Polynomial.X ^ 6 + (64 : Polynomial ℕ) * Polynomial.X ^ 7 := by
  have h0 : petrial_nullity_poly (op_1239_candidate31.induce (vs0 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs0 (by decide)
  have h1 : petrial_nullity_poly (op_1239_candidate31.induce (vs1 : Set (Fin 31))) = (1 : Polynomial ℕ) := by
    exact hempty
  have h2 : petrial_nullity_poly (op_1239_candidate31.induce (vs2 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs2 29 30 (by decide) (by decide) (by decide) (by decide)
    have ha : vs2.erase 29 = vs0 := by decide
    have hb : (vs2.erase 29).erase 30 = vs1 := by decide
    rw [hb, ha, h0, h1] at hstep
    convert hstep using 1 <;> ring
  have h3 : petrial_nullity_poly (op_1239_candidate31.induce (vs3 : Set (Fin 31))) = (5 : Polynomial ℕ) + (3 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs3 26 29 (by decide) (by decide) (by decide) (by decide)
    have ha : vs3.erase 26 = vs2 := by decide
    have hb : (vs3.erase 26).erase 29 = vs0 := by decide
    rw [hb, ha, h2, h0] at hstep
    convert hstep using 1 <;> ring
  have h4 : petrial_nullity_poly (op_1239_candidate31.induce (vs4 : Set (Fin 31))) = (11 : Polynomial ℕ) + (5 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs4 27 26 (by decide) (by decide) (by decide) (by decide)
    have ha : vs4.erase 27 = vs3 := by decide
    have hb : (vs4.erase 27).erase 26 = vs2 := by decide
    rw [hb, ha, h3, h2] at hstep
    convert hstep using 1 <;> ring
  have h5 : petrial_nullity_poly (op_1239_candidate31.induce (vs5 : Set (Fin 31))) = (21 : Polynomial ℕ) + (11 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs5 28 27 (by decide) (by decide) (by decide) (by decide)
    have ha : vs5.erase 28 = vs4 := by decide
    have hb : (vs5.erase 28).erase 27 = vs3 := by decide
    rw [hb, ha, h4, h3] at hstep
    convert hstep using 1 <;> ring
  have h6 : petrial_nullity_poly (op_1239_candidate31.induce (vs6 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs6 (by decide)
  have h7 : petrial_nullity_poly (op_1239_candidate31.induce (vs7 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs7 27 28 (by decide) (by decide) (by decide) (by decide)
    have ha : vs7.erase 27 = vs6 := by decide
    have hb : (vs7.erase 27).erase 28 = vs1 := by decide
    rw [hb, ha, h6, h1] at hstep
    convert hstep using 1 <;> ring
  have h8 : petrial_nullity_poly (op_1239_candidate31.induce (vs8 : Set (Fin 31))) = (9 : Polynomial ℕ) + (6 : Polynomial ℕ) * Polynomial.X ^ 1 + (1 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hcut vs7 vs2 (by decide) (by decide)
    have hu : vs7 ∪ vs2 = vs8 := by decide
    rw [hu, h7, h2] at hstep
    convert hstep using 1 <;> ring
  have h9 : petrial_nullity_poly (op_1239_candidate31.induce (vs9 : Set (Fin 31))) = (39 : Polynomial ℕ) + (23 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs9 24 26 (by decide) (by decide) (by decide) (by decide)
    have ha : vs9.erase 24 = vs5 := by decide
    have hb : (vs9.erase 24).erase 26 = vs8 := by decide
    rw [hb, ha, h5, h8] at hstep
    convert hstep using 1 <;> ring
  have h10 : petrial_nullity_poly (op_1239_candidate31.induce (vs10 : Set (Fin 31))) = (81 : Polynomial ℕ) + (45 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs10 25 24 (by decide) (by decide) (by decide) (by decide)
    have ha : vs10.erase 25 = vs9 := by decide
    have hb : (vs10.erase 25).erase 24 = vs5 := by decide
    rw [hb, ha, h9, h5] at hstep
    convert hstep using 1 <;> ring
  have h11 : petrial_nullity_poly (op_1239_candidate31.induce (vs11 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs11 (by decide)
  have h12 : petrial_nullity_poly (op_1239_candidate31.induce (vs12 : Set (Fin 31))) = (21 : Polynomial ℕ) + (32 : Polynomial ℕ) * Polynomial.X ^ 1 + (11 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hcut vs11 vs5 (by decide) (by decide)
    have hu : vs11 ∪ vs5 = vs12 := by decide
    rw [hu, h11, h5] at hstep
    convert hstep using 1 <;> ring
  have h13 : petrial_nullity_poly (op_1239_candidate31.induce (vs13 : Set (Fin 31))) = (123 : Polynomial ℕ) + (109 : Polynomial ℕ) * Polynomial.X ^ 1 + (24 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs13 21 24 (by decide) (by decide) (by decide) (by decide)
    have ha : vs13.erase 21 = vs10 := by decide
    have hb : (vs13.erase 21).erase 24 = vs12 := by decide
    rw [hb, ha, h10, h12] at hstep
    convert hstep using 1 <;> ring
  have h14 : petrial_nullity_poly (op_1239_candidate31.induce (vs14 : Set (Fin 31))) = (285 : Polynomial ℕ) + (199 : Polynomial ℕ) * Polynomial.X ^ 1 + (28 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs14 22 21 (by decide) (by decide) (by decide) (by decide)
    have ha : vs14.erase 22 = vs13 := by decide
    have hb : (vs14.erase 22).erase 21 = vs10 := by decide
    rw [hb, ha, h13, h10] at hstep
    convert hstep using 1 <;> ring
  have h15 : petrial_nullity_poly (op_1239_candidate31.induce (vs15 : Set (Fin 31))) = (531 : Polynomial ℕ) + (417 : Polynomial ℕ) * Polynomial.X ^ 1 + (76 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs15 23 22 (by decide) (by decide) (by decide) (by decide)
    have ha : vs15.erase 23 = vs14 := by decide
    have hb : (vs15.erase 23).erase 22 = vs13 := by decide
    rw [hb, ha, h14, h13] at hstep
    convert hstep using 1 <;> ring
  have h16 : petrial_nullity_poly (op_1239_candidate31.induce (vs16 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs16 (by decide)
  have h17 : petrial_nullity_poly (op_1239_candidate31.induce (vs17 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs17 22 23 (by decide) (by decide) (by decide) (by decide)
    have ha : vs17.erase 22 = vs16 := by decide
    have hb : (vs17.erase 22).erase 23 = vs1 := by decide
    rw [hb, ha, h16, h1] at hstep
    convert hstep using 1 <;> ring
  have h18 : petrial_nullity_poly (op_1239_candidate31.induce (vs18 : Set (Fin 31))) = (243 : Polynomial ℕ) + (216 : Polynomial ℕ) * Polynomial.X ^ 1 + (51 : Polynomial ℕ) * Polynomial.X ^ 2 + (2 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hcut vs17 vs10 (by decide) (by decide)
    have hu : vs17 ∪ vs10 = vs18 := by decide
    rw [hu, h17, h10] at hstep
    convert hstep using 1 <;> ring
  have h19 : petrial_nullity_poly (op_1239_candidate31.induce (vs19 : Set (Fin 31))) = (1017 : Polynomial ℕ) + (849 : Polynomial ℕ) * Polynomial.X ^ 1 + (178 : Polynomial ℕ) * Polynomial.X ^ 2 + (4 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs19 0 21 (by decide) (by decide) (by decide) (by decide)
    have ha : vs19.erase 0 = vs15 := by decide
    have hb : (vs19.erase 0).erase 21 = vs18 := by decide
    rw [hb, ha, h15, h18] at hstep
    convert hstep using 1 <;> ring
  have h20 : petrial_nullity_poly (op_1239_candidate31.induce (vs20 : Set (Fin 31))) = (2079 : Polynomial ℕ) + (1683 : Polynomial ℕ) * Polynomial.X ^ 1 + (330 : Polynomial ℕ) * Polynomial.X ^ 2 + (4 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs20 11 0 (by decide) (by decide) (by decide) (by decide)
    have ha : vs20.erase 11 = vs19 := by decide
    have hb : (vs20.erase 11).erase 0 = vs15 := by decide
    rw [hb, ha, h19, h15] at hstep
    convert hstep using 1 <;> ring
  have h21 : petrial_nullity_poly (op_1239_candidate31.induce (vs21 : Set (Fin 31))) = (4113 : Polynomial ℕ) + (3381 : Polynomial ℕ) * Polynomial.X ^ 1 + (686 : Polynomial ℕ) * Polynomial.X ^ 2 + (12 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs21 14 11 (by decide) (by decide) (by decide) (by decide)
    have ha : vs21.erase 14 = vs20 := by decide
    have hb : (vs21.erase 14).erase 11 = vs19 := by decide
    rw [hb, ha, h20, h19] at hstep
    convert hstep using 1 <;> ring
  have h22 : petrial_nullity_poly (op_1239_candidate31.induce (vs22 : Set (Fin 31))) = (8271 : Polynomial ℕ) + (6747 : Polynomial ℕ) * Polynomial.X ^ 1 + (1346 : Polynomial ℕ) * Polynomial.X ^ 2 + (20 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs22 16 14 (by decide) (by decide) (by decide) (by decide)
    have ha : vs22.erase 16 = vs21 := by decide
    have hb : (vs22.erase 16).erase 14 = vs20 := by decide
    rw [hb, ha, h21, h20] at hstep
    convert hstep using 1 <;> ring
  have h23 : petrial_nullity_poly (op_1239_candidate31.induce (vs23 : Set (Fin 31))) = (16497 : Polynomial ℕ) + (13509 : Polynomial ℕ) * Polynomial.X ^ 1 + (2718 : Polynomial ℕ) * Polynomial.X ^ 2 + (44 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs23 19 16 (by decide) (by decide) (by decide) (by decide)
    have ha : vs23.erase 19 = vs22 := by decide
    have hb : (vs23.erase 19).erase 16 = vs21 := by decide
    rw [hb, ha, h22, h21] at hstep
    convert hstep using 1 <;> ring
  have h24 : petrial_nullity_poly (op_1239_candidate31.induce (vs24 : Set (Fin 31))) = (33039 : Polynomial ℕ) + (27003 : Polynomial ℕ) * Polynomial.X ^ 1 + (5410 : Polynomial ℕ) * Polynomial.X ^ 2 + (84 : Polynomial ℕ) * Polynomial.X ^ 3 := by
    have hstep := hleaf vs24 20 19 (by decide) (by decide) (by decide) (by decide)
    have ha : vs24.erase 20 = vs23 := by decide
    have hb : (vs24.erase 20).erase 19 = vs22 := by decide
    rw [hb, ha, h23, h22] at hstep
    convert hstep using 1 <;> ring
  have h25 : petrial_nullity_poly (op_1239_candidate31.induce (vs25 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs25 (by decide)
  have h26 : petrial_nullity_poly (op_1239_candidate31.induce (vs26 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs26 19 20 (by decide) (by decide) (by decide) (by decide)
    have ha : vs26.erase 19 = vs25 := by decide
    have hb : (vs26.erase 19).erase 20 = vs1 := by decide
    rw [hb, ha, h25, h1] at hstep
    convert hstep using 1 <;> ring
  have h27 : petrial_nullity_poly (op_1239_candidate31.induce (vs27 : Set (Fin 31))) = (12339 : Polynomial ℕ) + (14256 : Polynomial ℕ) * Polynomial.X ^ 1 + (5439 : Polynomial ℕ) * Polynomial.X ^ 2 + (722 : Polynomial ℕ) * Polynomial.X ^ 3 + (12 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hcut vs21 vs26 (by decide) (by decide)
    have hu : vs21 ∪ vs26 = vs27 := by decide
    rw [hu, h21, h26] at hstep
    convert hstep using 1 <;> ring
  have h28 : petrial_nullity_poly (op_1239_candidate31.induce (vs28 : Set (Fin 31))) = (57717 : Polynomial ℕ) + (55515 : Polynomial ℕ) * Polynomial.X ^ 1 + (16288 : Polynomial ℕ) * Polynomial.X ^ 2 + (1528 : Polynomial ℕ) * Polynomial.X ^ 3 + (24 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hleaf vs28 17 16 (by decide) (by decide) (by decide) (by decide)
    have ha : vs28.erase 17 = vs24 := by decide
    have hb : (vs28.erase 17).erase 16 = vs27 := by decide
    rw [hb, ha, h24, h27] at hstep
    convert hstep using 1 <;> ring
  have h29 : petrial_nullity_poly (op_1239_candidate31.induce (vs29 : Set (Fin 31))) = (123795 : Polynomial ℕ) + (109521 : Polynomial ℕ) * Polynomial.X ^ 1 + (27108 : Polynomial ℕ) * Polynomial.X ^ 2 + (1696 : Polynomial ℕ) * Polynomial.X ^ 3 + (24 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hleaf vs29 18 17 (by decide) (by decide) (by decide) (by decide)
    have ha : vs29.erase 18 = vs28 := by decide
    have hb : (vs29.erase 18).erase 17 = vs24 := by decide
    rw [hb, ha, h28, h24] at hstep
    convert hstep using 1 <;> ring
  have h30 : petrial_nullity_poly (op_1239_candidate31.induce (vs30 : Set (Fin 31))) = (5 : Polynomial ℕ) + (3 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs30 16 19 (by decide) (by decide) (by decide) (by decide)
    have ha : vs30.erase 16 = vs26 := by decide
    have hb : (vs30.erase 16).erase 19 = vs25 := by decide
    rw [hb, ha, h26, h25] at hstep
    convert hstep using 1 <;> ring
  have h31 : petrial_nullity_poly (op_1239_candidate31.induce (vs31 : Set (Fin 31))) = (11 : Polynomial ℕ) + (5 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs31 17 16 (by decide) (by decide) (by decide) (by decide)
    have ha : vs31.erase 17 = vs30 := by decide
    have hb : (vs31.erase 17).erase 16 = vs26 := by decide
    rw [hb, ha, h30, h26] at hstep
    convert hstep using 1 <;> ring
  have h32 : petrial_nullity_poly (op_1239_candidate31.induce (vs32 : Set (Fin 31))) = (21 : Polynomial ℕ) + (11 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs32 18 17 (by decide) (by decide) (by decide) (by decide)
    have ha : vs32.erase 18 = vs31 := by decide
    have hb : (vs32.erase 18).erase 17 = vs30 := by decide
    rw [hb, ha, h31, h30] at hstep
    convert hstep using 1 <;> ring
  have h33 : petrial_nullity_poly (op_1239_candidate31.induce (vs33 : Set (Fin 31))) = (43659 : Polynomial ℕ) + (58212 : Polynomial ℕ) * Polynomial.X ^ 1 + (25443 : Polynomial ℕ) * Polynomial.X ^ 2 + (3714 : Polynomial ℕ) * Polynomial.X ^ 3 + (44 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hcut vs20 vs32 (by decide) (by decide)
    have hu : vs20 ∪ vs32 = vs33 := by decide
    rw [hu, h20, h32] at hstep
    convert hstep using 1 <;> ring
  have h34 : petrial_nullity_poly (op_1239_candidate31.induce (vs34 : Set (Fin 31))) = (211113 : Polynomial ℕ) + (225945 : Polynomial ℕ) * Polynomial.X ^ 1 + (77994 : Polynomial ℕ) * Polynomial.X ^ 2 + (9124 : Polynomial ℕ) * Polynomial.X ^ 3 + (112 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hleaf vs34 15 14 (by decide) (by decide) (by decide) (by decide)
    have ha : vs34.erase 15 = vs29 := by decide
    have hb : (vs34.erase 15).erase 14 = vs33 := by decide
    rw [hb, ha, h29, h33] at hstep
    convert hstep using 1 <;> ring
  have h35 : petrial_nullity_poly (op_1239_candidate31.induce (vs35 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs35 (by decide)
  have h36 : petrial_nullity_poly (op_1239_candidate31.induce (vs36 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs36 17 18 (by decide) (by decide) (by decide) (by decide)
    have ha : vs36.erase 17 = vs35 := by decide
    have hb : (vs36.erase 17).erase 18 = vs1 := by decide
    rw [hb, ha, h35, h1] at hstep
    convert hstep using 1 <;> ring
  have h37 : petrial_nullity_poly (op_1239_candidate31.induce (vs37 : Set (Fin 31))) = (9 : Polynomial ℕ) + (6 : Polynomial ℕ) * Polynomial.X ^ 1 + (1 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hcut vs36 vs26 (by decide) (by decide)
    have hu : vs36 ∪ vs26 = vs37 := by decide
    rw [hu, h36, h26] at hstep
    convert hstep using 1 <;> ring
  have h38 : petrial_nullity_poly (op_1239_candidate31.induce (vs38 : Set (Fin 31))) = (39 : Polynomial ℕ) + (23 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs38 14 16 (by decide) (by decide) (by decide) (by decide)
    have ha : vs38.erase 14 = vs32 := by decide
    have hb : (vs38.erase 14).erase 16 = vs37 := by decide
    rw [hb, ha, h32, h37] at hstep
    convert hstep using 1 <;> ring
  have h39 : petrial_nullity_poly (op_1239_candidate31.induce (vs39 : Set (Fin 31))) = (81 : Polynomial ℕ) + (45 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs39 15 14 (by decide) (by decide) (by decide) (by decide)
    have ha : vs39.erase 15 = vs38 := by decide
    have hb : (vs39.erase 15).erase 14 = vs32 := by decide
    rw [hb, ha, h38, h32] at hstep
    convert hstep using 1 <;> ring
  have h40 : petrial_nullity_poly (op_1239_candidate31.induce (vs40 : Set (Fin 31))) = (82377 : Polynomial ℕ) + (114534 : Polynomial ℕ) * Polynomial.X ^ 1 + (54657 : Polynomial ℕ) * Polynomial.X ^ 2 + (10032 : Polynomial ℕ) * Polynomial.X ^ 3 + (536 : Polynomial ℕ) * Polynomial.X ^ 4 + (8 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hcut vs19 vs39 (by decide) (by decide)
    have hu : vs19 ∪ vs39 = vs40 := by decide
    rw [hu, h19, h39] at hstep
    convert hstep using 1 <;> ring
  have h41 : petrial_nullity_poly (op_1239_candidate31.induce (vs41 : Set (Fin 31))) = (375867 : Polynomial ℕ) + (455013 : Polynomial ℕ) * Polynomial.X ^ 1 + (187308 : Polynomial ℕ) * Polynomial.X ^ 2 + (29188 : Polynomial ℕ) * Polynomial.X ^ 3 + (1184 : Polynomial ℕ) * Polynomial.X ^ 4 + (16 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs41 12 11 (by decide) (by decide) (by decide) (by decide)
    have ha : vs41.erase 12 = vs34 := by decide
    have hb : (vs41.erase 12).erase 11 = vs40 := by decide
    rw [hb, ha, h34, h40] at hstep
    convert hstep using 1 <;> ring
  have h42 : petrial_nullity_poly (op_1239_candidate31.induce (vs42 : Set (Fin 31))) = (798093 : Polynomial ℕ) + (906903 : Polynomial ℕ) * Polynomial.X ^ 1 + (343296 : Polynomial ℕ) * Polynomial.X ^ 2 + (47436 : Polynomial ℕ) * Polynomial.X ^ 3 + (1408 : Polynomial ℕ) * Polynomial.X ^ 4 + (16 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs42 13 12 (by decide) (by decide) (by decide) (by decide)
    have ha : vs42.erase 13 = vs41 := by decide
    have hb : (vs42.erase 13).erase 12 = vs34 := by decide
    rw [hb, ha, h41, h34] at hstep
    convert hstep using 1 <;> ring
  have h43 : petrial_nullity_poly (op_1239_candidate31.induce (vs43 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs43 (by decide)
  have h44 : petrial_nullity_poly (op_1239_candidate31.induce (vs44 : Set (Fin 31))) = (21 : Polynomial ℕ) + (32 : Polynomial ℕ) * Polynomial.X ^ 1 + (11 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hcut vs43 vs32 (by decide) (by decide)
    have hu : vs43 ∪ vs32 = vs44 := by decide
    rw [hu, h43, h32] at hstep
    convert hstep using 1 <;> ring
  have h45 : petrial_nullity_poly (op_1239_candidate31.induce (vs45 : Set (Fin 31))) = (123 : Polynomial ℕ) + (109 : Polynomial ℕ) * Polynomial.X ^ 1 + (24 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs45 11 14 (by decide) (by decide) (by decide) (by decide)
    have ha : vs45.erase 11 = vs39 := by decide
    have hb : (vs45.erase 11).erase 14 = vs44 := by decide
    rw [hb, ha, h39, h44] at hstep
    convert hstep using 1 <;> ring
  have h46 : petrial_nullity_poly (op_1239_candidate31.induce (vs46 : Set (Fin 31))) = (285 : Polynomial ℕ) + (199 : Polynomial ℕ) * Polynomial.X ^ 1 + (28 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs46 12 11 (by decide) (by decide) (by decide) (by decide)
    have ha : vs46.erase 12 = vs45 := by decide
    have hb : (vs46.erase 12).erase 11 = vs39 := by decide
    rw [hb, ha, h45, h39] at hstep
    convert hstep using 1 <;> ring
  have h47 : petrial_nullity_poly (op_1239_candidate31.induce (vs47 : Set (Fin 31))) = (531 : Polynomial ℕ) + (417 : Polynomial ℕ) * Polynomial.X ^ 1 + (76 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs47 13 12 (by decide) (by decide) (by decide) (by decide)
    have ha : vs47.erase 13 = vs46 := by decide
    have hb : (vs47.erase 13).erase 12 = vs45 := by decide
    rw [hb, ha, h46, h45] at hstep
    convert hstep using 1 <;> ring
  have h48 : petrial_nullity_poly (op_1239_candidate31.induce (vs48 : Set (Fin 31))) = (281961 : Polynomial ℕ) + (442854 : Polynomial ℕ) * Polynomial.X ^ 1 + (254601 : Polynomial ℕ) * Polynomial.X ^ 2 + (63384 : Polynomial ℕ) * Polynomial.X ^ 3 + (5776 : Polynomial ℕ) * Polynomial.X ^ 4 := by
    have hstep := hcut vs47 vs15 (by decide) (by decide)
    have hu : vs47 ∪ vs15 = vs48 := by decide
    rw [hu, h47, h15] at hstep
    convert hstep using 1 <;> ring
  have h49 : petrial_nullity_poly (op_1239_candidate31.induce (vs49 : Set (Fin 31))) = (1362015 : Polynomial ℕ) + (1792611 : Polynomial ℕ) * Polynomial.X ^ 1 + (852498 : Polynomial ℕ) * Polynomial.X ^ 2 + (174204 : Polynomial ℕ) * Polynomial.X ^ 3 + (12960 : Polynomial ℕ) * Polynomial.X ^ 4 + (16 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs49 1 0 (by decide) (by decide) (by decide) (by decide)
    have ha : vs49.erase 1 = vs42 := by decide
    have hb : (vs49.erase 1).erase 0 = vs48 := by decide
    rw [hb, ha, h42, h48] at hstep
    convert hstep using 1 <;> ring
  have h50 : petrial_nullity_poly (op_1239_candidate31.induce (vs50 : Set (Fin 31))) = (2958201 : Polynomial ℕ) + (3606417 : Polynomial ℕ) * Polynomial.X ^ 1 + (1539090 : Polynomial ℕ) * Polynomial.X ^ 2 + (269076 : Polynomial ℕ) * Polynomial.X ^ 3 + (15776 : Polynomial ℕ) * Polynomial.X ^ 4 + (48 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs50 4 1 (by decide) (by decide) (by decide) (by decide)
    have ha : vs50.erase 4 = vs49 := by decide
    have hb : (vs50.erase 4).erase 1 = vs42 := by decide
    rw [hb, ha, h49, h42] at hstep
    convert hstep using 1 <;> ring
  have h51 : petrial_nullity_poly (op_1239_candidate31.induce (vs51 : Set (Fin 31))) = (5682231 : Polynomial ℕ) + (7191639 : Polynomial ℕ) * Polynomial.X ^ 1 + (3244086 : Polynomial ℕ) * Polynomial.X ^ 2 + (617484 : Polynomial ℕ) * Polynomial.X ^ 3 + (41696 : Polynomial ℕ) * Polynomial.X ^ 4 + (80 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs51 6 4 (by decide) (by decide) (by decide) (by decide)
    have ha : vs51.erase 6 = vs50 := by decide
    have hb : (vs51.erase 6).erase 4 = vs49 := by decide
    rw [hb, ha, h50, h49] at hstep
    convert hstep using 1 <;> ring
  have h52 : petrial_nullity_poly (op_1239_candidate31.induce (vs52 : Set (Fin 31))) = (11598633 : Polynomial ℕ) + (14404473 : Polynomial ℕ) * Polynomial.X ^ 1 + (6322266 : Polynomial ℕ) * Polynomial.X ^ 2 + (1155636 : Polynomial ℕ) * Polynomial.X ^ 3 + (73248 : Polynomial ℕ) * Polynomial.X ^ 4 + (176 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs52 9 6 (by decide) (by decide) (by decide) (by decide)
    have ha : vs52.erase 9 = vs51 := by decide
    have hb : (vs52.erase 9).erase 6 = vs50 := by decide
    rw [hb, ha, h51, h50] at hstep
    convert hstep using 1 <;> ring
  have h53 : petrial_nullity_poly (op_1239_candidate31.induce (vs53 : Set (Fin 31))) = (22963095 : Polynomial ℕ) + (28787751 : Polynomial ℕ) * Polynomial.X ^ 1 + (12810438 : Polynomial ℕ) * Polynomial.X ^ 2 + (2390604 : Polynomial ℕ) * Polynomial.X ^ 3 + (156640 : Polynomial ℕ) * Polynomial.X ^ 4 + (336 : Polynomial ℕ) * Polynomial.X ^ 5 := by
    have hstep := hleaf vs53 10 9 (by decide) (by decide) (by decide) (by decide)
    have ha : vs53.erase 10 = vs52 := by decide
    have hb : (vs53.erase 10).erase 9 = vs51 := by decide
    rw [hb, ha, h52, h51] at hstep
    convert hstep using 1 <;> ring
  have h54 : petrial_nullity_poly (op_1239_candidate31.induce (vs54 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs54 (by decide)
  have h55 : petrial_nullity_poly (op_1239_candidate31.induce (vs55 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs55 9 10 (by decide) (by decide) (by decide) (by decide)
    have ha : vs55.erase 9 = vs54 := by decide
    have hb : (vs55.erase 9).erase 10 = vs1 := by decide
    rw [hb, ha, h54, h1] at hstep
    convert hstep using 1 <;> ring
  have h56 : petrial_nullity_poly (op_1239_candidate31.induce (vs56 : Set (Fin 31))) = (8874603 : Polynomial ℕ) + (13777452 : Polynomial ℕ) * Polynomial.X ^ 1 + (8223687 : Polynomial ℕ) * Polynomial.X ^ 2 + (2346318 : Polynomial ℕ) * Polynomial.X ^ 3 + (316404 : Polynomial ℕ) * Polynomial.X ^ 4 + (15920 : Polynomial ℕ) * Polynomial.X ^ 5 + (48 : Polynomial ℕ) * Polynomial.X ^ 6 := by
    have hstep := hcut vs50 vs55 (by decide) (by decide)
    have hu : vs50 ∪ vs55 = vs56 := by decide
    rw [hu, h50, h55] at hstep
    convert hstep using 1 <;> ring
  have h57 : petrial_nullity_poly (op_1239_candidate31.induce (vs57 : Set (Fin 31))) = (40712301 : Polynomial ℕ) + (56342655 : Polynomial ℕ) * Polynomial.X ^ 1 + (29257812 : Polynomial ℕ) * Polynomial.X ^ 2 + (7083240 : Polynomial ℕ) * Polynomial.X ^ 3 + (789448 : Polynomial ℕ) * Polynomial.X ^ 4 + (32176 : Polynomial ℕ) * Polynomial.X ^ 5 + (96 : Polynomial ℕ) * Polynomial.X ^ 6 := by
    have hstep := hleaf vs57 7 6 (by decide) (by decide) (by decide) (by decide)
    have ha : vs57.erase 7 = vs53 := by decide
    have hb : (vs57.erase 7).erase 6 = vs56 := by decide
    rw [hb, ha, h53, h56] at hstep
    convert hstep using 1 <;> ring
  have h58 : petrial_nullity_poly (op_1239_candidate31.induce (vs58 : Set (Fin 31))) = (86638491 : Polynomial ℕ) + (113918157 : Polynomial ℕ) * Polynomial.X ^ 1 + (54878688 : Polynomial ℕ) * Polynomial.X ^ 2 + (11864448 : Polynomial ℕ) * Polynomial.X ^ 3 + (1102728 : Polynomial ℕ) * Polynomial.X ^ 4 + (32848 : Polynomial ℕ) * Polynomial.X ^ 5 + (96 : Polynomial ℕ) * Polynomial.X ^ 6 := by
    have hstep := hleaf vs58 8 7 (by decide) (by decide) (by decide) (by decide)
    have ha : vs58.erase 8 = vs57 := by decide
    have hb : (vs58.erase 8).erase 7 = vs53 := by decide
    rw [hb, ha, h57, h53] at hstep
    convert hstep using 1 <;> ring
  have h59 : petrial_nullity_poly (op_1239_candidate31.induce (vs59 : Set (Fin 31))) = (5 : Polynomial ℕ) + (3 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs59 6 9 (by decide) (by decide) (by decide) (by decide)
    have ha : vs59.erase 6 = vs55 := by decide
    have hb : (vs59.erase 6).erase 9 = vs54 := by decide
    rw [hb, ha, h55, h54] at hstep
    convert hstep using 1 <;> ring
  have h60 : petrial_nullity_poly (op_1239_candidate31.induce (vs60 : Set (Fin 31))) = (11 : Polynomial ℕ) + (5 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs60 7 6 (by decide) (by decide) (by decide) (by decide)
    have ha : vs60.erase 7 = vs59 := by decide
    have hb : (vs60.erase 7).erase 6 = vs55 := by decide
    rw [hb, ha, h59, h55] at hstep
    convert hstep using 1 <;> ring
  have h61 : petrial_nullity_poly (op_1239_candidate31.induce (vs61 : Set (Fin 31))) = (21 : Polynomial ℕ) + (11 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs61 8 7 (by decide) (by decide) (by decide) (by decide)
    have ha : vs61.erase 8 = vs60 := by decide
    have hb : (vs61.erase 8).erase 7 = vs59 := by decide
    rw [hb, ha, h60, h59] at hstep
    convert hstep using 1 <;> ring
  have h62 : petrial_nullity_poly (op_1239_candidate31.induce (vs62 : Set (Fin 31))) = (28602315 : Polynomial ℕ) + (52626996 : Polynomial ℕ) * Polynomial.X ^ 1 + (37621179 : Polynomial ℕ) * Polynomial.X ^ 2 + (13035762 : Polynomial ℕ) * Polynomial.X ^ 3 + (2188404 : Polynomial ℕ) * Polynomial.X ^ 4 + (142896 : Polynomial ℕ) * Polynomial.X ^ 5 + (176 : Polynomial ℕ) * Polynomial.X ^ 6 := by
    have hstep := hcut vs49 vs61 (by decide) (by decide)
    have hu : vs49 ∪ vs61 = vs62 := by decide
    rw [hu, h49, h61] at hstep
    convert hstep using 1 <;> ring
  have h63 : petrial_nullity_poly (op_1239_candidate31.induce (vs63 : Set (Fin 31))) = (143843121 : Polynomial ℕ) + (219172149 : Polynomial ℕ) * Polynomial.X ^ 1 + (130121046 : Polynomial ℕ) * Polynomial.X ^ 2 + (37935972 : Polynomial ℕ) * Polynomial.X ^ 3 + (5479536 : Polynomial ℕ) * Polynomial.X ^ 4 + (318640 : Polynomial ℕ) * Polynomial.X ^ 5 + (448 : Polynomial ℕ) * Polynomial.X ^ 6 := by
    have hstep := hleaf vs63 5 4 (by decide) (by decide) (by decide) (by decide)
    have ha : vs63.erase 5 = vs58 := by decide
    have hb : (vs63.erase 5).erase 4 = vs62 := by decide
    rw [hb, ha, h58, h62] at hstep
    convert hstep using 1 <;> ring
  have h64 : petrial_nullity_poly (op_1239_candidate31.induce (vs64 : Set (Fin 31))) = (1 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using hsingle vs64 (by decide)
  have h65 : petrial_nullity_poly (op_1239_candidate31.induce (vs65 : Set (Fin 31))) = (3 : Polynomial ℕ) + (1 : Polynomial ℕ) * Polynomial.X ^ 1 := by
    have hstep := hleaf vs65 7 8 (by decide) (by decide) (by decide) (by decide)
    have ha : vs65.erase 7 = vs64 := by decide
    have hb : (vs65.erase 7).erase 8 = vs1 := by decide
    rw [hb, ha, h64, h1] at hstep
    convert hstep using 1 <;> ring
  have h66 : petrial_nullity_poly (op_1239_candidate31.induce (vs66 : Set (Fin 31))) = (9 : Polynomial ℕ) + (6 : Polynomial ℕ) * Polynomial.X ^ 1 + (1 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hcut vs65 vs55 (by decide) (by decide)
    have hu : vs65 ∪ vs55 = vs66 := by decide
    rw [hu, h65, h55] at hstep
    convert hstep using 1 <;> ring
  have h67 : petrial_nullity_poly (op_1239_candidate31.induce (vs67 : Set (Fin 31))) = (39 : Polynomial ℕ) + (23 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs67 4 6 (by decide) (by decide) (by decide) (by decide)
    have ha : vs67.erase 4 = vs61 := by decide
    have hb : (vs67.erase 4).erase 6 = vs66 := by decide
    rw [hb, ha, h61, h66] at hstep
    convert hstep using 1 <;> ring
  have h68 : petrial_nullity_poly (op_1239_candidate31.induce (vs68 : Set (Fin 31))) = (81 : Polynomial ℕ) + (45 : Polynomial ℕ) * Polynomial.X ^ 1 + (2 : Polynomial ℕ) * Polynomial.X ^ 2 := by
    have hstep := hleaf vs68 5 4 (by decide) (by decide) (by decide) (by decide)
    have ha : vs68.erase 5 = vs67 := by decide
    have hb : (vs68.erase 5).erase 4 = vs61 := by decide
    rw [hb, ha, h67, h61] at hstep
    convert hstep using 1 <;> ring
  have h69 : petrial_nullity_poly (op_1239_candidate31.induce (vs69 : Set (Fin 31))) = (64645533 : Polynomial ℕ) + (109373328 : Polynomial ℕ) * Polynomial.X ^ 1 + (70213797 : Polynomial ℕ) * Polynomial.X ^ 2 + (21104442 : Polynomial ℕ) * Polynomial.X ^ 3 + (2935260 : Polynomial ℕ) * Polynomial.X ^ 4 + (159528 : Polynomial ℕ) * Polynomial.X ^ 5 + (3536 : Polynomial ℕ) * Polynomial.X ^ 6 + (32 : Polynomial ℕ) * Polynomial.X ^ 7 := by
    have hstep := hcut vs42 vs68 (by decide) (by decide)
    have hu : vs42 ∪ vs68 = vs69 := by decide
    rw [hu, h42, h68] at hstep
    convert hstep using 1 <;> ring
  have h70 : petrial_nullity_poly (op_1239_candidate31.induce (vs70 : Set (Fin 31))) = (273134187 : Polynomial ℕ) + (437918805 : Polynomial ℕ) * Polynomial.X ^ 1 + (270548640 : Polynomial ℕ) * Polynomial.X ^ 2 + (80144856 : Polynomial ℕ) * Polynomial.X ^ 3 + (11350056 : Polynomial ℕ) * Polynomial.X ^ 4 + (637696 : Polynomial ℕ) * Polynomial.X ^ 5 + (7520 : Polynomial ℕ) * Polynomial.X ^ 6 + (64 : Polynomial ℕ) * Polynomial.X ^ 7 := by
    have hstep := hleaf vs70 2 1 (by decide) (by decide) (by decide) (by decide)
    have ha : vs70.erase 2 = vs63 := by decide
    have hb : (vs70.erase 2).erase 1 = vs69 := by decide
    rw [hb, ha, h63, h69] at hstep
    convert hstep using 1 <;> ring
  have h71 : petrial_nullity_poly (op_1239_candidate31.induce (vs71 : Set (Fin 31))) = (560820429 : Polynomial ℕ) + (876263103 : Polynomial ℕ) * Polynomial.X ^ 1 + (530790732 : Polynomial ℕ) * Polynomial.X ^ 2 + (156016800 : Polynomial ℕ) * Polynomial.X ^ 3 + (22309128 : Polynomial ℕ) * Polynomial.X ^ 4 + (1274976 : Polynomial ℕ) * Polynomial.X ^ 5 + (8416 : Polynomial ℕ) * Polynomial.X ^ 6 + (64 : Polynomial ℕ) * Polynomial.X ^ 7 := by
    have hstep := hleaf vs71 3 2 (by decide) (by decide) (by decide) (by decide)
    have ha : vs71.erase 3 = vs70 := by decide
    have hb : (vs71.erase 3).erase 2 = vs63 := by decide
    rw [hb, ha, h70, h63] at hstep
    convert hstep using 1 <;> ring
  exact h71
