import AFTD.Prelude
import AFTD.Kb.Tcs.HasRangeCriterionSubspaces
import AFTD.Kb.Tcs.KrawtchoukSporadicZeroFiveFiveThreeFive
import AFTD.Kb.Tcs.HasRangeCriterionOfMatrixPencil

/-!
# range_criterion_subspaces_sporadic_five_five_three_five

Topic: quantum   Node: 3e9c97e329ce

Provenance: formalization of a published result. Source: arXiv:2611.08518 Sec. 1

There exist complex subspaces D and E in C^5 ⊗ C^5 of codimensions 3 and 5, respectively, satisfying the range criterion (no nonzero product vector has its tensor in D and its partial conjugate in E).
-/

abbrev r5ZI := GaussianInt
def r5dA : List (List (ℤ × ℤ)) := [
  [(-7,23),(-8,5),(-4,-2),(-3,0),(12,14),(-2,-7),(17,6),(-2,11),(3,18),(5,-8),(0,-12),(-23,4),(-4,-9),(14,-1),(14,12),(10,-7),(-2,-5),(-13,3),(-5,1),(-15,9),(-8,-8),(-13,14),(16,4),(0,0),(-9,-14)],
  [(-1,-8),(-9,-5),(11,10),(-25,-3),(2,-18),(31,-1),(-8,7),(15,13),(13,-1),(3,1),(0,-5),(-11,3),(15,5),(-6,5),(2,21),(-13,-5),(-19,14),(-18,1),(15,1),(-11,-7),(-2,-8),(7,-8),(-5,16),(-16,3),(-2,-4)],
  [(4,5),(-14,2),(-21,-15),(1,-3),(-16,-5),(1,5),(9,-9),(1,-11),(3,-24),(-1,-12),(-15,16),(-13,-2),(12,5),(-10,-10),(5,15),(6,7),(-11,8),(10,-5),(-16,-7),(-14,-9),(9,-10),(3,-3),(8,2),(4,-20),(-4,7)]]
def r5dB : List (List (ℤ × ℤ)) := [
  [(-7,7),(6,12),(11,8),(10,3),(5,-1),(-8,-8),(-9,9),(-9,11),(9,-8),(-9,8),(-8,-1),(2,-11),(-3,-12),(-12,0),(7,11),(-7,7),(-6,-8),(-9,-7),(-12,-8),(6,9),(-6,-9),(-10,-8),(-7,10),(2,-11),(-8,9)],
  [(-6,11),(11,4),(-12,-1),(-11,11),(-4,-6),(10,-7),(6,-2),(11,-7),(-7,10),(-7,-11),(0,13),(1,-14),(-2,-7),(1,-5),(12,-1),(13,1),(-5,6),(11,2),(12,-4),(10,1),(-6,-8),(-11,3),(-8,-9),(11,-1),(-1,13)],
  [(3,11),(-10,9),(-1,11),(12,-4),(-1,-9),(7,8),(10,5),(1,-10),(11,7),(-5,14),(-7,6),(0,1),(9,-5),(15,-3),(-6,-6),(7,8),(5,5),(-10,0),(10,-1),(12,3),(17,3),(1,11),(-8,8),(-10,6),(-9,4)],
  [(-6,-5),(10,-7),(-14,2),(6,6),(-5,-8),(-11,-3),(12,0),(3,12),(-1,-9),(-8,-7),(10,-4),(-2,12),(-11,6),(-14,-5),(-12,6),(8,10),(8,-11),(-12,6),(12,2),(-7,-7),(3,-6),(2,5),(-11,-5),(-2,5),(-9,9)],
  [(-5,-12),(-4,8),(1,-10),(13,-3),(9,-8),(2,-5),(6,-11),(-3,9),(-9,-5),(7,10),(5,-13),(-7,-11),(6,5),(-9,-8),(5,-10),(11,12),(-5,14),(0,-12),(9,-3),(1,12),(-8,-10),(10,8),(-10,1),(7,1),(4,-12)]]
def r5dC : List (List (ℤ × ℤ)) := [
  [(0,-6),(-2,7),(-2,-9),(8,6),(4,-6),(1,-2),(3,-2),(-3,-11),(11,4),(-1,-2),(6,-2),(-8,3),(-5,1),(-3,8),(-2,-7),(-5,7),(-8,17),(0,7),(-9,-8),(-5,4),(-2,2),(3,-2),(-4,-3),(-3,6),(-5,-2)],
  [(5,3),(6,2),(5,11),(2,-1),(1,11),(-8,-7),(2,7),(-6,-3),(-6,5),(0,0),(-8,1),(3,0),(-1,-7),(1,9),(-8,5),(-2,2),(1,4),(4,-4),(-1,6),(6,1),(1,4),(-4,-3),(-3,11),(-1,4),(1,-10)],
  [(2,5),(1,11),(8,0),(1,0),(5,-4),(-1,-4),(-8,-8),(-2,-10),(0,-2),(-1,-4),(-2,4),(8,4),(3,-4),(4,-5),(-6,-2),(-4,-4),(0,4),(1,-2),(7,3),(5,4),(2,-1),(1,-2),(-4,-3),(-5,-2),(0,-4)],
  [(0,3),(-5,1),(6,1),(6,-3),(-2,-1),(-7,-5),(4,1),(4,2),(0,2),(-4,-6),(-1,-4),(1,-3),(-4,4),(5,9),(-2,8),(2,1),(-2,2),(11,-6),(-7,6),(3,-5),(-6,-8),(1,-3),(5,4),(-3,-2),(2,1)],
  [(0,2),(1,0),(5,0),(-2,6),(2,-3),(9,-8),(-6,2),(2,0),(3,-13),(2,-2),(1,6),(-2,-5),(-1,-5),(-3,-1),(-7,-3),(-2,4),(-3,-2),(0,-1),(0,-5),(5,0),(4,-9),(6,-5),(-3,0),(-5,0),(-1,9)],
  [(-10,-7),(-4,2),(-7,6),(0,2),(-6,-5),(-7,-3),(7,1),(-4,-2),(-1,1),(5,-1),(-2,-3),(-4,0),(2,2),(4,5),(-7,-3),(13,3),(-4,4),(8,0),(-3,5),(0,0),(-4,1),(-6,4),(4,-2),(5,6),(3,5)],
  [(-2,-7),(3,-4),(6,-5),(2,-9),(-1,-7),(-12,6),(1,3),(-2,-1),(-6,-3),(-2,5),(0,1),(-5,-5),(-4,4),(3,0),(8,6),(-1,3),(2,-1),(-3,-2),(0,-1),(4,-11),(-5,-3),(-11,-2),(9,2),(-4,1),(0,4)],
  [(-1,-9),(-2,-4),(0,5),(5,-4),(5,-1),(-3,2),(9,-3),(7,-1),(4,5),(8,3),(-2,-2),(2,1),(1,3),(0,5),(-2,-3),(4,5),(4,-2),(3,4),(-2,6),(8,6),(4,-5),(-3,3),(6,5),(7,-1),(-5,-4)],
  [(-1,7),(-1,5),(8,3),(-9,2),(-2,5),(7,5),(-1,1),(2,9),(12,0),(-4,1),(-7,4),(3,-7),(1,2),(6,0),(4,-5),(-8,2),(-4,3),(6,-10),(1,3),(-7,1),(6,0),(4,3),(-2,-4),(-8,-1),(-1,5)],
  [(-5,3),(5,3),(7,9),(0,-2),(-2,8),(3,1),(-2,0),(-3,-8),(2,0),(7,-2),(-6,4),(-2,1),(2,-10),(-5,5),(-9,-4),(-6,-1),(-1,3),(-1,-1),(2,-1),(8,1),(3,2),(1,3),(-5,2),(0,-1),(-2,-6)],
  [(5,0),(-4,-1),(-3,2),(3,-9),(-2,4),(-1,3),(3,1),(6,6),(3,6),(-4,6),(-6,-7),(3,4),(1,7),(3,5),(10,-1),(-5,1),(4,-2),(6,-1),(-8,10),(-5,2),(1,1),(-1,-4),(3,2),(0,-2),(-1,-3)],
  [(-2,7),(2,-5),(-5,-7),(2,-6),(-1,-3),(4,0),(-6,-6),(-4,-2),(-12,-6),(0,-3),(6,-4),(2,12),(2,3),(-1,-5),(-1,5),(6,-3),(12,-5),(-5,8),(-1,0),(2,-2),(-2,1),(1,0),(-2,0),(3,-4),(4,-1)],
  [(3,1),(4,3),(-7,-1),(-6,8),(-3,11),(4,-6),(3,7),(-5,2),(6,8),(1,-6),(4,2),(6,-1),(-1,-4),(0,5),(-12,-1),(5,7),(-3,4),(3,-3),(3,3),(-5,6),(-3,4),(4,5),(-8,1),(7,8),(-2,-3)],
  [(-4,-10),(4,-5),(-7,6),(2,-7),(-6,1),(-8,5),(3,6),(-1,5),(7,-1),(-6,4),(-1,-8),(-1,-13),(-3,5),(-2,3),(7,9),(0,-1),(1,-3),(0,-4),(0,-2),(3,-4),(-6,3),(-5,-3),(3,4),(4,-6),(-4,6)]]
def r5dM : List (List (ℤ × ℤ)) := [
  [(81,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(2,-7),(84,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(9,0),(-3,4),(89,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(1,-4),(-18,2),(-2,-5),(89,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-7,-3),(2,0),(-13,7),(-6,-3),(86,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(3,1),(-18,4),(8,5),(14,-4),(-4,-4),(89,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(5,2),(-2,-6),(7,-12),(-2,8),(-6,-1),(2,2),(81,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-1,-2),(-9,8),(-9,0),(14,7),(4,-9),(14,5),(8,-8),(82,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-13,-4),(-6,-3),(-18,-4),(0,3),(14,5),(5,9),(0,4),(-1,13),(87,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(3,0),(5,-3),(3,6),(-9,13),(-1,-6),(2,1),(3,6),(-4,8),(4,-10),(77,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-7,6),(1,13),(-6,13),(-2,-11),(10,-20),(17,-10),(-5,-6),(5,-9),(2,-8),(3,10),(82,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-5,8),(14,0),(-13,14),(-19,1),(13,-8),(-12,-5),(-12,4),(-2,2),(12,-7),(3,8),(1,2),(86,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(4,-11),(-14,-2),(2,-16),(7,3),(-7,7),(-1,2),(-4,5),(-1,-3),(-3,7),(0,-6),(-4,-2),(-5,0),(75,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(1,10),(7,1),(-9,14),(-7,-1),(8,-6),(-9,0),(-2,5),(2,-3),(12,-2),(-5,13),(-5,2),(2,-2),(1,-4),(79,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-2,-5),(-1,13),(-5,-4),(16,-14),(5,-6),(8,-7),(0,-3),(-2,-3),(4,6),(-12,1),(-5,5),(-8,3),(-2,-8),(6,7),(82,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-3,2),(13,-3),(-3,6),(-2,-8),(-2,-1),(-6,-3),(-4,-4),(-3,10),(3,2),(-1,4),(-3,-1),(0,1),(-1,-4),(1,1),(2,-7),(78,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-1,-11),(13,-6),(2,-10),(-9,8),(7,10),(-12,3),(-2,0),(-10,13),(18,1),(-5,-3),(-7,1),(-3,2),(9,-9),(-5,1),(-5,-1),(0,-3),(75,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-7,-3),(0,-10),(-17,4),(2,0),(12,1),(-4,-2),(-10,-3),(3,2),(10,-2),(-6,6),(10,11),(1,1),(-10,-5),(5,2),(-1,0),(-7,3),(-1,0),(78,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(2,9),(7,-11),(1,13),(-1,11),(0,-13),(-6,5),(-3,1),(2,4),(8,-8),(6,-5),(6,1),(6,-6),(-2,1),(4,-10),(-9,2),(3,0),(-7,-1),(3,-5),(75,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(-4,-11),(-5,-20),(-8,-5),(13,10),(13,-4),(-1,20),(2,-4),(7,18),(11,-2),(2,4),(2,6),(-3,0),(0,2),(-3,-2),(3,12),(3,-5),(3,-5),(4,-1),(3,4),(76,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  [(10,-5),(4,19),(4,-7),(1,-3),(-8,16),(-2,-22),(-2,4),(-11,0),(-2,3),(-5,-1),(-1,-7),(-5,-7),(7,-2),(-4,1),(0,0),(-1,2),(-8,2),(-3,-5),(-5,-2),(-5,-10),(73,0),(0,0),(0,0),(0,0),(0,0)],
  [(-9,-2),(-10,-1),(-12,-4),(8,-3),(13,4),(5,7),(-6,-2),(9,5),(12,-7),(1,3),(8,3),(5,4),(-5,-3),(-3,-2),(2,3),(-3,-2),(0,-1),(8,-2),(-4,0),(3,2),(-1,-2),(78,0),(0,0),(0,0),(0,0)],
  [(-4,-3),(1,-24),(-1,-1),(-4,23),(10,-5),(-7,18),(7,7),(-3,10),(7,-7),(5,5),(-4,2),(4,0),(-2,5),(1,-3),(-1,1),(6,3),(10,2),(2,14),(0,5),(1,8),(-3,3),(-10,1),(78,0),(0,0),(0,0)],
  [(4,-2),(-2,-1),(-8,-11),(7,-2),(6,18),(8,-3),(7,1),(-5,1),(6,1),(-8,-12),(-3,4),(-4,5),(6,-3),(-3,0),(5,-6),(2,4),(-6,2),(4,-2),(5,-4),(6,-7),(0,3),(5,6),(-4,-3),(73,0),(0,0)],
  [(0,-4),(-2,5),(0,-12),(3,6),(1,1),(4,0),(-2,-2),(-3,-8),(3,11),(-3,4),(-10,-5),(1,0),(8,1),(-3,2),(4,-6),(6,-3),(-3,4),(2,-3),(8,-8),(4,6),(-3,-1),(5,-2),(-2,5),(-8,2),(74,0)]]
def r5WA : List (List (ℤ × ℤ)) := [
  [(-210,-286),(30,804),(208,-264)],
  [(379,-3),(55,206),(-752,76)],
  [(51,-811),(87,6),(-144,-644)]]
def r5WB : List (List (ℤ × ℤ)) := [
  [(-154936,-27196),(150438,147826),(-179405,-154381),(-95592,24217),(-40325,-177110)],
  [(-2648,-199174),(209087,-158991),(61822,27502),(-75544,194724),(102740,-195290)],
  [(91874,12808),(-50504,82662),(-275116,-140302),(220702,39504),(162841,43967)],
  [(221285,105097),(-160034,-152028),(-45046,-101434),(-188159,69054),(-209570,-38755)],
  [(139619,177267),(-31003,143159),(82887,162515),(-23530,145829),(25363,-196314)]]
def r5dDA : r5ZI := ⟨1680,27712⟩
def r5dDB : r5ZI := ⟨-9293469,-4452693⟩
def r5cell (l : List (List (ℤ × ℤ))) (i j : ℕ) : r5ZI :=
  let v := (l.getD i []).getD j (0, 0)
  ⟨v.1, v.2⟩
def r5A (a : Fin 3) (r s : Fin 5) : r5ZI := r5cell r5dA a (5 * r + s)
def r5B (j : Fin 5) (r s : Fin 5) : r5ZI := r5cell r5dB j (5 * r + s)
def r5C (k : Fin 14) (r s : Fin 5) : r5ZI := r5cell r5dC k (5 * r + s)
def r5M (p q : Fin 5) (u : Fin 25) : r5ZI := r5cell r5dM (5 * p + q) u
def r5star (z : r5ZI) : r5ZI := ⟨z.re, -z.im⟩
def r5H (p q p' q' : Fin 5) : r5ZI :=
  (∑ a, r5A a p q' * r5star (r5A a p' q)) + (∑ j, r5star (r5B j p q) * r5B j p' q')
    - ∑ k, r5C k p' q * r5star (r5C k p q')
def r5E (p q p' q' : Fin 5) : r5ZI :=
  (16 : r5ZI) * r5H p q p' q' - (if p = p' ∧ q = q' then (3200 : r5ZI) else 0)
    - ∑ u, r5M p q u * r5star (r5M p' q' u)
def r5bd (z : r5ZI) : ℕ := z.re.natAbs + z.im.natAbs
def r5chk : Bool :=
  decide (∀ p q : Fin 5, ∑ p', ∑ q', r5bd (r5E p q p' q') ≤ 1220) &&
  decide (∀ p' q' : Fin 5, ∑ p, ∑ q, r5bd (r5E p q p' q') ≤ 1220)
set_option maxRecDepth 1000000 in
theorem r5chk_true : r5chk = true := by decide +kernel

noncomputable def r5i : r5ZI →+* ℂ := GaussianInt.toComplex

lemma r5i_re (z : r5ZI) : (r5i z).re = (z.re : ℝ) := (GaussianInt.intCast_re z).symm
lemma r5i_im (z : r5ZI) : (r5i z).im = (z.im : ℝ) := (GaussianInt.intCast_im z).symm

lemma r5i_star (z : r5ZI) : r5i (r5star z) = star (r5i z) := by
  apply Complex.ext
  · rw [r5i_re, Complex.star_def, Complex.conj_re, r5i_re]; rfl
  · rw [r5i_im, Complex.star_def, Complex.conj_im, r5i_im]
    show (((-z.im : ℤ)) : ℝ) = _
    push_cast; ring

lemma r5i_norm (z : r5ZI) : ‖r5i z‖ ≤ (r5bd z : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (r5i z)
  rw [r5i_re, r5i_im] at h
  have hb : (r5bd z : ℝ) = |(z.re : ℝ)| + |(z.im : ℝ)| := by
    simp [r5bd, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
  rw [hb]; exact h

lemma r5perm1 (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ r, ∑ s, ∑ r', ∑ s', f r s r' s') = ∑ p, ∑ q, ∑ p', ∑ q', f p q' p' q := by
  refine Finset.sum_congr rfl fun r _ => ?_
  calc (∑ s, ∑ r', ∑ s', f r s r' s') = ∑ r', ∑ s, ∑ s', f r s r' s' := Finset.sum_comm
    _ = ∑ r', ∑ s', ∑ s, f r s r' s' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s', ∑ r', ∑ s, f r s r' s' := Finset.sum_comm

lemma r5perm2 (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ r, ∑ s, ∑ r', ∑ s', f r s r' s') = ∑ p, ∑ q, ∑ p', ∑ q', f p' q' p q := by
  calc (∑ r, ∑ s, ∑ r', ∑ s', f r s r' s') = ∑ r, ∑ r', ∑ s, ∑ s', f r s r' s' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r', ∑ r, ∑ s, ∑ s', f r s r' s' := Finset.sum_comm
    _ = ∑ r', ∑ r, ∑ s', ∑ s, f r s r' s' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r', ∑ s', ∑ r, ∑ s, f r s r' s' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma r5perm3 (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ r, ∑ s, ∑ r', ∑ s', f r s r' s') = ∑ p, ∑ q, ∑ p', ∑ q', f p' q p q' := by
  calc (∑ r, ∑ s, ∑ r', ∑ s', f r s r' s') = ∑ r, ∑ r', ∑ s, ∑ s', f r s r' s' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r', ∑ r, ∑ s, ∑ s', f r s r' s' := Finset.sum_comm
    _ = ∑ r', ∑ s, ∑ r, ∑ s', f r s r' s' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma r5swap4 {n : ℕ} (h : Fin n → Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ p, ∑ q, ∑ p', ∑ q', ∑ i, h i p q p' q') = ∑ i, ∑ p, ∑ q, ∑ p', ∑ q', h i p q p' q' := by
  calc (∑ p, ∑ q, ∑ p', ∑ q', ∑ i, h i p q p' q')
      = ∑ p, ∑ q, ∑ p', ∑ i, ∑ q', h i p q p' q' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ i, ∑ p', ∑ q', h i p q p' q' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ q, ∑ p', ∑ q', h i p q p' q' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ q, ∑ p', ∑ q', h i p q p' q' := Finset.sum_comm

lemma r5i_H (p q p' q' : Fin 5) : r5i (r5H p q p' q') =
    (∑ a, r5i (r5A a p q') * star (r5i (r5A a p' q)))
      + (∑ j, star (r5i (r5B j p q)) * r5i (r5B j p' q'))
      - ∑ k, r5i (r5C k p' q) * star (r5i (r5C k p q')) := by
  simp only [r5H, map_sub, map_add, map_sum, map_mul, r5i_star]

lemma r5i_E (p q p' q' : Fin 5) : r5i (r5E p q p' q') =
    16 * r5i (r5H p q p' q') - (if p = p' ∧ q = q' then (3200 : ℂ) else 0)
      - ∑ u, r5i (r5M p q u) * star (r5i (r5M p' q' u)) := by
  have h16 : r5i (16 : r5ZI) = 16 := map_ofNat r5i 16
  have h3200 : r5i (3200 : r5ZI) = 3200 := map_ofNat r5i 3200
  simp only [r5E, map_sub, map_mul, map_sum, r5i_star, h16]
  congr 2
  split_ifs <;> simp [h3200]

lemma r5i_rowsum (p q : Fin 5) : (∑ p', ∑ q', ‖r5i (r5E p q p' q')‖) ≤ 1220 := by
  have h1 := of_decide_eq_true ((Bool.and_eq_true _ _).mp r5chk_true).1
  have h : (∑ p', ∑ q', ((r5bd (r5E p q p' q') : ℕ) : ℝ)) ≤ 1220 := by
    exact_mod_cast h1 p q
  refine le_trans ?_ h
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => r5i_norm _

lemma r5i_colsum (p' q' : Fin 5) : (∑ p, ∑ q, ‖r5i (r5E p q p' q')‖) ≤ 1220 := by
  have h1 := of_decide_eq_true ((Bool.and_eq_true _ _).mp r5chk_true).2
  have h : (∑ p, ∑ q, ((r5bd (r5E p q p' q') : ℕ) : ℝ)) ≤ 1220 := by
    exact_mod_cast h1 p' q'
  refine le_trans ?_ h
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => r5i_norm _

lemma r5quad_lower (v : Fin 5 → Fin 5 → ℂ) (e : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ)
    (hrow : ∀ p q, (∑ p', ∑ q', ‖e p q p' q'‖) ≤ 1220)
    (hcol : ∀ p' q', (∑ p, ∑ q, ‖e p q p' q'‖) ≤ 1220) :
    -(1220 * ∑ p, ∑ q, ‖v p q‖ ^ 2)
      ≤ (∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * e p q p' q' * v p' q').re := by
  have hterm : ∀ p q p' q', -(‖e p q p' q'‖ * (‖v p q‖ ^ 2 + ‖v p' q'‖ ^ 2) / 2)
      ≤ (star (v p q) * e p q p' q' * v p' q').re := by
    intro p q p' q'
    have h1 : -‖star (v p q) * e p q p' q' * v p' q'‖ ≤ (star (v p q) * e p q p' q' * v p' q').re := by
      have := Complex.abs_re_le_norm (star (v p q) * e p q p' q' * v p' q')
      linarith [(abs_le.mp this).1]
    have h2 : ‖star (v p q) * e p q p' q' * v p' q'‖ = ‖v p q‖ * ‖e p q p' q'‖ * ‖v p' q'‖ := by
      rw [norm_mul, norm_mul, norm_star]
    rw [h2] at h1
    have h3 : 0 ≤ ‖e p q p' q'‖ := norm_nonneg _
    nlinarith [mul_nonneg h3 (sq_nonneg (‖v p q‖ - ‖v p' q'‖))]
  have hsum : (∑ p, ∑ q, ∑ p', ∑ q', -(‖e p q p' q'‖ * (‖v p q‖ ^ 2 + ‖v p' q'‖ ^ 2) / 2))
      ≤ (∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * e p q p' q' * v p' q').re := by
    simp only [Complex.re_sum]
    exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p' _ =>
      Finset.sum_le_sum fun q' _ => hterm p q p' q'
  set S : ℝ := ∑ p, ∑ q, ‖v p q‖ ^ 2 with hS
  have hfirst : (∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p q‖ ^ 2) ≤ 1220 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    calc (∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p q‖ ^ 2)
        = (∑ p', ∑ q', ‖e p q p' q'‖) * ‖v p q‖ ^ 2 := by
          simp only [Finset.sum_mul]
      _ ≤ 1220 * ‖v p q‖ ^ 2 := mul_le_mul_of_nonneg_right (hrow p q) (sq_nonneg _)
  have hsecond : (∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2) ≤ 1220 * S := by
    have hswap : (∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2)
        = ∑ p', ∑ q', ∑ p, ∑ q, ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 := by
      calc (∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2)
          = ∑ p, ∑ p', ∑ q, ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ p', ∑ p, ∑ q, ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 := Finset.sum_comm
        _ = ∑ p', ∑ p, ∑ q', ∑ q, ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ p', ∑ q', ∑ p, ∑ q, ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hswap, hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun p' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q' _ => ?_
    calc (∑ p, ∑ q, ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2)
        = (∑ p, ∑ q, ‖e p q p' q'‖) * ‖v p' q'‖ ^ 2 := by
          simp only [Finset.sum_mul]
      _ ≤ 1220 * ‖v p' q'‖ ^ 2 := mul_le_mul_of_nonneg_right (hcol p' q') (sq_nonneg _)
  have h : ∀ p q p' q', -(‖e p q p' q'‖ * (‖v p q‖ ^ 2 + ‖v p' q'‖ ^ 2) / 2)
      = (-1 / 2) * (‖e p q p' q'‖ * ‖v p q‖ ^ 2) + (-1 / 2) * (‖e p q p' q'‖ * ‖v p' q'‖ ^ 2) := by
    intro p q p' q'; ring
  have heq : (∑ p, ∑ q, ∑ p', ∑ q', -(‖e p q p' q'‖ * (‖v p q‖ ^ 2 + ‖v p' q'‖ ^ 2) / 2))
      = (-1 / 2) * (∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p q‖ ^ 2)
        + (-1 / 2) * ∑ p, ∑ q, ∑ p', ∑ q', ‖e p q p' q'‖ * ‖v p' q'‖ ^ 2 := by
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [heq] at hsum
  linarith

lemma r5mul (f g : Fin 5 → Fin 5 → ℂ) :
    (∑ r, ∑ s, f r s) * (∑ r', ∑ s', g r' s') = ∑ r, ∑ s, ∑ r', ∑ s', f r s * g r' s' := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.mul_sum]

lemma r5main (x y : Fin 5 → ℂ)
    (hA : ∀ a : Fin 3, ∑ r, ∑ s, x r * r5i (r5A a r s) * y s = 0)
    (hB : ∀ j : Fin 5, ∑ r, ∑ s, star (x r) * r5i (r5B j r s) * y s = 0) :
    x = 0 ∨ y = 0 := by
  set v : Fin 5 → Fin 5 → ℂ := fun p q => star (x p) * y q with hv
  have hstarv : ∀ p q, star (v p q) = x p * star (y q) := by
    intro p q; simp only [hv, star_mul', star_star]
  -- the three squares
  let aterm : Fin 3 → ℂ := fun a => ∑ r, ∑ s, x r * r5i (r5A a r s) * y s
  let bterm : Fin 5 → ℂ := fun j => ∑ r, ∑ s, star (x r) * r5i (r5B j r s) * y s
  let cterm : Fin 14 → ℂ := fun k => ∑ r, ∑ s, star (x r) * star (y s) * r5i (r5C k r s)
  have ha : ∀ a, (∑ p, ∑ q, ∑ p', ∑ q', star (v p q)
      * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q') = aterm a * star (aterm a) := by
    intro a
    have e : (∑ r, ∑ s, ∑ r', ∑ s', (x r * r5i (r5A a r s) * y s) *
        (star (x r') * star (r5i (r5A a r' s')) * star (y s'))) = aterm a * star (aterm a) := by
      simp only [aterm, star_sum, star_mul', r5mul]
    rw [← e, r5perm1]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    rw [hstarv]; simp only [hv]; ring
  have hb : ∀ j, (∑ p, ∑ q, ∑ p', ∑ q', star (v p q)
      * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q') = bterm j * star (bterm j) := by
    intro j
    have e : (∑ r, ∑ s, ∑ r', ∑ s', (star (x r) * r5i (r5B j r s) * y s) *
        (x r' * star (r5i (r5B j r' s')) * star (y s'))) = bterm j * star (bterm j) := by
      simp only [bterm, star_sum, star_mul', star_star, r5mul]
    rw [← e, r5perm2]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    rw [hstarv]; simp only [hv]; ring
  have hc : ∀ k, (∑ p, ∑ q, ∑ p', ∑ q', star (v p q)
      * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q') = cterm k * star (cterm k) := by
    intro k
    have e : (∑ r, ∑ s, ∑ r', ∑ s', (star (x r) * star (y s) * r5i (r5C k r s)) *
        (x r' * y s' * star (r5i (r5C k r' s')))) = cterm k * star (cterm k) := by
      simp only [cterm, star_sum, star_mul', star_star, r5mul]
    rw [← e, r5perm3]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    rw [hstarv]; simp only [hv]; ring
  have ha0 : ∀ a, aterm a = 0 := fun a => hA a
  have hb0 : ∀ j, bterm j = 0 := fun j => hB j
  -- the quadratic form Q
  set Q : ℂ := ∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * r5i (r5H p q p' q') * v p' q' with hQ
  have hQval : Q = -∑ k, cterm k * star (cterm k) := by
    have hexp : ∀ p q p' q', star (v p q) * r5i (r5H p q p' q') * v p' q' =
        (∑ a, star (v p q) * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q')
        + (∑ j, star (v p q) * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q')
        - ∑ k, star (v p q) * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q' := by
      intro p q p' q'
      rw [r5i_H]
      rw [mul_sub, sub_mul, mul_add, add_mul]
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hsum : Q = (∑ p, ∑ q, ∑ p', ∑ q', ∑ a, star (v p q) * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q')
        + (∑ p, ∑ q, ∑ p', ∑ q', ∑ j, star (v p q) * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q')
        - ∑ p, ∑ q, ∑ p', ∑ q', ∑ k, star (v p q) * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q' := by
      rw [hQ]
      simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e1 : (∑ p, ∑ q, ∑ p', ∑ q', ∑ a, star (v p q) * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q')
        = ∑ a, ∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q' :=
      r5swap4 (fun a p q p' q' => star (v p q) * (r5i (r5A a p q') * star (r5i (r5A a p' q))) * v p' q')
    have e2 : (∑ p, ∑ q, ∑ p', ∑ q', ∑ j, star (v p q) * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q')
        = ∑ j, ∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q' :=
      r5swap4 (fun j p q p' q' => star (v p q) * (star (r5i (r5B j p q)) * r5i (r5B j p' q')) * v p' q')
    have e3 : (∑ p, ∑ q, ∑ p', ∑ q', ∑ k, star (v p q) * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q')
        = ∑ k, ∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q' :=
      r5swap4 (fun k p q p' q' => star (v p q) * (r5i (r5C k p' q) * star (r5i (r5C k p q'))) * v p' q')
    rw [hsum, e1, e2, e3]
    simp only [ha, hb, hc, ha0, hb0, zero_mul, Finset.sum_const_zero, zero_add]
    ring
  have hQre : Q.re ≤ 0 := by
    rw [hQval, Complex.neg_re, Complex.re_sum]
    have : ∀ k, 0 ≤ (cterm k * star (cterm k)).re := by
      intro k
      rw [Complex.star_def, Complex.mul_conj]
      simp [Complex.normSq_nonneg]
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => this k)
    linarith
  -- the certificate
  let e : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ := fun p q p' q' => r5i (r5E p q p' q')
  let m : Fin 25 → ℂ := fun u => ∑ p, ∑ q, star (v p q) * r5i (r5M p q u)
  have hmsum : (∑ p, ∑ q, ∑ p', ∑ q', ∑ u, star (v p q) *
      (r5i (r5M p q u) * star (r5i (r5M p' q' u))) * v p' q') = ∑ u, m u * star (m u) := by
    rw [r5swap4]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [m, star_sum, star_mul', star_star, r5mul]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    ring
  have hdiag : (∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * (if p = p' ∧ q = q' then (3200 : ℂ) else 0) * v p' q')
      = 3200 * ∑ p, ∑ q, star (v p q) * v p q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Ne.symm hb]
    · simp
  have h16 : 16 * Q = 3200 * (∑ p, ∑ q, star (v p q) * v p q) + (∑ u, m u * star (m u))
      + ∑ p, ∑ q, ∑ p', ∑ q', star (v p q) * e p q p' q' * v p' q' := by
    rw [← hdiag, ← hmsum, hQ]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    simp only [e, r5i_E, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hlow := r5quad_lower v e (fun p q => r5i_rowsum p q) (fun p' q' => r5i_colsum p' q')
  set S : ℝ := ∑ p, ∑ q, ‖v p q‖ ^ 2 with hS
  have hSre : (∑ p, ∑ q, star (v p q) * v p q).re = S := by
    simp only [Complex.re_sum, hS]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  have hm : 0 ≤ (∑ u, m u * star (m u)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun u _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have hre := congrArg Complex.re h16
  have h16re : (16 * Q).re = 16 * Q.re := by simp [Complex.mul_re]
  have h3200re : (3200 * ∑ p, ∑ q, star (v p q) * v p q).re = 3200 * S := by
    rw [← hSre]; simp [Complex.mul_re]
  rw [h16re, Complex.add_re, Complex.add_re, h3200re] at hre
  have hS0 : S ≤ 0 := by nlinarith
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _
  have hS00 : S = 0 := le_antisymm hS0 hSnn
  have hv0 : ∀ p q, v p q = 0 := by
    intro p q
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg _)).mp hS00 p (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg _)).mp h1 q (Finset.mem_univ _)
    simpa using h2
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hx (funext hne)
    ext q
    have := hv0 p q
    simp only [hv] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (star_eq_zero.mp h) hp
    · simpa using h

lemma r5li {k : ℕ} (F : Fin k → Fin 5 → Fin 5 → r5ZI) (piv : Fin k → Fin 5 × Fin 5)
    (W : Fin k → Fin k → r5ZI) (d : r5ZI) (hd : r5i d ≠ 0)
    (hW : ∀ a b, ∑ i, F a (piv i).1 (piv i).2 * W i b = if a = b then d else 0) :
    LinearIndependent ℂ (fun a => (Matrix.of fun r s => r5i (F a r s) : Matrix (Fin 5) (Fin 5) ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have heval : ∀ i, ∑ a, g a * r5i (F a (piv i).1 (piv i).2) = 0 := by
    intro i
    have := congrFun (congrFun hg (piv i).1) (piv i).2
    simpa [Matrix.sum_apply] using this
  have h1 : ∑ i, (∑ a, g a * r5i (F a (piv i).1 (piv i).2)) * r5i (W i b) = 0 := by
    simp [heval]
  have h2 : (∑ i, (∑ a, g a * r5i (F a (piv i).1 (piv i).2)) * r5i (W i b))
      = ∑ a, g a * ∑ i, r5i (F a (piv i).1 (piv i).2) * r5i (W i b) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∀ a, ∑ i, r5i (F a (piv i).1 (piv i).2) * r5i (W i b) = if a = b then r5i d else 0 := by
    intro a
    have := congrArg r5i (hW a b)
    simp only [map_sum, map_mul] at this
    rw [this]
    split_ifs <;> simp
  rw [h2] at h1
  simp only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact (mul_eq_zero.mp h1).resolve_right hd

def r5pA : Fin 3 → Fin 5 × Fin 5 := ![(1,0),(1,3),(2,1)]
def r5pB : Fin 5 → Fin 5 × Fin 5 := ![(0,3),(2,1),(2,3),(3,3),(4,4)]
def r5WAf (i j : Fin 3) : r5ZI := r5cell r5WA i j
def r5WBf (i j : Fin 5) : r5ZI := r5cell r5WB i j

set_option maxRecDepth 1000000 in
theorem r5hWA : ∀ a b : Fin 3, ∑ i, r5A a (r5pA i).1 (r5pA i).2 * r5WAf i b = if a = b then r5dDA else 0 := by
  decide +kernel
set_option maxRecDepth 1000000 in
theorem r5hWB : ∀ a b : Fin 5, ∑ i, r5B a (r5pB i).1 (r5pB i).2 * r5WBf i b = if a = b then r5dDB else 0 := by
  decide +kernel

theorem r5hcond (x : Fin 5 → ℂ) (y : Fin 5 → ℂ)
    (hA : ∀ i : Fin 3, ∑ r : Fin 5, ∑ s : Fin 5, x r * (Matrix.of fun r s => r5i (r5A i r s) : Matrix (Fin 5) (Fin 5) ℂ) r s * y s = 0)
    (hB : ∀ j : Fin 5, ∑ r : Fin 5, ∑ s : Fin 5, star (x r) * (Matrix.of fun r s => r5i (r5B j r s) : Matrix (Fin 5) (Fin 5) ℂ) r s * y s = 0) :
    x = 0 ∨ y = 0 := r5main x y hA hB

theorem r5li_A : LinearIndependent ℂ (fun a : Fin 3 => (Matrix.of fun r s => r5i (r5A a r s) : Matrix (Fin 5) (Fin 5) ℂ)) := by
  refine r5li r5A r5pA r5WAf r5dDA ?_ r5hWA
  intro h
  have := congrArg Complex.re h
  rw [r5i_re] at this
  simp [r5dDA] at this

theorem r5li_B : LinearIndependent ℂ (fun a : Fin 5 => (Matrix.of fun r s => r5i (r5B a r s) : Matrix (Fin 5) (Fin 5) ℂ)) := by
  refine r5li r5B r5pB r5WBf r5dDB ?_ r5hWB
  intro h
  have := congrArg Complex.re h
  rw [r5i_re] at this
  simp [r5dDB] at this

/-- Existence of range-criterion subspaces for the minimal sporadic quadruple (m, n, k, ℓ) = (5, 5, 3, 5). -/
theorem range_criterion_subspaces_sporadic_five_five_three_five :
    has_range_criterion_subspaces 5 5 3 5 := by
  exact has_range_criterion_of_matrix_pencil 5 5 3 5 (fun a => Matrix.of fun r s => r5i (r5A a r s)) (fun j => Matrix.of fun r s => r5i (r5B j r s)) r5li_A r5li_B r5hcond
