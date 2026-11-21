import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130GreedyOrientationsEmbedding
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_greedy_discrepancies_embedding

Topic: online_algorithms   Node: d69dd8057d3d

Provenance: helper lemma. Independent-path-block construction for refuting op_2130_path_greedy_fixed_time_tail

After injectively relabeling the vertices of a greedy carpool instance, restricting every prefix discrepancy vector to the original vertices recovers the original trajectory.
-/

private lemma op2130_scan_step_embedding (n m : ℕ) (f : Fin n ↪ Fin m)
    (d : Fin n → ℤ) (d' : Fin m → ℤ) (e : Fin n × Fin n) (b : Bool)
    (hd : ∀ v, d' (f v) = d v) :
    ∀ v, carpool_step m d' (f e.1, f e.2) b (f v) = carpool_step n d e b v := by
  intro v
  have h1 : (f v = f e.1) ↔ v = e.1 := f.injective.eq_iff
  have h2 : (f v = f e.2) ↔ v = e.2 := f.injective.eq_iff
  simp [carpool_step, hd v, h1, h2]

private lemma scan_embedding (n m : ℕ) (f : Fin n ↪ Fin m)
    (edges : List (Fin n × Fin n)) (signs : List Bool)
    (d : Fin n → ℤ) (d' : Fin m → ℤ) (hd : ∀ v, d' (f v) = d v) :
    (((edges.map (fun e => (f e.1, f e.2))).zip signs).scanl (fun (d : Fin m → ℤ) (p : (Fin m × Fin m) × Bool) => carpool_step m d p.1 p.2) d').map (fun d => fun v => d (f v)) =
      (edges.zip signs).scanl (fun (d : Fin n → ℤ) (p : (Fin n × Fin n) × Bool) => carpool_step n d p.1 p.2) d := by
  induction edges generalizing signs d d' with
  | nil => simp [List.scanl, funext hd]
  | cons e es ih =>
    cases signs with
    | nil => simp [List.scanl, funext hd]
    | cons b bs =>
      simp only [List.map_cons, List.zip_cons_cons, List.scanl_cons]
      have heq : (fun v => d' (f v)) = d := funext hd
      rw [heq]
      congr 1
      exact ih bs _ _ (op2130_scan_step_embedding n m f d d' e b hd)

theorem op_2130_greedy_discrepancies_embedding (n m : ℕ) (f : Fin n ↪ Fin m) (edges : List (Fin n × Fin n)) (coins : List Bool) : (carpool_discrepancies m (edges.map (fun e => (f e.1, f e.2))) (carpool_greedy_orientations m (edges.map (fun e => (f e.1, f e.2))) coins)).map (fun d => fun v => d (f v)) = carpool_discrepancies n edges (carpool_greedy_orientations n edges coins) := by
  unfold carpool_discrepancies
  rw [op_2130_greedy_orientations_embedding]
  exact scan_embedding n m f edges _ _ _ (by intro; rfl)
