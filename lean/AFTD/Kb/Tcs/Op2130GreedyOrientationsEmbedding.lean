import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_greedy_orientations_embedding

Topic: online_algorithms   Node: b4d03df5b777

Provenance: helper lemma. Independent-path-block construction for refuting op_2130_path_greedy_fixed_time_tail

Injectively relabeling the vertices of a greedy carpool instance leaves its sequence of orientations unchanged for the same tie-breaking coins.
-/

private lemma carpool_step_embedding (n m : ℕ) (f : Fin n ↪ Fin m)
    (d : Fin n → ℤ) (d' : Fin m → ℤ) (e : Fin n × Fin n) (b : Bool)
    (hd : ∀ v, d' (f v) = d v) :
    ∀ v, carpool_step m d' (f e.1, f e.2) b (f v) = carpool_step n d e b v := by
  intro v
  have h1 : (f v = f e.1) ↔ v = e.1 := f.injective.eq_iff
  have h2 : (f v = f e.2) ↔ v = e.2 := f.injective.eq_iff
  simp [carpool_step, hd v, h1, h2]

private lemma greedy_aux_embedding (n m : ℕ) (f : Fin n ↪ Fin m)
    (edges : List (Fin n × Fin n)) (coins : List Bool)
    (d : Fin n → ℤ) (d' : Fin m → ℤ) (hd : ∀ v, d' (f v) = d v) :
    carpool_greedy_orientations.aux m (edges.map (fun e => (f e.1, f e.2))) coins d' =
      carpool_greedy_orientations.aux n edges coins d := by
  induction edges generalizing coins d d' with
  | nil => simp [carpool_greedy_orientations.aux]
  | cons e es ih =>
    cases coins with
    | nil => simp [carpool_greedy_orientations.aux]
    | cons c cs =>
      let b := if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c
      have hb : (if d' (f e.1) < d' (f e.2) then true else if d' (f e.2) < d' (f e.1) then false else c) = b := by simp [hd, b]
      simp only [List.map_cons, carpool_greedy_orientations.aux]
      rw [hb]
      apply congrArg (List.cons b)
      exact ih cs _ _ (carpool_step_embedding n m f d d' e b hd)

theorem op_2130_greedy_orientations_embedding (n m : ℕ) (f : Fin n ↪ Fin m) (edges : List (Fin n × Fin n)) (coins : List Bool) : carpool_greedy_orientations m (edges.map (fun e => (f e.1, f e.2))) coins = carpool_greedy_orientations n edges coins := by
  unfold carpool_greedy_orientations
  exact greedy_aux_embedding n m f edges coins _ _ (by intro; rfl)
