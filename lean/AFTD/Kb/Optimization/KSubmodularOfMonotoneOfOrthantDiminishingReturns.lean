import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodMonotone
import AFTD.Kb.Optimization.HasOrthantDiminishingReturns
import AFTD.Kb.Optimization.IsKSubmodular
import AFTD.Kb.Optimization.KSubmodLe
import AFTD.Kb.Optimization.KSubmodJoin
import AFTD.Kb.Optimization.KSubmodMeet

/-!
# k_submodular_of_monotone_of_orthant_diminishing_returns

Topic: submodular   Node: 259b9fea1f45

Provenance: formalization of a published result. Source: arXiv:2610.26677, proof of Lemma 2.2

A monotone function on assignments Fin n → Option (Fin k) that satisfies orthant diminishing returns is k-submodular.
-/

def k_submodular_of_monotone_of_orthant_diminishing_returns_patch {n k : ℕ}
    (u : Fin n → Option (Fin k)) (S : Finset (Fin n))
    (x : Fin n → Option (Fin k)) : Fin n → Option (Fin k) :=
  fun e => if e ∈ S then u e else x e

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_patch_empty {n k : ℕ}
    (u : Fin n → Option (Fin k)) (x : Fin n → Option (Fin k)) :
    k_submodular_of_monotone_of_orthant_diminishing_returns_patch u ∅ x = x := by
  funext e
  simp [k_submodular_of_monotone_of_orthant_diminishing_returns_patch]

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_patch_insert {n k : ℕ}
    (u : Fin n → Option (Fin k)) (S : Finset (Fin n))
    (x : Fin n → Option (Fin k)) (e : Fin n) :
    k_submodular_of_monotone_of_orthant_diminishing_returns_patch u (insert e S) x =
      k_submodular_of_monotone_of_orthant_diminishing_returns_patch u S (Function.update x e (u e)) := by
  funext e'
  simp only [k_submodular_of_monotone_of_orthant_diminishing_returns_patch, Function.update_apply, Finset.mem_insert]
  by_cases he : e' = e
  · subst he; simp
  · simp [he]

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_le_update {n k : ℕ}
    (a b : Fin n → Option (Fin k)) (e : Fin n) (i : Fin k) (hab : k_submod_le a b) :
    k_submod_le (Function.update a e (some i)) (Function.update b e (some i)) := by
  intro e'
  simp only [Function.update_apply]
  by_cases he : e' = e
  · subst he; simp
  · simp only [if_neg he]
    exact hab e'

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_update_none_of_mem {n k : ℕ}
    (b : Fin n → Option (Fin k)) (S : Finset (Fin n)) (e : Fin n) (i : Fin k) (he : e ∉ S)
    (hb : ∀ e' ∈ S, b e' = none) :
    ∀ e' ∈ S, Function.update b e (some i) e' = none := by
  intro e' he'
  have : e' ≠ e := by rintro rfl; exact he he'
  simp [Function.update, this, hb e' he']

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_dr_finset_patch {n k : ℕ}
    (f : (Fin n → Option (Fin k)) → ℝ)
    (hdim : has_orthant_diminishing_returns f)
    (u : Fin n → Option (Fin k)) (S : Finset (Fin n))
    (hu : ∀ e ∈ S, ∃ i, u e = some i) :
    ∀ (a b : Fin n → Option (Fin k)),
      k_submod_le a b →
      (∀ e ∈ S, b e = none) →
      f (k_submodular_of_monotone_of_orthant_diminishing_returns_patch u S b) - f b ≤
        f (k_submodular_of_monotone_of_orthant_diminishing_returns_patch u S a) - f a := by
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab hb
    simp [k_submodular_of_monotone_of_orthant_diminishing_returns_patch_empty]
  | insert e S he ih =>
    intro a b hab hb
    have hu_e : ∃ i, u e = some i := hu e (Finset.mem_insert_self e S)
    have hu_S : ∀ e' ∈ S, ∃ i, u e' = some i := fun e' he' => hu e' (Finset.mem_insert_of_mem he')
    have hb_e : b e = none := hb e (Finset.mem_insert_self e S)
    have hb_S : ∀ e' ∈ S, b e' = none := fun e' he' => hb e' (Finset.mem_insert_of_mem he')
    rcases hu_e with ⟨i, hi⟩
    have hdim_step : f (Function.update b e (some i)) - f b ≤ f (Function.update a e (some i)) - f a :=
      hdim a b e i hab hb_e
    have hab' : k_submod_le (Function.update a e (some i)) (Function.update b e (some i)) :=
      k_submodular_of_monotone_of_orthant_diminishing_returns_le_update a b e i hab
    have hb' : ∀ e' ∈ S, Function.update b e (some i) e' = none :=
      k_submodular_of_monotone_of_orthant_diminishing_returns_update_none_of_mem b S e i he hb_S
    have h_ih := ih hu_S (Function.update a e (some i)) (Function.update b e (some i)) hab' hb'
    rw [k_submodular_of_monotone_of_orthant_diminishing_returns_patch_insert,
        k_submodular_of_monotone_of_orthant_diminishing_returns_patch_insert, hi]
    linarith

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_compatible_meet_le {n k : ℕ}
    (u v : Fin n → Option (Fin k)) :
    k_submod_le (k_submod_meet u v) v := by
  intro e
  dsimp [k_submod_meet]
  rcases hu : u e with _ | i <;> rcases hv : v e with _ | j
  · simp
  · simp
  · simp
  · by_cases h : i = j
    · subst h; simp
    · simp [h]

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_patch_meet_eq_u {n k : ℕ}
    (u v : Fin n → Option (Fin k))
    (hcomp : ∀ e i j, u e = some i → v e = some j → i = j) :
    let S : Finset (Fin n) := Finset.filter (fun e => (u e).isSome ∧ (v e).isNone) Finset.univ
    k_submodular_of_monotone_of_orthant_diminishing_returns_patch u S (k_submod_meet u v) = u := by
  intro S
  funext e
  dsimp [k_submodular_of_monotone_of_orthant_diminishing_returns_patch, S, k_submod_meet]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hu : u e with _ | i <;> rcases hv : v e with _ | j
  · simp
  · simp
  · simp
  · have hij := hcomp e i j hu hv
    subst hij
    simp

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_patch_v_eq_join {n k : ℕ}
    (u v : Fin n → Option (Fin k))
    (hcomp : ∀ e i j, u e = some i → v e = some j → i = j) :
    let S : Finset (Fin n) := Finset.filter (fun e => (u e).isSome ∧ (v e).isNone) Finset.univ
    k_submodular_of_monotone_of_orthant_diminishing_returns_patch u S v = k_submod_join u v := by
  intro S
  funext e
  dsimp [k_submodular_of_monotone_of_orthant_diminishing_returns_patch, S, k_submod_join]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hu : u e with _ | i <;> rcases hv : v e with _ | j
  · simp
  · simp
  · simp
  · have hij := hcomp e i j hu hv
    subst hij
    simp

theorem k_submodular_of_monotone_of_orthant_diminishing_returns_of_compatible {n k : ℕ}
    (f : (Fin n → Option (Fin k)) → ℝ)
    (hdim : has_orthant_diminishing_returns f)
    (u v : Fin n → Option (Fin k))
    (hcomp : ∀ e i j, u e = some i → v e = some j → i = j) :
    f (k_submod_meet u v) + f (k_submod_join u v) ≤ f u + f v := by
  let S : Finset (Fin n) := Finset.filter (fun e => (u e).isSome ∧ (v e).isNone) Finset.univ
  have hu : ∀ e ∈ S, ∃ i, u e = some i := by
    intro e he
    have h := (Finset.mem_filter.mp he).2.1
    rcases h_ue : u e with _ | i
    · simp [h_ue] at h
    · exact ⟨i, rfl⟩
  have hb : ∀ e ∈ S, v e = none := by
    intro e he
    have h := (Finset.mem_filter.mp he).2.2
    rcases h_ve : v e with _ | j
    · rfl
    · simp [h_ve] at h
  have hab := k_submodular_of_monotone_of_orthant_diminishing_returns_compatible_meet_le u v
  have h_patch := k_submodular_of_monotone_of_orthant_diminishing_returns_dr_finset_patch
    f hdim u S hu (k_submod_meet u v) v hab hb
  have h_join := k_submodular_of_monotone_of_orthant_diminishing_returns_patch_v_eq_join u v hcomp
  have h_u := k_submodular_of_monotone_of_orthant_diminishing_returns_patch_meet_eq_u u v hcomp
  dsimp [S] at h_join h_u
  rw [h_join, h_u] at h_patch
  linarith

/-- Monotonicity and orthant diminishing returns imply k-submodularity. -/
theorem k_submodular_of_monotone_of_orthant_diminishing_returns
    {n k : ℕ} (f : (Fin n → Option (Fin k)) → ℝ)
    (hmono : is_k_submod_monotone f)
    (hdim : has_orthant_diminishing_returns f) :
    is_k_submodular f := by
  intro x y
  let u : Fin n → Option (Fin k) := fun e =>
    match x e, y e with
    | some i, some j => if i = j then some i else none
    | a, _ => a
  let v : Fin n → Option (Fin k) := fun e =>
    match x e, y e with
    | some i, some j => if i = j then some j else none
    | _, b => b
  have hu_le : k_submod_le u x := by
    intro e
    dsimp [u]
    rcases hx : x e with _ | i <;> rcases hy : y e with _ | j
    · simp
    · simp
    · simp
    · by_cases h : i = j
      · subst h; simp
      · simp [h]
  have hv_le : k_submod_le v y := by
    intro e
    dsimp [v]
    rcases hx : x e with _ | i <;> rcases hy : y e with _ | j
    · simp
    · simp
    · simp
    · by_cases h : i = j
      · subst h; simp
      · simp [h]
  have hmeet : k_submod_meet u v = k_submod_meet x y := by
    ext e
    dsimp [u, v, k_submod_meet]
    rcases hx : x e with _ | i <;> rcases hy : y e with _ | j
    · rfl
    · rfl
    · rfl
    · by_cases h : i = j
      · subst h; simp
      · simp [h]
  have hjoin : k_submod_join u v = k_submod_join x y := by
    ext e
    dsimp [u, v, k_submod_join]
    rcases hx : x e with _ | i <;> rcases hy : y e with _ | j
    · rfl
    · rfl
    · rfl
    · by_cases h : i = j
      · subst h; simp
      · simp [h]
  have hcomp : ∀ e i j, u e = some i → v e = some j → i = j := by
    intro e i j
    dsimp [u, v]
    rcases hx : x e with _ | xi <;> rcases hy : y e with _ | yj
    · intro h; contradiction
    · intro h; contradiction
    · intro _ h; contradiction
    · by_cases h : xi = yj
      · subst h
        simp
        rintro rfl rfl
        rfl
      · simp [h]
  have hsub := k_submodular_of_monotone_of_orthant_diminishing_returns_of_compatible f hdim u v hcomp
  have hu_mono := hmono u x hu_le
  have hv_mono := hmono v y hv_le
  rw [hmeet, hjoin] at hsub
  linarith
