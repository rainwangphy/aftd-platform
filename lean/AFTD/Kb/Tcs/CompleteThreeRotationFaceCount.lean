import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFaceCount
import AFTD.Kb.Tcs.SimpleGraphIsRotationSystem
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm
import AFTD.Kb.Tcs.PosetNonemptyOrderIsoOfCardOrderHomEqOfConnected

/-!
# complete_three_rotation_face_count

Topic: graphs   Node: 0d8532a6de81

Provenance: helper lemma. Sanity lemma for simple_graph_rotation_face_count (OP-541)

Every rotation system of the triangle K_3 has exactly 2 faces (inside and outside), so V - E + F = 3 - 3 + 2 = 2 (sanity check of simple_graph_rotation_face_count).
-/

open SimpleGraph

def complete_three_d01 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(0, 1), by decide⟩
def complete_three_d02 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(0, 2), by decide⟩
def complete_three_d10 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(1, 0), by decide⟩
def complete_three_d12 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(1, 2), by decide⟩
def complete_three_d20 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(2, 0), by decide⟩
def complete_three_d21 : (⊤ : SimpleGraph (Fin 3)).Dart := ⟨(2, 1), by decide⟩

lemma complete_three_darts_zero (z : (⊤ : SimpleGraph (Fin 3)).Dart) (h : z.fst = 0) :
    z = complete_three_d01 ∨ z = complete_three_d02 := by
  have hadj : z.fst ≠ z.snd := z.adj
  rw [h] at hadj
  have : z.snd = 1 ∨ z.snd = 2 := by
    revert hadj; generalize z.snd = s; fin_cases s <;> decide
  rcases this with h1 | h2
  · left; apply SimpleGraph.Dart.ext; exact Prod.ext h h1
  · right; apply SimpleGraph.Dart.ext; exact Prod.ext h h2

lemma complete_three_darts_one (z : (⊤ : SimpleGraph (Fin 3)).Dart) (h : z.fst = 1) :
    z = complete_three_d10 ∨ z = complete_three_d12 := by
  have hadj : z.fst ≠ z.snd := z.adj
  rw [h] at hadj
  have : z.snd = 0 ∨ z.snd = 2 := by
    revert hadj; generalize z.snd = s; fin_cases s <;> decide
  rcases this with h1 | h2
  · left; apply SimpleGraph.Dart.ext; exact Prod.ext h h1
  · right; apply SimpleGraph.Dart.ext; exact Prod.ext h h2

lemma complete_three_darts_two (z : (⊤ : SimpleGraph (Fin 3)).Dart) (h : z.fst = 2) :
    z = complete_three_d20 ∨ z = complete_three_d21 := by
  have hadj : z.fst ≠ z.snd := z.adj
  rw [h] at hadj
  have : z.snd = 0 ∨ z.snd = 1 := by
    revert hadj; generalize z.snd = s; fin_cases s <;> decide
  rcases this with h1 | h2
  · left; apply SimpleGraph.Dart.ext; exact Prod.ext h h1
  · right; apply SimpleGraph.Dart.ext; exact Prod.ext h h2

lemma complete_three_dart_all (z : (⊤ : SimpleGraph (Fin 3)).Dart) :
    z = complete_three_d01 ∨ z = complete_three_d02 ∨
    z = complete_three_d10 ∨ z = complete_three_d12 ∨
    z = complete_three_d20 ∨ z = complete_three_d21 := by
  have : z.fst = 0 ∨ z.fst = 1 ∨ z.fst = 2 := by
    generalize z.fst = f; fin_cases f <;> decide
  rcases this with h | h | h
  · rcases complete_three_darts_zero z h with h1 | h2
    · left; exact h1
    · right; left; exact h2
  · rcases complete_three_darts_one z h with h1 | h2
    · right; right; left; exact h1
    · right; right; right; left; exact h2
  · rcases complete_three_darts_two z h with h1 | h2
    · right; right; right; right; left; exact h1
    · right; right; right; right; right; exact h2

lemma complete_three_sigma_step (σ : Equiv.Perm (⊤ : SimpleGraph (Fin 3)).Dart)
    (hσ : simple_graph_is_rotation_system (⊤ : SimpleGraph (Fin 3)) σ)
    (x y : (⊤ : SimpleGraph (Fin 3)).Dart) (h_fst : y.fst = x.fst) (hne : y ≠ x)
    (h_all : ∀ z : (⊤ : SimpleGraph (Fin 3)).Dart, z.fst = x.fst → z = x ∨ z = y) :
    σ x = y := by
  have h_ne : σ x ≠ x := by
    intro h_fix
    have h_sc : σ.SameCycle x y := hσ.2 x y h_fst.symm
    have h_eq : x = y := h_sc.eq_of_left (Function.IsFixedPt.eq h_fix)
    exact hne h_eq.symm
  have h_tail : (σ x).fst = x.fst := hσ.1 x
  rcases h_all (σ x) h_tail with h1 | h2
  · exact False.elim (h_ne h1)
  · exact h2

lemma complete_three_ne_of_prod {x y : (⊤ : SimpleGraph (Fin 3)).Dart} (h : x.toProd ≠ y.toProd) : x ≠ y := by
  intro h_eq; apply h; rw [h_eq]

lemma complete_three_card_quotient_eq_two {α : Type*} (s : Setoid α) [Fintype (Quotient s)]
    (x y : α) (hne : ¬ x ≈ y) (hcov : ∀ z : α, z ≈ x ∨ z ≈ y) :
    Fintype.card (Quotient s) = 2 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  use ⟦x⟧, ⟦y⟧
  refine ⟨?_, ?_⟩
  · intro h; exact hne (Quotient.exact h)
  · ext q
    simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
    induction' q using Quotient.inductionOn with z
    rcases hcov z with h1 | h2
    · left; exact Quotient.sound h1
    · right; exact Quotient.sound h2

theorem complete_three_rotation_face_count (σ : Equiv.Perm (⊤ : SimpleGraph (Fin 3)).Dart)
    (hσ : simple_graph_is_rotation_system (⊤ : SimpleGraph (Fin 3)) σ) :
    simple_graph_rotation_face_count (⊤ : SimpleGraph (Fin 3)) σ = 2 := by
  let d01 := complete_three_d01
  let d02 := complete_three_d02
  let d10 := complete_three_d10
  let d12 := complete_three_d12
  let d20 := complete_three_d20
  let d21 := complete_three_d21
  have h01_ne : d02 ≠ d01 := complete_three_ne_of_prod (by decide)
  have h02_ne : d01 ≠ d02 := complete_three_ne_of_prod (by decide)
  have h10_ne : d12 ≠ d10 := complete_three_ne_of_prod (by decide)
  have h12_ne : d10 ≠ d12 := complete_three_ne_of_prod (by decide)
  have h20_ne : d21 ≠ d20 := complete_three_ne_of_prod (by decide)
  have h21_ne : d20 ≠ d21 := complete_three_ne_of_prod (by decide)
  have s01 : σ d01 = d02 := complete_three_sigma_step σ hσ d01 d02 rfl h01_ne (fun z hz => complete_three_darts_zero z hz)
  have s02 : σ d02 = d01 := complete_three_sigma_step σ hσ d02 d01 rfl h02_ne (fun z hz => (complete_three_darts_zero z hz).symm)
  have s10 : σ d10 = d12 := complete_three_sigma_step σ hσ d10 d12 rfl h10_ne (fun z hz => complete_three_darts_one z hz)
  have s12 : σ d12 = d10 := complete_three_sigma_step σ hσ d12 d10 rfl h12_ne (fun z hz => (complete_three_darts_one z hz).symm)
  have s20 : σ d20 = d21 := complete_three_sigma_step σ hσ d20 d21 rfl h20_ne (fun z hz => complete_three_darts_two z hz)
  have s21 : σ d21 = d20 := complete_three_sigma_step σ hσ d21 d20 rfl h21_ne (fun z hz => (complete_three_darts_two z hz).symm)
  have y01 : d01.symm = d10 := by apply SimpleGraph.Dart.ext; rfl
  have y02 : d02.symm = d20 := by apply SimpleGraph.Dart.ext; rfl
  have y10 : d10.symm = d01 := by apply SimpleGraph.Dart.ext; rfl
  have y12 : d12.symm = d21 := by apply SimpleGraph.Dart.ext; rfl
  have y20 : d20.symm = d02 := by apply SimpleGraph.Dart.ext; rfl
  have y21 : d21.symm = d12 := by apply SimpleGraph.Dart.ext; rfl
  set F := simple_graph_rotation_face_perm (⊤ : SimpleGraph (Fin 3)) σ
  have f_apply : ∀ d, F d = σ d.symm := fun _ => rfl
  have f01 : F d01 = d12 := by rw [f_apply, y01, s10]
  have f12 : F d12 = d20 := by rw [f_apply, y12, s21]
  have f20 : F d20 = d01 := by rw [f_apply, y20, s02]
  have f10 : F d10 = d02 := by rw [f_apply, y10, s01]
  have f02 : F d02 = d21 := by rw [f_apply, y02, s20]
  have f21 : F d21 = d10 := by rw [f_apply, y21, s12]
  have f2_01 : (F ^ 2) d01 = d20 := by
    change F (F d01) = d20
    rw [f01, f12]
  have f2_10 : (F ^ 2) d10 = d21 := by
    change F (F d10) = d21
    rw [f10, f02]
  let P (x : (⊤ : SimpleGraph (Fin 3)).Dart) : Prop := x = d01 ∨ x = d12 ∨ x = d20
  have hP : ∀ n : ℕ, P ((F ^ n) d01) := by
    intro n
    induction n with
    | zero => left; rfl
    | succ n ih =>
      rcases ih with h | h | h
      · rw [pow_succ', Equiv.Perm.mul_apply, h, f01]
        right; left; rfl
      · rw [pow_succ', Equiv.Perm.mul_apply, h, f12]
        right; right; rfl
      · rw [pow_succ', Equiv.Perm.mul_apply, h, f20]
        left; rfl
  have hne : ¬ (simple_graph_rotation_face_perm (⊤ : SimpleGraph (Fin 3)) σ).SameCycle d01 d10 := by
    intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    have : P d10 := hn ▸ hP n
    rcases this with h | h | h
    · exact (complete_three_ne_of_prod (by decide)) h.symm
    · exact (complete_three_ne_of_prod (by decide)) h.symm
    · exact (complete_three_ne_of_prod (by decide)) h.symm
  have hcov : ∀ z : (⊤ : SimpleGraph (Fin 3)).Dart, F.SameCycle z d01 ∨ F.SameCycle z d10 := by
    intro z
    rcases complete_three_dart_all z with h | h | h | h | h | h
    · left; rw [h]
    · right; rw [h]
      exact Equiv.Perm.SameCycle.symm ⟨1, f10⟩
    · right; rw [h]
    · left; rw [h]
      exact Equiv.Perm.SameCycle.symm ⟨1, f01⟩
    · left; rw [h]
      exact Equiv.Perm.SameCycle.symm ⟨2, f2_01⟩
    · right; rw [h]
      exact Equiv.Perm.SameCycle.symm ⟨2, f2_10⟩
  exact complete_three_card_quotient_eq_two (Equiv.Perm.SameCycle.setoid F) d01 d10 hne hcov
