import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsPlaneRotationSystem
import AFTD.Kb.Tcs.SimpleGraphIsRotationSystem
import AFTD.Kb.Tcs.SimpleGraphRotationFaceCount
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm

/-!
# exists_plane_rotation_system_complete_four

Topic: graphs   Node: ef787f8feb9a

Provenance: helper lemma. Sanity lemma for simple_graph_is_plane_rotation_system (OP-541)

K_4 has a plane rotation system: 4 vertices, 6 edges, 4 faces (sanity check of simple_graph_is_plane_rotation_system).
-/

open SimpleGraph

private def exists_plane_rotation_system_complete_four_next : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 3, 1, 2], ![2, 1, 3, 0], ![3, 0, 2, 1], ![1, 2, 0, 3]]

private def exists_plane_rotation_system_complete_four_rot
    (d : (⊤ : SimpleGraph (Fin 4)).Dart) : (⊤ : SimpleGraph (Fin 4)).Dart :=
  ⟨(d.fst, exists_plane_rotation_system_complete_four_next d.fst d.snd), by
    have hd : d.fst ≠ d.snd := d.adj
    revert hd
    generalize d.fst = u
    generalize d.snd = v
    fin_cases u <;> fin_cases v <;> decide⟩

private noncomputable def exists_plane_rotation_system_complete_four_sigma :
    Equiv.Perm (⊤ : SimpleGraph (Fin 4)).Dart :=
  Equiv.ofBijective exists_plane_rotation_system_complete_four_rot (by decide)

private def exists_plane_rotation_system_complete_four_face_idx : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 2], ![2, 1, 0, 3], ![0, 3, 2, 1], ![1, 2, 3, 3]]

private def exists_plane_rotation_system_complete_four_rep :
    Fin 4 → (⊤ : SimpleGraph (Fin 4)).Dart :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩, ⟨(1, 3), by decide⟩]

private noncomputable abbrev exists_plane_rotation_system_complete_four_face :
    Equiv.Perm (⊤ : SimpleGraph (Fin 4)).Dart :=
  simple_graph_rotation_face_perm (⊤ : SimpleGraph (Fin 4))
    exists_plane_rotation_system_complete_four_sigma

private lemma exists_plane_rotation_system_complete_four_face_idx_apply :
    ∀ d : (⊤ : SimpleGraph (Fin 4)).Dart,
      exists_plane_rotation_system_complete_four_face_idx
          (exists_plane_rotation_system_complete_four_face d).fst
          (exists_plane_rotation_system_complete_four_face d).snd
        = exists_plane_rotation_system_complete_four_face_idx d.fst d.snd := by
  decide

private lemma exists_plane_rotation_system_complete_four_face_idx_rep :
    ∀ i : Fin 4,
      exists_plane_rotation_system_complete_four_face_idx
          (exists_plane_rotation_system_complete_four_rep i).fst
          (exists_plane_rotation_system_complete_four_rep i).snd = i := by
  decide

private lemma exists_plane_rotation_system_complete_four_cover :
    ∀ d : (⊤ : SimpleGraph (Fin 4)).Dart,
      d = exists_plane_rotation_system_complete_four_rep
            (exists_plane_rotation_system_complete_four_face_idx d.fst d.snd) ∨
      exists_plane_rotation_system_complete_four_face d
        = exists_plane_rotation_system_complete_four_rep
            (exists_plane_rotation_system_complete_four_face_idx d.fst d.snd) ∨
      exists_plane_rotation_system_complete_four_face
          (exists_plane_rotation_system_complete_four_face d)
        = exists_plane_rotation_system_complete_four_rep
            (exists_plane_rotation_system_complete_four_face_idx d.fst d.snd) := by
  decide

private lemma exists_plane_rotation_system_complete_four_rot_cover :
    ∀ d e : (⊤ : SimpleGraph (Fin 4)).Dart, d.fst = e.fst →
      e = d ∨ e = exists_plane_rotation_system_complete_four_sigma d ∨
        e = exists_plane_rotation_system_complete_four_sigma
          (exists_plane_rotation_system_complete_four_sigma d) := by
  decide

private lemma exists_plane_rotation_system_complete_four_is_rotation_system :
    simple_graph_is_rotation_system (⊤ : SimpleGraph (Fin 4))
      exists_plane_rotation_system_complete_four_sigma := by
  constructor
  · intro d; rfl
  · intro d e h
    obtain rfl | h | h := exists_plane_rotation_system_complete_four_rot_cover d e h
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact (h.symm.sameCycle exists_plane_rotation_system_complete_four_sigma).of_apply_left
    · exact ((h.symm.sameCycle
        exists_plane_rotation_system_complete_four_sigma).of_apply_left).of_apply_left

private lemma exists_plane_rotation_system_complete_four_face_idx_eq_of_sameCycle
    {a b : (⊤ : SimpleGraph (Fin 4)).Dart}
    (h : (exists_plane_rotation_system_complete_four_face).SameCycle a b) :
    exists_plane_rotation_system_complete_four_face_idx a.fst a.snd
      = exists_plane_rotation_system_complete_four_face_idx b.fst b.snd := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  clear h
  subst hn
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        exists_plane_rotation_system_complete_four_face_idx_apply]
      exact ih

private lemma exists_plane_rotation_system_complete_four_sameCycle_rep
    (d : (⊤ : SimpleGraph (Fin 4)).Dart) :
    (exists_plane_rotation_system_complete_four_face).SameCycle d
      (exists_plane_rotation_system_complete_four_rep
        (exists_plane_rotation_system_complete_four_face_idx d.fst d.snd)) := by
  obtain h | h | h := exists_plane_rotation_system_complete_four_cover d
  · exact h.sameCycle exists_plane_rotation_system_complete_four_face
  · exact (h.sameCycle exists_plane_rotation_system_complete_four_face).of_apply_left
  · exact ((h.sameCycle
      exists_plane_rotation_system_complete_four_face).of_apply_left).of_apply_left

private noncomputable def exists_plane_rotation_system_complete_four_face_to_fun :
    Quotient (Equiv.Perm.SameCycle.setoid exists_plane_rotation_system_complete_four_face)
      → Fin 4 :=
  Quotient.lift (fun d => exists_plane_rotation_system_complete_four_face_idx d.fst d.snd)
    (fun _ _ hab => exists_plane_rotation_system_complete_four_face_idx_eq_of_sameCycle hab)

private noncomputable def exists_plane_rotation_system_complete_four_face_inv_fun :
    Fin 4 → Quotient (Equiv.Perm.SameCycle.setoid exists_plane_rotation_system_complete_four_face) :=
  fun i => Quotient.mk _ (exists_plane_rotation_system_complete_four_rep i)

private lemma exists_plane_rotation_system_complete_four_face_left_inv :
    Function.LeftInverse exists_plane_rotation_system_complete_four_face_inv_fun
      exists_plane_rotation_system_complete_four_face_to_fun := by
  intro q
  induction q using Quotient.inductionOn with
  | h d => exact Quotient.sound (exists_plane_rotation_system_complete_four_sameCycle_rep d).symm

private lemma exists_plane_rotation_system_complete_four_face_right_inv :
    Function.RightInverse exists_plane_rotation_system_complete_four_face_inv_fun
      exists_plane_rotation_system_complete_four_face_to_fun := by
  intro i
  exact exists_plane_rotation_system_complete_four_face_idx_rep i

private lemma exists_plane_rotation_system_complete_four_face_card :
    Fintype.card (Quotient
      (Equiv.Perm.SameCycle.setoid exists_plane_rotation_system_complete_four_face)) = 4 := by
  have e : Quotient
      (Equiv.Perm.SameCycle.setoid exists_plane_rotation_system_complete_four_face) ≃ Fin 4 :=
    ⟨exists_plane_rotation_system_complete_four_face_to_fun,
     exists_plane_rotation_system_complete_four_face_inv_fun,
     exists_plane_rotation_system_complete_four_face_left_inv,
     exists_plane_rotation_system_complete_four_face_right_inv⟩
  rw [Fintype.card_congr e, Fintype.card_fin]

private lemma exists_plane_rotation_system_complete_four_face_count :
    simple_graph_rotation_face_count (⊤ : SimpleGraph (Fin 4))
      exists_plane_rotation_system_complete_four_sigma = 4 := by
  unfold simple_graph_rotation_face_count
  exact exists_plane_rotation_system_complete_four_face_card

theorem exists_plane_rotation_system_complete_four :
    ∃ σ : Equiv.Perm (⊤ : SimpleGraph (Fin 4)).Dart,
      simple_graph_is_plane_rotation_system (⊤ : SimpleGraph (Fin 4)) σ := by
  refine ⟨exists_plane_rotation_system_complete_four_sigma, connected_top,
    exists_plane_rotation_system_complete_four_is_rotation_system, ?_⟩
  rw [exists_plane_rotation_system_complete_four_face_count]
  have hedge : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
  rw [hedge]
  norm_num
