import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidReplacementFromThree

/-!
# wild_valid_triple_exists_in_six

Topic: graphs   Node: 7f49cf17e4b7

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed.

For any array with injective rows and any six distinct vertices, there are three distinct indices satisfying all three triple-validity inequalities. Symmetry, idempotence and finite color type are not needed for this local statement.
-/

set_option maxHeartbeats 4000000

theorem wild_valid_triple_exists_in_six {C : Type*} (A : C → C → C)
    (hinj : ∀ x,Function.Injective (A x)) (v : Fin 6 → C) (hv : Function.Injective v) :
    ∃ i j k : Fin 6,i≠j ∧ i≠k ∧ j≠k ∧
      A (v i) (v j)≠v k ∧ A (v i) (v k)≠v j ∧ A (v j) (v k)≠v i := by
  classical
  by_cases hgood : A (v 0) (v 1)≠v 2 ∧ A (v 0) (v 2)≠v 1 ∧ A (v 1) (v 2)≠v 0
  · exact ⟨0,1,2,by decide,by decide,by decide,hgood⟩
  have hbad : A (v 0) (v 1)=v 2 ∨ A (v 0) (v 2)=v 1 ∨ A (v 1) (v 2)=v 0 := by tauto
  let u : Fin 3 → Fin 6 := fun i => ⟨i.val+3,by omega⟩
  have hu : Function.Injective u := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [u] at h
    omega
  have hw : Function.Injective (v ∘ u) := hv.comp hu
  have hout (z : Fin 6) (hz : z.val<3) : ∀ i,(v ∘ u) i≠v z := by
    intro i h
    have h' := congrArg Fin.val (hv h)
    dsimp [u,Function.comp_def] at h'
    omega
  rcases hbad with h|h|h
  · obtain ⟨i,h1,h2,h3⟩ := wild_valid_replacement_from_three A (v 0) (v 1) (v 2)
      (hinj _) (hinj _) (v ∘ u) hw h (hout 2 (by decide))
    refine ⟨0,1,u i,by decide,?_,?_,h1,h2,h3⟩
    · intro h'
      have hh := congrArg Fin.val h'
      change 0=i.val+3 at hh
      omega
    · intro h'
      have hh := congrArg Fin.val h'
      change 1=i.val+3 at hh
      omega
  · obtain ⟨i,h1,h2,h3⟩ := wild_valid_replacement_from_three A (v 0) (v 2) (v 1)
      (hinj _) (hinj _) (v ∘ u) hw h (hout 1 (by decide))
    refine ⟨0,2,u i,by decide,?_,?_,h1,h2,h3⟩
    · intro h'
      have hh := congrArg Fin.val h'
      change 0=i.val+3 at hh
      omega
    · intro h'
      have hh := congrArg Fin.val h'
      change 2=i.val+3 at hh
      omega
  · obtain ⟨i,h1,h2,h3⟩ := wild_valid_replacement_from_three A (v 1) (v 2) (v 0)
      (hinj _) (hinj _) (v ∘ u) hw h (hout 0 (by decide))
    refine ⟨1,2,u i,by decide,?_,?_,h1,h2,h3⟩
    · intro h'
      have hh := congrArg Fin.val h'
      change 1=i.val+3 at hh
      omega
    · intro h'
      have hh := congrArg Fin.val h'
      change 2=i.val+3 at hh
      omega
