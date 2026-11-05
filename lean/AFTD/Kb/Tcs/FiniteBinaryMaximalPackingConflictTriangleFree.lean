import AFTD.Prelude

/-!
# finite_binary_maximal_packing_conflict_triangle_free

Topic: graphs   Node: 21edea121999

Provenance: helper lemma. Elementary characteristic-two exchange in the three-packing support argument.

In a finite binary line family covered by a set U, the graph joining two points when their sum lies outside U in the geometry is triangle-free.
-/

theorem finite_binary_maximal_packing_conflict_triangle_free
    (n : ℕ) (S U : Finset (Fin n → ZMod 2))
    (F : Finset (Finset (Fin n → ZMod 2)))
    (hF : ∀ t : Finset (Fin n → ZMod 2),
      t ∈ F ↔ t ⊆ S ∧ t.card = 3 ∧ t.sum id = 0)
    (hcover : ∀ t ∈ F, ¬ Disjoint U t)
    (x y z : Fin n → ZMod 2) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hxyS : x + y ∈ S \ U) (hyzS : y + z ∈ S \ U) (hzxS : z + x ∈ S \ U) :
    False := by
  classical
  have hab : x + y ≠ y + z := by
    intro h
    have h' : y + x = y + z := by simpa [add_comm] using h
    exact hzx (add_left_cancel h').symm
  have hac : x + y ≠ z + x := by
    intro h
    have h' : x + y = x + z := by simpa [add_comm] using h
    exact hyz (add_left_cancel h')
  have hbc : y + z ≠ z + x := by
    intro h
    have h' : z + y = z + x := by simpa [add_comm] using h
    exact hxy (add_left_cancel h').symm
  let T : Finset (Fin n → ZMod 2) := {x+y, y+z, z+x}
  have hsub : T ⊆ S := by
    intro a ha
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact (Finset.mem_sdiff.mp hxyS).1
    · exact (Finset.mem_sdiff.mp hyzS).1
    · exact (Finset.mem_sdiff.mp hzxS).1
  have hcard : T.card = 3 := by simp [T, hab, hac, hbc]
  have hadd0 : ∀ v : Fin n → ZMod 2, v + v = 0 := by
    intro v
    have hh : ∀ a : ZMod 2, a + a = 0 := by decide
    ext i
    exact hh (v i)
  have hsum : T.sum id = 0 := by
    have hval : (x+y)+(y+z)+(z+x) = 0 := by
      calc
        (x+y)+(y+z)+(z+x) = (x+x)+(y+y)+(z+z) := by abel
        _ = 0 := by simp [hadd0]
    simpa [T, hab, hac, hbc, add_assoc] using hval
  have htF : T ∈ F := (hF T).2 ⟨hsub, hcard, hsum⟩
  have hdis : Disjoint U T := by
    apply Finset.disjoint_left.mpr
    intro a haU haT
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at haT
    rcases haT with rfl | rfl | rfl
    · exact (Finset.mem_sdiff.mp hxyS).2 haU
    · exact (Finset.mem_sdiff.mp hyzS).2 haU
    · exact (Finset.mem_sdiff.mp hzxS).2 haU
  exact hcover T htF hdis
