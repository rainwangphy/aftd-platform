import AFTD.Prelude

/-!
# op309_ten_cubic_star_selection_boolean_kernel

Topic: graphs   Node: 447da202ecb9

Provenance: helper lemma. OP-309; finite selected-edge obstruction for the ten-vertex graph, experiment 42028.

For the fifteen labeled edges of the specified ten-vertex graph, any Boolean selected-edge mask that totally dominates every edge and contains no selected triangle or three-edge path contains one of the twelve listed small masks.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem in1237_bridge_lobe_left (b0 b1 b2 b9 b10 b12 b13 : Bool)
  (hd : (b1 = true ∨ b2 = true ∨ b12 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b9 = true ∨ b12 = true) ∧
    (b0 = true ∨ b1 = true ∨ b10 = true ∨ b13 = true) ∧
    (b0 = true ∨ b1 = true ∨ b9 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b10 = true ∨ b12 = true))
  (hp : ¬ (b0 = true ∧ b1 = true ∧ b9 = true) ∧
    ¬ (b0 = true ∧ b1 = true ∧ b13 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b9 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b9 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b2 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b2 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b12 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b9 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b10 = true ∧ b12 = true ∧ b13 = true))
  (hn : ¬ (b0 = true ∧ b2 = true ∧ b9 = true) ∧
    ¬ (b0 = true ∧ b1 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b10 = true ∧ b12 = true) ∧
    ¬ (b2 = true ∧ b13 = true) ∧
    ¬ (b0 = true ∧ b9 = true ∧ b13 = true)) :
  ¬ b9 = true ∧ ¬ b10 = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b9 <;> cases b10 <;> cases b12 <;> cases b13 <;> simp_all

private theorem in1237_bridge_lobe_right (b3 b4 b5 b6 b7 b8 b14 : Bool)
  (hd : (b4 = true ∨ b5 = true ∨ b6 = true ∨ b14 = true) ∧
    (b3 = true ∨ b4 = true ∨ b8 = true ∨ b14 = true) ∧
    (b3 = true ∨ b7 = true ∨ b8 = true ∨ b14 = true) ∧
    (b5 = true ∨ b6 = true ∨ b7 = true ∨ b14 = true) ∧
    (b3 = true ∨ b5 = true ∨ b6 = true ∨ b8 = true))
  (hp : ¬ (b3 = true ∧ b4 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b14 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b8 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b14 = true) ∧
    ¬ (b5 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b6 = true ∧ b7 = true ∧ b14 = true) ∧
    ¬ (b7 = true ∧ b8 = true ∧ b14 = true))
  (hn : ¬ (b3 = true ∧ b5 = true) ∧
    ¬ (b6 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b6 = true ∧ b14 = true) ∧
    ¬ (b3 = true ∧ b7 = true ∧ b14 = true) ∧
    ¬ (b5 = true ∧ b7 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b8 = true ∧ b14 = true)) :
  ¬ b4 = true ∧ ¬ b7 = true := by
  cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b14 <;> simp_all

theorem op309_ten_cubic_star_selection_boolean_kernel (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool)
  (hdom : (b1 = true ∨ b2 = true ∨ b12 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b9 = true ∨ b12 = true) ∧
    (b0 = true ∨ b1 = true ∨ b10 = true ∨ b13 = true) ∧
    (b4 = true ∨ b5 = true ∨ b6 = true ∨ b14 = true) ∧
    (b3 = true ∨ b5 = true ∨ b7 = true ∨ b11 = true) ∧
    (b3 = true ∨ b4 = true ∨ b8 = true ∨ b14 = true) ∧
    (b3 = true ∨ b7 = true ∨ b8 = true ∨ b14 = true) ∧
    (b4 = true ∨ b6 = true ∨ b8 = true ∨ b11 = true) ∧
    (b5 = true ∨ b6 = true ∨ b7 = true ∨ b14 = true) ∧
    (b1 = true ∨ b10 = true ∨ b11 = true ∨ b12 = true) ∧
    (b2 = true ∨ b9 = true ∨ b11 = true ∨ b13 = true) ∧
    (b4 = true ∨ b7 = true ∨ b9 = true ∨ b10 = true) ∧
    (b0 = true ∨ b1 = true ∨ b9 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b10 = true ∨ b12 = true) ∧
    (b3 = true ∨ b5 = true ∨ b6 = true ∨ b8 = true))
  (htri : ¬ (b0 = true ∧ b1 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b13 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b14 = true) ∧
    ¬ (b6 = true ∧ b8 = true ∧ b14 = true))
  (hpath : ¬ (b0 = true ∧ b1 = true ∧ b9 = true) ∧
    ¬ (b0 = true ∧ b1 = true ∧ b13 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b9 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b9 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b1 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b2 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b2 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b2 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b11 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b14 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b8 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b11 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b4 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b14 = true) ∧
    ¬ (b5 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b6 = true ∧ b7 = true ∧ b11 = true) ∧
    ¬ (b6 = true ∧ b7 = true ∧ b14 = true) ∧
    ¬ (b7 = true ∧ b8 = true ∧ b11 = true) ∧
    ¬ (b7 = true ∧ b8 = true ∧ b14 = true) ∧
    ¬ (b7 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b7 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b12 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b9 = true ∧ b11 = true ∧ b12 = true) ∧
    ¬ (b9 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b10 = true ∧ b11 = true ∧ b13 = true) ∧
    ¬ (b10 = true ∧ b12 = true ∧ b13 = true)) :
    (b3 = true ∧ b5 = true) ∨
    (b6 = true ∧ b8 = true) ∨
    (b0 = true ∧ b2 = true ∧ b9 = true) ∨
    (b0 = true ∧ b1 = true ∧ b10 = true) ∨
    (b1 = true ∧ b12 = true) ∨
    (b0 = true ∧ b10 = true ∧ b12 = true) ∨
    (b2 = true ∧ b13 = true) ∨
    (b0 = true ∧ b9 = true ∧ b13 = true) ∨
    (b4 = true ∧ b6 = true ∧ b14 = true) ∨
    (b3 = true ∧ b7 = true ∧ b14 = true) ∨
    (b5 = true ∧ b7 = true ∧ b14 = true) ∨
    (b4 = true ∧ b8 = true ∧ b14 = true) := by
  by_contra hno
  have n0 : ¬ (b3 = true ∧ b5 = true) := by
    intro h
    exact hno (Or.inl h)
  have n1 : ¬ (b6 = true ∧ b8 = true) := by
    intro h
    exact hno (Or.inr (Or.inl h))
  have n2 : ¬ (b0 = true ∧ b2 = true ∧ b9 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inl h)))
  have n3 : ¬ (b0 = true ∧ b1 = true ∧ b10 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have n4 : ¬ (b1 = true ∧ b12 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have n5 : ¬ (b0 = true ∧ b10 = true ∧ b12 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have n6 : ¬ (b2 = true ∧ b13 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have n7 : ¬ (b0 = true ∧ b9 = true ∧ b13 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have n8 : ¬ (b4 = true ∧ b6 = true ∧ b14 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  have n9 : ¬ (b3 = true ∧ b7 = true ∧ b14 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
  have n10 : ¬ (b5 = true ∧ b7 = true ∧ b14 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
  have n11 : ¬ (b4 = true ∧ b8 = true ∧ b14 = true) := by
    intro h
    exact hno (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))))))
  rcases hdom with ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩
  rcases hpath with ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43, p44, p45, p46, p47⟩
  have hleft := in1237_bridge_lobe_left b0 b1 b2 b9 b10 b12 b13 ⟨d0, d1, d2, d12, d13⟩ ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p12, p13, p15, p42, p43, p45, p47⟩ ⟨n2, n3, n4, n5, n6, n7⟩
  have hright := in1237_bridge_lobe_right b3 b4 b5 b6 b7 b8 b14 ⟨d3, d5, d6, d8, d14⟩ ⟨p16, p17, p19, p20, p21, p22, p23, p24, p25, p26, p28, p29, p30, p33, p34, p35, p37, p39⟩ ⟨n0, n1, n8, n9, n10, n11⟩
  rcases hleft with ⟨hl9, hl10⟩
  rcases hright with ⟨hr4, hr7⟩
  rcases d11 with h | h | h | h
  · exact hr4 h
  · exact hr7 h
  · exact hl9 h
  · exact hl10 h
