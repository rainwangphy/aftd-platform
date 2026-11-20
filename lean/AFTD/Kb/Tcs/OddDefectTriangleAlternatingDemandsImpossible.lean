import AFTD.Prelude

/-!
# odd_defect_triangle_alternating_demands_impossible

Topic: graphs   Node: c432eb7115e6

Provenance: helper lemma. OP-874 single-defect local interface obstruction, independently tested in experiment 35103.

The explicit four-color constraints arising from a defect triangle with alternating demands on the defect palette are inconsistent.
-/

theorem odd_defect_triangle_alternating_demands_impossible
    (a b c t u r p q : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hta : t ≠ a) (htb : t ≠ b) (hua : u ≠ a) (hub : u ≠ b) (htu : t ≠ u)
    (hra : r ≠ a) (hrb : r ≠ b) (hrc : r ≠ c)
    (hpa : p ≠ a) (hpc : p ≠ c) (hqa : q ≠ a) (hqc : q ≠ c) (hpq : p ≠ q)
    (hrq : r ≠ q) (hpu : p ≠ u)
    (ht : t = 0 ∨ t = 1) (hd1 : b = 0 ∨ c = 0) (hd2 : c = 1 ∨ a = 1) : False := by
  simp only [Fin.ext_iff] at *
  omega
