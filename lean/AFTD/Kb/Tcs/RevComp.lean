import AFTD.Prelude

/-!
# rev_comp

Topic: approximation   Node: c39c002f1c38

Provenance: formalization of a published result. Source: arXiv:2611.16573, Section 2

The reverse complement rc(s) of a string s = a_1…a_m under a complement map cm is cm(a_m)…cm(a_1).
-/

/-- The reverse complement rc(s) of a string: reverse it and complement each letter. -/
def rev_comp {Γ : Type*} (cm : Γ → Γ) (s : List Γ) : List Γ := (s.map cm).reverse
