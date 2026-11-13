import AFTD.Prelude

/-!
# turan_hypergraph

Topic: combinatorics   Node: fcae81bc1929

Provenance: formalization of a published result. Source: arXiv:2611.16654:378

The balanced 3-partite Turán 3-uniform hypergraph T_n on vertex set Fin n: its edges are all 3-element subsets e of Fin n such that either e meets each residue class modulo 3 in exactly one vertex, or there exists some residue class i modulo 3 such that e has two vertices congruent to i modulo 3 and one vertex congruent to i + 1 modulo 3.
-/

/-- The balanced 3-partite Turán 3-graph T_n on Fin n with residue classes modulo 3. -/
def turan_hypergraph (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter fun (e : Finset (Fin n)) =>
    e.card = 3 ∧
    ((e.image (fun v => (v.val : ZMod 3))).card = 3 ∨
     ∃ i : ZMod 3,
       (e.filter (fun v => (v.val : ZMod 3) = i)).card = 2 ∧
       (e.filter (fun v => (v.val : ZMod 3) = i + 1)).card = 1)
