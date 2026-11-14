import AFTD.Prelude

/-!
# digraph_oriented_regular_cut20_extension

Topic: graphs   Node: 94218c13f976

Provenance: helper lemma. Finite construction and checks in experiment 26337.

An explicit strongly connected 104-vertex extension of the oriented 20-cut example using twelve seven-vertex regular tournaments.
-/

def digraph_oriented_regular_cut20_extension : Digraph (Fin 104) := ⟨fun u v =>
  (u.val < 5 ∧ (v.val < u.val ∨ v.val = 5 ∨ (20 ≤ v.val ∧ u.val + v.val < 26))) ∨
  (u.val = 5 ∧ 13 ≤ v.val ∧ v.val < 20) ∨
  (6 ≤ u.val ∧ u.val < 13 ∧ (v.val < 6 ∨ v.val = 6 + (u.val - 6 + 1) % 7)) ∨
  (13 ≤ u.val ∧ u.val < 20 ∧ ((13 ≤ v.val ∧ v.val < u.val) ∨ (6 ≤ v.val ∧ u.val + v.val < 26))) ∨
  (20 ≤ u.val ∧ 20 ≤ v.val ∧ (u.val - 20) / 7 = (v.val - 20) / 7 ∧
    (v.val + 7 - u.val) % 7 ∈ ({1,2,4} : Finset ℕ)) ∨
  (20 ≤ u.val ∧ (let k := (u.val - 20) / 7;
    (k < 7 ∧ (v.val = 5 ∨ v.val = 13 + k ∨ v.val = 12 - k ∨ v.val = 20 + 7 * ((k + 1) % 12))) ∨
    (7 ≤ k ∧ k < 11 ∧ (v.val = k - 7 ∨ v.val = 32 - k ∨ v.val = 5 ∨ v.val = 20 + 7 * ((k + 1) % 12))) ∨
    (k = 11 ∧ (v.val = 4 ∨ v.val = 20 ∨ v.val = 21 ∨ v.val = 26))))⟩
