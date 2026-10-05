import AFTD.Prelude

/-!
# poc8_cands

Topic: fair_division   Node: f1c45e631faf

47 vertex bitmasks, each the first part of a connected bipartition of G; together they separate every pair (M1, M2) of disjoint sets with |M1| = 2, |M2| = 3.
-/

/-- 47 connected-bipartition masks covering all (2,3) terminal pairs (found by computer search). -/
def poc8_cands : List ℕ :=
  [35, 21, 73, 14, 146, 164, 137, 70, 208, 49, 42, 28, 224, 67, 133, 116, 184, 202, 50, 76, 131, 81,
    101, 134, 98, 140, 161, 52, 152, 105, 86, 196, 31, 47, 91, 122, 145, 168, 60, 59, 10, 72, 69,
    29, 89, 46, 54]
