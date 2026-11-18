import AFTD.Prelude

/-!
# op861_no_local_source_rule_counterexample

Topic: graphs   Node: 466fea6575e1

Provenance: helper lemma. Finite local-rule synthesis in experiments 30758, 30759, and 30768; compared with the four-vertex longest-path construction in https://korandi.org/docs/domination-3tournaments.pdf.

Six explicit five-vertex acyclic directed graphs refute every ordered-triple source rule: whichever source choice is made for each possible induced ordered triple, one graph uses every vertex as a tail.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def localSourceEdges (i : Fin 6) (x y : Fin 5) : Bool :=
  match i.val with
  | 0 => (x == 1 && y == 3) || (x == 3 && y == 2) || (x == 4 && y == 1)
  | 1 => (x == 0 && y == 4) || (x == 1 && y == 4)
  | 2 => (x == 0 && y == 4) || (x == 4 && y == 2)
  | 3 => (x == 3 && y == 2) || (x == 4 && y == 1)
  | 4 => (x == 2 && y == 4) || (x == 3 && y == 2) || (x == 4 && y == 1)
  | _ => (x == 2 && y == 4) || (x == 3 && y == 4) || (x == 4 && y == 1)

def localSourceRank : Fin 6 → Fin 5 → ℕ :=
  ![![0,1,3,2,0], ![0,0,0,0,1], ![0,0,2,0,1],
    ![0,1,1,0,0], ![0,3,1,0,2], ![0,2,0,0,1]]

def localSourceTriple : Fin 10 → Fin 3 → Fin 5 :=
  ![![0,1,2], ![0,1,3], ![0,1,4], ![0,2,3], ![0,2,4],
    ![0,3,4], ![1,2,3], ![1,2,4], ![1,3,4], ![2,3,4]]

def localSourceEdgeCode (i : Fin 6) (u v : Fin 5) : ℕ :=
  if localSourceEdges i u v then 1 else if localSourceEdges i v u then 2 else 0

def localSourcePattern (i : Fin 6) (j : Fin 10) : ℕ :=
  localSourceEdgeCode i (localSourceTriple j 0) (localSourceTriple j 1) +
  3 * localSourceEdgeCode i (localSourceTriple j 0) (localSourceTriple j 2) +
  9 * localSourceEdgeCode i (localSourceTriple j 1) (localSourceTriple j 2)

def localSourceRule (a : Fin 3) (b c d e f g : Bool) (p : ℕ) : Fin 3 :=
  if p = 0 then a
  else if p = 9 then if b then 0 else 1
  else if p = 18 then if c then 0 else 2
  else if p = 3 then if d then 0 else 1
  else if p = 12 then if e then 0 else 1
  else if p = 6 then if f then 1 else 2
  else if p = 2 then if g then 1 else 2
  else if p = 21 then 0
  else if p = 15 then 1
  else if p = 7 then 2
  else if p = 5 then 1
  else 0

def localSourceTail (a : Fin 3) (b c d e f g : Bool)
    (i : Fin 6) (j : Fin 10) : Fin 5 :=
  localSourceTriple j (localSourceRule a b c d e f g (localSourcePattern i j))

theorem op861_no_local_source_rule_counterexample :
    (∀ i x y, localSourceEdges i x y = true → localSourceRank i x < localSourceRank i y) ∧
    (∀ a : Fin 3, ∀ b c d e f g : Bool,
      (∀ i j z, localSourceEdges i (localSourceTriple j z) (localSourceTail a b c d e f g i j) = false) ∧
      ∃ i : Fin 6, ∀ v : Fin 5, ∃ j : Fin 10, localSourceTail a b c d e f g i j = v) := by
  constructor
  · decide
  · intro a b
    fin_cases a <;> cases b <;> decide
