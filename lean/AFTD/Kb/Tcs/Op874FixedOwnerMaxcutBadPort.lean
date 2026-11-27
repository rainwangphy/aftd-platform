import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FixedOwnerBooleanCore

/-!
# op874_fixed_owner_maxcut_bad_port

Topic: graphs   Node: daa0eb568ed1

Provenance: helper lemma. Fixed-ownership port obstruction for the global-pair route to OP-874; experiments 43171–43178.

For the explicit fourteen-vertex cubic graph, matching, matching bits and low-port owners in the statement, every compatible six-color local state using the common pair 2 and 3 on unowned factor edges has neither color 2 nor color 3 at the specified exposed port of vertex 6. The corresponding matching cut is a mixed global maximum; that graph property is a separate finite verification.
-/

namespace IN1258Bridge
def L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
def R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
def ends (e : Fin 21) : Sym2 (Fin 14) := s(L e,R e)
def M : Finset (Fin 21) := {2,3,7,10,13,17,18}
def bit : Fin 14 → Bool := ![false,true,true,true,true,false,false,false,false,true,false,false,false,true]
def own : Fin 14 → Fin 21 := ![1,4,8,9,3,13,16,6,18,7,2,17,14,10]

private theorem six_exhaust (x : Fin 6) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  fin_cases x <;> simp

def val (c : Fin 21 → Fin 6) (h : Fin 14 → Fin 21 → Fin 6) : Sat.Valuation
  | 0 => c 3 = (1 : Fin 6)
  | 1 => c 4 = (0 : Fin 6)
  | 2 => c 4 = (1 : Fin 6)
  | 3 => c 4 = (2 : Fin 6)
  | 4 => c 4 = (3 : Fin 6)
  | 5 => c 4 = (4 : Fin 6)
  | 6 => c 4 = (5 : Fin 6)
  | 7 => c 5 = (2 : Fin 6)
  | 8 => c 5 = (3 : Fin 6)
  | 9 => c 7 = (1 : Fin 6)
  | 10 => c 10 = (1 : Fin 6)
  | 11 => c 11 = (2 : Fin 6)
  | 12 => c 11 = (3 : Fin 6)
  | 13 => c 12 = (2 : Fin 6)
  | 14 => c 12 = (3 : Fin 6)
  | 15 => c 13 = (0 : Fin 6)
  | 16 => c 15 = (2 : Fin 6)
  | 17 => c 15 = (3 : Fin 6)
  | 18 => c 16 = (0 : Fin 6)
  | 19 => c 16 = (1 : Fin 6)
  | 20 => c 16 = (2 : Fin 6)
  | 21 => c 16 = (3 : Fin 6)
  | 22 => c 16 = (4 : Fin 6)
  | 23 => c 16 = (5 : Fin 6)
  | 24 => c 17 = (0 : Fin 6)
  | 25 => c 18 = (0 : Fin 6)
  | 26 => c 19 = (2 : Fin 6)
  | 27 => c 19 = (3 : Fin 6)
  | 28 => c 20 = (2 : Fin 6)
  | 29 => c 20 = (3 : Fin 6)
  | 30 => h 1 4 = (0 : Fin 6)
  | 31 => h 1 5 = (0 : Fin 6)
  | 32 => h 1 5 = (1 : Fin 6)
  | 33 => h 1 5 = (2 : Fin 6)
  | 34 => h 1 5 = (3 : Fin 6)
  | 35 => h 1 5 = (4 : Fin 6)
  | 36 => h 1 5 = (5 : Fin 6)
  | 37 => h 1 3 = (0 : Fin 6)
  | 38 => h 1 3 = (1 : Fin 6)
  | 39 => h 1 3 = (2 : Fin 6)
  | 40 => h 1 3 = (3 : Fin 6)
  | 41 => h 1 3 = (4 : Fin 6)
  | 42 => h 1 3 = (5 : Fin 6)
  | 43 => h 2 8 = (0 : Fin 6)
  | 44 => h 3 9 = (0 : Fin 6)
  | 45 => h 4 11 = (0 : Fin 6)
  | 46 => h 4 11 = (1 : Fin 6)
  | 47 => h 4 11 = (2 : Fin 6)
  | 48 => h 4 11 = (3 : Fin 6)
  | 49 => h 4 11 = (4 : Fin 6)
  | 50 => h 4 11 = (5 : Fin 6)
  | 51 => h 4 12 = (0 : Fin 6)
  | 52 => h 4 12 = (1 : Fin 6)
  | 53 => h 4 12 = (2 : Fin 6)
  | 54 => h 4 12 = (3 : Fin 6)
  | 55 => h 4 12 = (4 : Fin 6)
  | 56 => h 4 12 = (5 : Fin 6)
  | 57 => h 5 13 = (1 : Fin 6)
  | 58 => h 5 4 = (0 : Fin 6)
  | 59 => h 5 4 = (1 : Fin 6)
  | 60 => h 5 4 = (2 : Fin 6)
  | 61 => h 5 4 = (3 : Fin 6)
  | 62 => h 5 4 = (4 : Fin 6)
  | 63 => h 5 4 = (5 : Fin 6)
  | 64 => h 6 13 = (0 : Fin 6)
  | 65 => h 6 13 = (1 : Fin 6)
  | 66 => h 6 13 = (2 : Fin 6)
  | 67 => h 6 13 = (3 : Fin 6)
  | 68 => h 6 13 = (4 : Fin 6)
  | 69 => h 6 13 = (5 : Fin 6)
  | 70 => h 6 16 = (1 : Fin 6)
  | 71 => h 6 16 = (2 : Fin 6)
  | 72 => h 6 16 = (3 : Fin 6)
  | 73 => h 6 15 = (2 : Fin 6)
  | 74 => h 6 15 = (3 : Fin 6)
  | 75 => h 7 6 = (1 : Fin 6)
  | 76 => h 8 18 = (1 : Fin 6)
  | 77 => h 8 11 = (0 : Fin 6)
  | 78 => h 8 11 = (1 : Fin 6)
  | 79 => h 8 11 = (2 : Fin 6)
  | 80 => h 8 11 = (3 : Fin 6)
  | 81 => h 8 11 = (4 : Fin 6)
  | 82 => h 8 11 = (5 : Fin 6)
  | 83 => h 8 5 = (0 : Fin 6)
  | 84 => h 8 5 = (1 : Fin 6)
  | 85 => h 8 5 = (2 : Fin 6)
  | 86 => h 8 5 = (3 : Fin 6)
  | 87 => h 8 5 = (4 : Fin 6)
  | 88 => h 8 5 = (5 : Fin 6)
  | 89 => h 9 19 = (0 : Fin 6)
  | 90 => h 9 19 = (1 : Fin 6)
  | 91 => h 9 19 = (2 : Fin 6)
  | 92 => h 9 19 = (3 : Fin 6)
  | 93 => h 9 19 = (4 : Fin 6)
  | 94 => h 9 19 = (5 : Fin 6)
  | 95 => h 9 15 = (0 : Fin 6)
  | 96 => h 9 15 = (1 : Fin 6)
  | 97 => h 9 15 = (2 : Fin 6)
  | 98 => h 9 15 = (3 : Fin 6)
  | 99 => h 9 15 = (4 : Fin 6)
  | 100 => h 9 15 = (5 : Fin 6)
  | 101 => h 11 12 = (0 : Fin 6)
  | 102 => h 11 12 = (1 : Fin 6)
  | 103 => h 11 12 = (2 : Fin 6)
  | 104 => h 11 12 = (3 : Fin 6)
  | 105 => h 11 12 = (4 : Fin 6)
  | 106 => h 11 12 = (5 : Fin 6)
  | 107 => h 11 20 = (0 : Fin 6)
  | 108 => h 11 20 = (1 : Fin 6)
  | 109 => h 11 20 = (2 : Fin 6)
  | 110 => h 11 20 = (3 : Fin 6)
  | 111 => h 11 20 = (4 : Fin 6)
  | 112 => h 11 20 = (5 : Fin 6)
  | 113 => h 12 18 = (0 : Fin 6)
  | 114 => h 12 18 = (1 : Fin 6)
  | 115 => h 12 18 = (2 : Fin 6)
  | 116 => h 12 18 = (3 : Fin 6)
  | 117 => h 12 18 = (4 : Fin 6)
  | 118 => h 12 18 = (5 : Fin 6)
  | 119 => h 12 19 = (0 : Fin 6)
  | 120 => h 12 19 = (1 : Fin 6)
  | 121 => h 12 19 = (2 : Fin 6)
  | 122 => h 12 19 = (3 : Fin 6)
  | 123 => h 12 19 = (4 : Fin 6)
  | 124 => h 12 19 = (5 : Fin 6)
  | 125 => h 13 20 = (0 : Fin 6)
  | 126 => h 13 20 = (1 : Fin 6)
  | 127 => h 13 20 = (2 : Fin 6)
  | 128 => h 13 20 = (3 : Fin 6)
  | 129 => h 13 20 = (4 : Fin 6)
  | 130 => h 13 20 = (5 : Fin 6)
  | 131 => h 13 16 = (0 : Fin 6)
  | 132 => h 13 16 = (1 : Fin 6)
  | 133 => h 13 16 = (2 : Fin 6)
  | 134 => h 13 16 = (3 : Fin 6)
  | 135 => h 13 16 = (4 : Fin 6)
  | 136 => h 13 16 = (5 : Fin 6)
  | _ => False

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_owner_bad_port
    (c : Fin 21 → Fin 6) (h : Fin 14 → Fin 21 → Fin 6)
    (hc : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f)
    (hh : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f)
    (hn : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f)
    (hs : ∀ e f g, L e ∈ ends f → R e ∈ ends g → f ≠ e → g ≠ e → h (L e) f ≠ h (R e) g)
    (hm : ∀ e ∈ M, c e = if bit (L e) then 1 else 0)
    (hf : ∀ e ∉ M, 2 ≤ (c e).val)
    (ho : ∀ v : Fin 14, h v (own v) = if bit v then 0 else 1)
    (hg : ∀ e ∉ M, e ≠ own (L e) → e ≠ own (R e) → c e = 2 ∨ c e = 3) :
    h 6 15 ≠ 2 ∧ h 6 15 ≠ 3 := by
  classical
  by_contra ht
  push_neg at ht
  have ht' : h 6 15 = 2 ∨ h 6 15 = 3 := by
    by_cases h2 : h 6 15 = 2
    · exact Or.inl h2
    · exact Or.inr (ht h2)
  have hsat : (val c h).satisfies_fmla [[Sat.Literal.pos 1,Sat.Literal.pos 2,Sat.Literal.pos 3,Sat.Literal.pos 4,Sat.Literal.pos 5,Sat.Literal.pos 6],[Sat.Literal.pos 18,Sat.Literal.pos 19,Sat.Literal.pos 20,Sat.Literal.pos 21,Sat.Literal.pos 22,Sat.Literal.pos 23],[Sat.Literal.pos 31,Sat.Literal.pos 32,Sat.Literal.pos 33,Sat.Literal.pos 34,Sat.Literal.pos 35,Sat.Literal.pos 36],[Sat.Literal.pos 37,Sat.Literal.pos 38,Sat.Literal.pos 39,Sat.Literal.pos 40,Sat.Literal.pos 41,Sat.Literal.pos 42],[Sat.Literal.neg 30,Sat.Literal.neg 31],[Sat.Literal.neg 30,Sat.Literal.neg 37],[Sat.Literal.neg 32,Sat.Literal.neg 0],[Sat.Literal.neg 38,Sat.Literal.neg 0],[Sat.Literal.neg 2,Sat.Literal.neg 0],[Sat.Literal.neg 33,Sat.Literal.neg 39],[Sat.Literal.neg 33,Sat.Literal.neg 3],[Sat.Literal.neg 33,Sat.Literal.neg 7],[Sat.Literal.neg 39,Sat.Literal.neg 3],[Sat.Literal.neg 39,Sat.Literal.neg 7],[Sat.Literal.neg 3,Sat.Literal.neg 7],[Sat.Literal.neg 34,Sat.Literal.neg 40],[Sat.Literal.neg 34,Sat.Literal.neg 4],[Sat.Literal.neg 34,Sat.Literal.neg 8],[Sat.Literal.neg 40,Sat.Literal.neg 4],[Sat.Literal.neg 40,Sat.Literal.neg 8],[Sat.Literal.neg 4,Sat.Literal.neg 8],[Sat.Literal.neg 35,Sat.Literal.neg 41],[Sat.Literal.neg 35,Sat.Literal.neg 5],[Sat.Literal.neg 41,Sat.Literal.neg 5],[Sat.Literal.neg 42,Sat.Literal.neg 6],[Sat.Literal.pos 45,Sat.Literal.pos 46,Sat.Literal.pos 47,Sat.Literal.pos 48,Sat.Literal.pos 49,Sat.Literal.pos 50],[Sat.Literal.pos 51,Sat.Literal.pos 52,Sat.Literal.pos 53,Sat.Literal.pos 54,Sat.Literal.pos 55,Sat.Literal.pos 56],[Sat.Literal.neg 46,Sat.Literal.neg 0],[Sat.Literal.neg 52,Sat.Literal.neg 0],[Sat.Literal.neg 47,Sat.Literal.neg 11],[Sat.Literal.neg 47,Sat.Literal.neg 13],[Sat.Literal.neg 53,Sat.Literal.neg 11],[Sat.Literal.neg 53,Sat.Literal.neg 13],[Sat.Literal.neg 11,Sat.Literal.neg 13],[Sat.Literal.neg 48,Sat.Literal.neg 12],[Sat.Literal.neg 48,Sat.Literal.neg 14],[Sat.Literal.neg 54,Sat.Literal.neg 12],[Sat.Literal.neg 54,Sat.Literal.neg 14],[Sat.Literal.neg 12,Sat.Literal.neg 14],[Sat.Literal.neg 49,Sat.Literal.neg 55],[Sat.Literal.neg 50,Sat.Literal.neg 56],[Sat.Literal.pos 58,Sat.Literal.pos 59,Sat.Literal.pos 60,Sat.Literal.pos 61,Sat.Literal.pos 62,Sat.Literal.pos 63],[Sat.Literal.neg 58,Sat.Literal.neg 15],[Sat.Literal.neg 15,Sat.Literal.neg 1],[Sat.Literal.neg 62,Sat.Literal.neg 5],[Sat.Literal.neg 63,Sat.Literal.neg 6],[Sat.Literal.pos 64,Sat.Literal.pos 65,Sat.Literal.pos 66,Sat.Literal.pos 67,Sat.Literal.pos 68,Sat.Literal.pos 69],[Sat.Literal.neg 64,Sat.Literal.neg 15],[Sat.Literal.neg 15,Sat.Literal.neg 18],[Sat.Literal.neg 65,Sat.Literal.neg 70],[Sat.Literal.neg 66,Sat.Literal.neg 71],[Sat.Literal.neg 66,Sat.Literal.neg 73],[Sat.Literal.neg 66,Sat.Literal.neg 16],[Sat.Literal.neg 71,Sat.Literal.neg 20],[Sat.Literal.neg 71,Sat.Literal.neg 16],[Sat.Literal.neg 73,Sat.Literal.neg 20],[Sat.Literal.neg 73,Sat.Literal.neg 16],[Sat.Literal.neg 20,Sat.Literal.neg 16],[Sat.Literal.neg 67,Sat.Literal.neg 72],[Sat.Literal.neg 67,Sat.Literal.neg 74],[Sat.Literal.neg 67,Sat.Literal.neg 17],[Sat.Literal.neg 72,Sat.Literal.neg 21],[Sat.Literal.neg 72,Sat.Literal.neg 17],[Sat.Literal.neg 74,Sat.Literal.neg 21],[Sat.Literal.neg 74,Sat.Literal.neg 17],[Sat.Literal.neg 21,Sat.Literal.neg 17],[Sat.Literal.neg 68,Sat.Literal.neg 22],[Sat.Literal.neg 69,Sat.Literal.neg 23],[Sat.Literal.pos 77,Sat.Literal.pos 78,Sat.Literal.pos 79,Sat.Literal.pos 80,Sat.Literal.pos 81,Sat.Literal.pos 82],[Sat.Literal.pos 83,Sat.Literal.pos 84,Sat.Literal.pos 85,Sat.Literal.pos 86,Sat.Literal.pos 87,Sat.Literal.pos 88],[Sat.Literal.neg 77,Sat.Literal.neg 25],[Sat.Literal.neg 83,Sat.Literal.neg 25],[Sat.Literal.neg 76,Sat.Literal.neg 78],[Sat.Literal.neg 76,Sat.Literal.neg 84],[Sat.Literal.neg 79,Sat.Literal.neg 11],[Sat.Literal.neg 79,Sat.Literal.neg 7],[Sat.Literal.neg 85,Sat.Literal.neg 11],[Sat.Literal.neg 85,Sat.Literal.neg 7],[Sat.Literal.neg 11,Sat.Literal.neg 7],[Sat.Literal.neg 80,Sat.Literal.neg 12],[Sat.Literal.neg 80,Sat.Literal.neg 8],[Sat.Literal.neg 86,Sat.Literal.neg 12],[Sat.Literal.neg 86,Sat.Literal.neg 8],[Sat.Literal.neg 12,Sat.Literal.neg 8],[Sat.Literal.neg 81,Sat.Literal.neg 87],[Sat.Literal.neg 82,Sat.Literal.neg 88],[Sat.Literal.pos 89,Sat.Literal.pos 90,Sat.Literal.pos 91,Sat.Literal.pos 92,Sat.Literal.pos 93,Sat.Literal.pos 94],[Sat.Literal.neg 91,Sat.Literal.neg 93],[Sat.Literal.pos 95,Sat.Literal.pos 96,Sat.Literal.pos 97,Sat.Literal.pos 98,Sat.Literal.pos 99,Sat.Literal.pos 100],[Sat.Literal.neg 90,Sat.Literal.neg 9],[Sat.Literal.neg 96,Sat.Literal.neg 9],[Sat.Literal.neg 91,Sat.Literal.neg 97],[Sat.Literal.neg 91,Sat.Literal.neg 26],[Sat.Literal.neg 91,Sat.Literal.neg 16],[Sat.Literal.neg 97,Sat.Literal.neg 26],[Sat.Literal.neg 97,Sat.Literal.neg 16],[Sat.Literal.neg 26,Sat.Literal.neg 16],[Sat.Literal.neg 92,Sat.Literal.neg 27],[Sat.Literal.neg 92,Sat.Literal.neg 17],[Sat.Literal.neg 98,Sat.Literal.neg 27],[Sat.Literal.neg 98,Sat.Literal.neg 17],[Sat.Literal.neg 27,Sat.Literal.neg 17],[Sat.Literal.neg 93,Sat.Literal.neg 99],[Sat.Literal.neg 94,Sat.Literal.neg 100],[Sat.Literal.pos 101,Sat.Literal.pos 102,Sat.Literal.pos 103,Sat.Literal.pos 104,Sat.Literal.pos 105,Sat.Literal.pos 106],[Sat.Literal.pos 107,Sat.Literal.pos 108,Sat.Literal.pos 109,Sat.Literal.pos 110,Sat.Literal.pos 111,Sat.Literal.pos 112],[Sat.Literal.neg 101,Sat.Literal.neg 24],[Sat.Literal.neg 107,Sat.Literal.neg 24],[Sat.Literal.neg 103,Sat.Literal.neg 13],[Sat.Literal.neg 103,Sat.Literal.neg 28],[Sat.Literal.neg 109,Sat.Literal.neg 13],[Sat.Literal.neg 109,Sat.Literal.neg 28],[Sat.Literal.neg 13,Sat.Literal.neg 28],[Sat.Literal.neg 104,Sat.Literal.neg 14],[Sat.Literal.neg 104,Sat.Literal.neg 29],[Sat.Literal.neg 110,Sat.Literal.neg 14],[Sat.Literal.neg 110,Sat.Literal.neg 29],[Sat.Literal.neg 14,Sat.Literal.neg 29],[Sat.Literal.neg 105,Sat.Literal.neg 111],[Sat.Literal.neg 106,Sat.Literal.neg 112],[Sat.Literal.pos 113,Sat.Literal.pos 114,Sat.Literal.pos 115,Sat.Literal.pos 116,Sat.Literal.pos 117,Sat.Literal.pos 118],[Sat.Literal.pos 119,Sat.Literal.pos 120,Sat.Literal.pos 121,Sat.Literal.pos 122,Sat.Literal.pos 123,Sat.Literal.pos 124],[Sat.Literal.neg 113,Sat.Literal.neg 25],[Sat.Literal.neg 119,Sat.Literal.neg 25],[Sat.Literal.neg 115,Sat.Literal.neg 121],[Sat.Literal.neg 115,Sat.Literal.neg 26],[Sat.Literal.neg 121,Sat.Literal.neg 26],[Sat.Literal.neg 116,Sat.Literal.neg 122],[Sat.Literal.neg 116,Sat.Literal.neg 27],[Sat.Literal.neg 122,Sat.Literal.neg 27],[Sat.Literal.pos 125,Sat.Literal.pos 126,Sat.Literal.pos 127,Sat.Literal.pos 128,Sat.Literal.pos 129,Sat.Literal.pos 130],[Sat.Literal.pos 131,Sat.Literal.pos 132,Sat.Literal.pos 133,Sat.Literal.pos 134,Sat.Literal.pos 135,Sat.Literal.pos 136],[Sat.Literal.neg 126,Sat.Literal.neg 10],[Sat.Literal.neg 132,Sat.Literal.neg 10],[Sat.Literal.neg 10,Sat.Literal.neg 19],[Sat.Literal.neg 127,Sat.Literal.neg 133],[Sat.Literal.neg 127,Sat.Literal.neg 28],[Sat.Literal.neg 133,Sat.Literal.neg 28],[Sat.Literal.neg 133,Sat.Literal.neg 20],[Sat.Literal.neg 128,Sat.Literal.neg 134],[Sat.Literal.neg 128,Sat.Literal.neg 29],[Sat.Literal.neg 134,Sat.Literal.neg 29],[Sat.Literal.neg 29,Sat.Literal.neg 21],[Sat.Literal.neg 129,Sat.Literal.neg 22],[Sat.Literal.neg 135,Sat.Literal.neg 22],[Sat.Literal.neg 130,Sat.Literal.neg 23],[Sat.Literal.neg 136,Sat.Literal.neg 23],[Sat.Literal.neg 30,Sat.Literal.neg 45],[Sat.Literal.neg 30,Sat.Literal.neg 51],[Sat.Literal.neg 35,Sat.Literal.neg 49],[Sat.Literal.neg 36,Sat.Literal.neg 50],[Sat.Literal.neg 35,Sat.Literal.neg 55],[Sat.Literal.neg 36,Sat.Literal.neg 56],[Sat.Literal.pos 0],[Sat.Literal.neg 41,Sat.Literal.neg 81],[Sat.Literal.neg 42,Sat.Literal.neg 82],[Sat.Literal.pos 7,Sat.Literal.pos 8],[Sat.Literal.neg 43,Sat.Literal.neg 89],[Sat.Literal.neg 43,Sat.Literal.neg 95],[Sat.Literal.pos 9],[Sat.Literal.neg 44,Sat.Literal.neg 125],[Sat.Literal.neg 44,Sat.Literal.neg 131],[Sat.Literal.pos 10],[Sat.Literal.neg 55,Sat.Literal.neg 87],[Sat.Literal.neg 56,Sat.Literal.neg 88],[Sat.Literal.pos 11,Sat.Literal.pos 12],[Sat.Literal.neg 49,Sat.Literal.neg 111],[Sat.Literal.neg 50,Sat.Literal.neg 112],[Sat.Literal.pos 13,Sat.Literal.pos 14],[Sat.Literal.neg 59,Sat.Literal.neg 70],[Sat.Literal.neg 60,Sat.Literal.neg 71],[Sat.Literal.neg 61,Sat.Literal.neg 72],[Sat.Literal.neg 60,Sat.Literal.neg 73],[Sat.Literal.neg 61,Sat.Literal.neg 74],[Sat.Literal.pos 15],[Sat.Literal.neg 57,Sat.Literal.neg 114],[Sat.Literal.neg 57,Sat.Literal.neg 120],[Sat.Literal.neg 62,Sat.Literal.neg 117],[Sat.Literal.neg 63,Sat.Literal.neg 118],[Sat.Literal.neg 60,Sat.Literal.neg 121],[Sat.Literal.neg 61,Sat.Literal.neg 122],[Sat.Literal.neg 68,Sat.Literal.neg 93],[Sat.Literal.neg 69,Sat.Literal.neg 94],[Sat.Literal.neg 71,Sat.Literal.neg 91],[Sat.Literal.neg 72,Sat.Literal.neg 92],[Sat.Literal.pos 16,Sat.Literal.pos 17],[Sat.Literal.neg 68,Sat.Literal.neg 129],[Sat.Literal.neg 69,Sat.Literal.neg 130],[Sat.Literal.neg 73,Sat.Literal.neg 127],[Sat.Literal.neg 74,Sat.Literal.neg 128],[Sat.Literal.neg 75,Sat.Literal.neg 102],[Sat.Literal.neg 75,Sat.Literal.neg 108],[Sat.Literal.pos 24],[Sat.Literal.neg 81,Sat.Literal.neg 123],[Sat.Literal.neg 82,Sat.Literal.neg 124],[Sat.Literal.neg 87,Sat.Literal.neg 123],[Sat.Literal.neg 88,Sat.Literal.neg 124],[Sat.Literal.pos 25],[Sat.Literal.neg 99,Sat.Literal.neg 117],[Sat.Literal.neg 100,Sat.Literal.neg 118],[Sat.Literal.pos 26,Sat.Literal.pos 27],[Sat.Literal.neg 105,Sat.Literal.neg 135],[Sat.Literal.neg 106,Sat.Literal.neg 136],[Sat.Literal.pos 28,Sat.Literal.pos 29],[Sat.Literal.pos 30],[Sat.Literal.pos 43],[Sat.Literal.pos 44],[Sat.Literal.pos 57],[Sat.Literal.pos 70],[Sat.Literal.pos 75],[Sat.Literal.pos 76],[Sat.Literal.pos 71,Sat.Literal.pos 72,Sat.Literal.pos 73,Sat.Literal.pos 74]] := by
    constructor
    intro clause hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (c 4) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (c 16) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 1 5) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 1 3) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 1 4 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 1 4 3 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 3 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 3 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 1 4 3 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 1 5 3 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 1 4 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 1 5 3 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 1 4 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 1 5 3 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 5 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 1 3 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 4 11) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 4 12) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 11 3 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 12 3 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 11 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 11 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 12 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 12 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 4 11 12 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 11 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 11 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 12 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 4 12 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 4 11 12 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 4 11 12 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 4 11 12 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 5 4) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 5 4 13 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 5 13 4 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 5 4 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 5 4 4 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 6 13) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 13 13 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 6 13 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 6 13 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 6 13 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 6 13 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 13 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 16 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 16 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 15 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 15 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 6 16 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 6 13 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 6 13 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 13 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 16 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 16 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 15 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 15 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 6 16 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 13 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 6 13 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 8 11) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 8 5) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 11 18 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 5 18 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 8 18 11 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 8 18 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 11 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 11 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 5 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 5 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 8 11 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 11 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 11 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 5 11 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 8 5 5 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 8 11 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 8 11 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 8 11 5 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 9 19) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      have he : (2 : Fin 6) = 4 := ha.symm.trans hb
      exact (by decide : (2 : Fin 6) ≠ 4) he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 9 15) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 19 7 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 15 7 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 9 19 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 19 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 19 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 15 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 15 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 9 19 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 19 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 19 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 15 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 9 15 15 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 9 19 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 9 19 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 9 19 15 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 11 12) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 11 20) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 12 17 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 20 17 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 12 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 12 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 20 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 20 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 11 12 20 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 12 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 12 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 20 12 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 11 20 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 11 12 20 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 11 12 20 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 11 12 20 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 12 18) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 12 19) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 18 18 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 19 18 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 12 18 19 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 18 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 19 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 12 18 19 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 18 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 12 19 19 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 13 20) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3 h4 h5
      rcases six_exhaust (h 13 16) with he | he | he | he | he | he
      · exact h0 he
      · exact h1 he
      · exact h2 he
      · exact h3 he
      · exact h4 he
      · exact h5 he
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 20 10 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 10 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 13 10 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 13 20 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 20 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hh 13 20 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 20 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 20 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hc 13 20 16 (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 20 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 20 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hn 13 16 16 (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 4 11 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 4 12 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 5 11 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 5 11 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 5 12 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 3 5 12 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 3 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 5 3 11 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 5 3 11 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 5 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 7 8 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 7 8 15 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 7 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 10 9 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 10 9 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 10 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 11 12 5 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 11 12 5 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 11 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 12 11 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 12 11 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 12 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 13 4 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 13 4 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 13 4 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 13 4 15 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 13 4 15 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 13 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 13 18 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 13 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 4 18 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 4 18 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 4 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 14 4 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 15 13 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 15 13 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 15 16 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 15 16 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 15 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 16 13 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 16 13 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 16 15 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 16 15 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 17 6 12 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 17 6 20 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 17 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 18 11 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 18 11 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 18 5 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 18 5 19 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [L,bit] using hm 18 (by decide)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 19 15 18 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 19 15 18 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 19 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 20 12 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      exact (hs 20 12 16 (by decide) (by decide) (by decide) (by decide)) (ha.trans hb.symm)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro ha hb
      rcases hg 20 (by decide) (by decide) (by decide) with hp | hp
      · exact ha hp
      · exact hb hp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 1
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 2
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 3
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 5
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 6
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 7
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro hneg
      apply hneg
      simpa [own,bit] using ho 8
    rcases List.mem_cons.mp hmem with rfl | hmem
    · dsimp [Sat.Valuation.satisfies, Sat.Valuation.neg, val]
      intro h0 h1 h2 h3
      rcases ht' with ht | ht
      · exact h2 ht
      · exact h3 ht
    cases hmem
  exact op874_fixed_owner_boolean_core (val c h) hsat

end IN1258Bridge

theorem op874_fixed_owner_maxcut_bad_port :
  let L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
  let R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
  let ends : Fin 21 → Sym2 (Fin 14) := fun e => s(L e,R e)
  let M : Finset (Fin 21) := {2,3,7,10,13,17,18}
  let bit : Fin 14 → Bool := ![false,true,true,true,true,false,false,false,false,true,false,false,false,true]
  let own : Fin 14 → Fin 21 := ![1,4,8,9,3,13,16,6,18,7,2,17,14,10]
  ∀ (c : Fin 21 → Fin 6) (h : Fin 14 → Fin 21 → Fin 6),
  (
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f) ∧
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f) ∧
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f) ∧
    (∀ e f g, L e ∈ ends f → R e ∈ ends g → f ≠ e → g ≠ e → h (L e) f ≠ h (R e) g) ∧
    (∀ e ∈ M, c e = if bit (L e) then 1 else 0) ∧
    (∀ e ∉ M, 2 ≤ (c e).val) ∧
    (∀ v : Fin 14, h v (own v) = if bit v then 0 else 1) ∧
    (∀ e ∉ M, e ≠ own (L e) → e ≠ own (R e) → c e = 2 ∨ c e = 3)) →
    h 6 15 ≠ 2 ∧ h 6 15 ≠ 3 := by
  dsimp only
  intro c h hstate
  rcases hstate with ⟨hc, hh, hn, hs, hm, hf, ho, hg⟩
  exact IN1258Bridge.fixed_owner_bad_port c h hc hh hn hs hm hf ho hg
