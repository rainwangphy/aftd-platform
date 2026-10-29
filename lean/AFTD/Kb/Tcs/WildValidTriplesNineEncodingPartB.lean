import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineSatCore

/-!
# wild_valid_triples_nine_encoding_part_b

Topic: graphs   Node: 82b7089781e4

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed. The former combined helper timed out in the180-second interactive gate. This is the SAME checked certificate and mathematical interpretation, split into a core and four soundness modules; no gate budget, axiom or mathematical statement is weakened.

Under the generic normalized-array assumptions and the assumption of no valid nine-vertex rearrangement, the induced equality valuation satisfies this explicit part of the fixed CNF. Every clause is proved from the array assumptions or an explicitly bijective candidate partition. This is an interpretation helper, not a standalone graph result.
-/

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
def in342_nine_formula_b : Sat.Fmla := (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 215]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 216])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 215,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 218])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 219]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 220]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 223])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 221]) (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 222])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 222]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 222,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 226])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 227]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 227])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 230])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 229,Sat.Literal.neg 230]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 232]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 234])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 236]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 234,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 240]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 240]) (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 243])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 242,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 246]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 247]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 249]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 249])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 248])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 250]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 248,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 248,Sat.Literal.neg 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 249,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 21])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 28]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 35]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 42]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 28])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 35]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 42])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 35])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 42]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 49]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 42]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 49])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 15]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 22]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 29]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 36]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 43]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 50])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 23]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 30])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 37]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 30]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 37]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 37])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 44]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 44]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 51])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 16]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 31])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 38]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 52]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 31]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 38])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 52]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 38]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 52]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 52])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 17])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 24]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 39])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 24]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 39])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 53])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 39]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 53])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 53]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 18])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 32])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 54]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 32])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 54]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 32]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 54]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 54])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 19])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 26]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 55]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 26]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 55]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 33]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 55]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 20])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 34])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 48]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 34])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 48]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 34]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 48]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 70])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 77]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 84])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 98]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 77]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 84])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 98])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 84]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 98]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 98])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 98]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 64])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 71]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 78])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 85]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 92]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 99]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 72])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 79]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 86]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 93]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 79]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 86]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 93])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 86])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 93]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 93])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 100]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 65]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 80])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 94]))))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 101]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 80]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 87]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 94]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 101])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 94])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 101]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 101]) (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 101]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 66]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 73])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 95]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 102]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 73]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 88]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 95]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 102])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 95])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 95])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 102]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 74])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 96])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 103]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 81]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 103])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 96])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 96])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 103]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 68]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 89]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 104]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 89]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 104])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 104])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 69]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 83])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 97]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 69,Sat.Literal.neg 83]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 69,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 97]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 112]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 119])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 126]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 133])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 119]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 126]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 133])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 126]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 133]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 133]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 140])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 113]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 120])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 120]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 127])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 134]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 134]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 141])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 57]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 114])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 128])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 142]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 121])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 135]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 142]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 128]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 142])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 135])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 142])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 58]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 122])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 136])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 143]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 122])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 129]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 136]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 143]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 59]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 108]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 115]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 130]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 144])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 115])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 137])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 137])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 130])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 137]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 144]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 60])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 116])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 138])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 145]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 116]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 61])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 117]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 131])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 110]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 117]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 131]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 117])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 131])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 124])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 146])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 62]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 118]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 125])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 139])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 132])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 139]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 105]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 147]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 154])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 168])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 147])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 161]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 175])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 161]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 168]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 161]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 175])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 175])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 106])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 155]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 162]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 169])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 155]))))))))))
private theorem in342_nine_chunk16 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 215]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 216])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 215,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 218])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 219]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 220]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 223])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 221]) (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 222])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 222]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 222,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 226])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 6)=v 2) → (A (v 5) (v 6)=v 7) → False
          intro h1 h2
          exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 3) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 4) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 4) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 7) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 2) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 7)=v 1) → (A (v 5) (v 7)=v 4) → False
          intro h1 h2
          exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 4) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 4) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 6) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk17 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 227]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 227])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 230])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 229,Sat.Literal.neg 230]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 232]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 234])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 236]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 234,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 236])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 240])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 3) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 1) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 1) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 2) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 2) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 2) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 3) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 3) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 3) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 4) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 4) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 6) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 6) (v 7)=v 0) → (A (v 6) (v 7)=v 1) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 1) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 1) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 1) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 1) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 2) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 2) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 3) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 4) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 0) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 0) → (A (v 6) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk18 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 240]) (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 239,Sat.Literal.neg 243])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 242,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 246]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 247]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 249]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 245,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 249])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 246,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 248])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 247,Sat.Literal.neg 250]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 248,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 248,Sat.Literal.neg 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 249,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 21])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 6) (v 8)=v 0) → (A (v 6) (v 8)=v 3) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 0) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 0) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 1) → (A (v 6) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 1) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 1) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 1) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 6) (v 8)=v 2) → (A (v 6) (v 8)=v 3) → False
          intro h1 h2
          exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 2) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 2) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 3) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 3) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 4) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 0) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 7) (v 8)=v 0) → (A (v 7) (v 8)=v 2) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 0) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 0) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 0) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 1) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 1) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 1) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 1) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 2) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 2) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 2) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 3) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 3) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 4) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 1 := h1
            have hb : A (v 0) (v 4)=v 1 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))


private theorem in342_nine_chunk19 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 28]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 35]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 42]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 28])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 35]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 42])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 35])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 42]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 49]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 42]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 49])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 49]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 15]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 22]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 29]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 36]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 43]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 50])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 23]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 30])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 37]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 30]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 37]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 37])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 3)=v 1) → (A (v 0) (v 5)=v 1) → False
          intro h1 h2
          have ha : A (v 0) (v 3)=v 1 := h1
          have hb : A (v 0) (v 5)=v 1 := h2
          exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 1 := h1
            have hb : A (v 0) (v 6)=v 1 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 1 := h1
            have hb : A (v 0) (v 7)=v 1 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 1 := h1
            have hb : A (v 0) (v 8)=v 1 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 1 := h1
            have hb : A (v 0) (v 5)=v 1 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 1 := h1
            have hb : A (v 0) (v 6)=v 1 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 1 := h1
            have hb : A (v 0) (v 7)=v 1 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 1 := h1
            have hb : A (v 0) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 1 := h1
            have hb : A (v 0) (v 6)=v 1 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 1 := h1
            have hb : A (v 0) (v 7)=v 1 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 1 := h1
            have hb : A (v 0) (v 8)=v 1 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 1 := h1
            have hb : A (v 0) (v 7)=v 1 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 1 := h1
            have hb : A (v 0) (v 8)=v 1 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 0) (v 7)=v 1 := h1
            have hb : A (v 0) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 3)=v 2) → False
            intro h1 h2
            have ha : A (v 0) (v 1)=v 2 := h1
            have hb : A (v 0) (v 3)=v 2 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 1)=v 2) → (A (v 0) (v 4)=v 2) → False
          intro h1 h2
          have ha : A (v 0) (v 1)=v 2 := h1
          have hb : A (v 0) (v 4)=v 2 := h2
          exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 5)=v 2) → False
            intro h1 h2
            have ha : A (v 0) (v 1)=v 2 := h1
            have hb : A (v 0) (v 5)=v 2 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 0) (v 1)=v 2 := h1
            have hb : A (v 0) (v 6)=v 2 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 0) (v 1)=v 2 := h1
            have hb : A (v 0) (v 7)=v 2 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 0) (v 1)=v 2 := h1
            have hb : A (v 0) (v 8)=v 2 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 3 := h1
            have hb : A (v 0) (v 4)=v 3 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 3 := h1
            have hb : A (v 0) (v 5)=v 3 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 3 := h1
            have hb : A (v 0) (v 6)=v 3 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 3 := h1
            have hb : A (v 0) (v 7)=v 3 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 3 := h1
            have hb : A (v 0) (v 8)=v 3 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 3 := h1
            have hb : A (v 0) (v 5)=v 3 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 3 := h1
            have hb : A (v 0) (v 6)=v 3 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 3 := h1
            have hb : A (v 0) (v 7)=v 3 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 3 := h1
            have hb : A (v 0) (v 8)=v 3 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 0) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 3 := h1
            have hb : A (v 0) (v 6)=v 3 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))


private theorem in342_nine_chunk20 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 44]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 44]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 51]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 51])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 16]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 31])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 38]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 52]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 31]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 38])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 52]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 38]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 52]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 52])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 17])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 24]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 39])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 24]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 39])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 53])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 3) → (A (v 0) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 0) (v 5)=v 3 := h1
          have hb : A (v 0) (v 7)=v 3 := h2
          exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 3 := h1
            have hb : A (v 0) (v 8)=v 3 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 0) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 3 := h1
            have hb : A (v 0) (v 7)=v 3 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 3 := h1
            have hb : A (v 0) (v 8)=v 3 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 0) (v 7)=v 3 := h1
            have hb : A (v 0) (v 8)=v 3 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 4 := h1
            have hb : A (v 0) (v 3)=v 4 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 4 := h1
            have hb : A (v 0) (v 5)=v 4 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 4) → (A (v 0) (v 6)=v 4) → False
          intro h1 h2
          have ha : A (v 0) (v 2)=v 4 := h1
          have hb : A (v 0) (v 6)=v 4 := h2
          exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 4 := h1
            have hb : A (v 0) (v 7)=v 4 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 4 := h1
            have hb : A (v 0) (v 8)=v 4 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 4 := h1
            have hb : A (v 0) (v 5)=v 4 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 4 := h1
            have hb : A (v 0) (v 6)=v 4 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 4 := h1
            have hb : A (v 0) (v 7)=v 4 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 4 := h1
            have hb : A (v 0) (v 8)=v 4 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 4) → (A (v 0) (v 6)=v 4) → False
          intro h1 h2
          have ha : A (v 0) (v 5)=v 4 := h1
          have hb : A (v 0) (v 6)=v 4 := h2
          exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 4 := h1
            have hb : A (v 0) (v 7)=v 4 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 4 := h1
            have hb : A (v 0) (v 8)=v 4 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 4 := h1
            have hb : A (v 0) (v 7)=v 4 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 4 := h1
            have hb : A (v 0) (v 8)=v 4 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 0) (v 7)=v 4 := h1
            have hb : A (v 0) (v 8)=v 4 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 5 := h1
            have hb : A (v 0) (v 3)=v 5 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 5 := h1
            have hb : A (v 0) (v 4)=v 5 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 5 := h1
            have hb : A (v 0) (v 6)=v 5 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 5 := h1
            have hb : A (v 0) (v 7)=v 5 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 5 := h1
            have hb : A (v 0) (v 8)=v 5 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 5 := h1
            have hb : A (v 0) (v 4)=v 5 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 5 := h1
            have hb : A (v 0) (v 6)=v 5 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 5 := h1
            have hb : A (v 0) (v 7)=v 5 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 5 := h1
            have hb : A (v 0) (v 8)=v 5 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))


private theorem in342_nine_chunk21 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 39]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 46]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 53])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 53]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 18])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 32])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 54]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 32])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 54]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 32]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 54]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 54])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 19])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 26]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 55]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 26]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 55])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 5) → (A (v 0) (v 6)=v 5) → False
          intro h1 h2
          have ha : A (v 0) (v 4)=v 5 := h1
          have hb : A (v 0) (v 6)=v 5 := h2
          exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 5 := h1
            have hb : A (v 0) (v 7)=v 5 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 5 := h1
            have hb : A (v 0) (v 8)=v 5 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 5 := h1
            have hb : A (v 0) (v 7)=v 5 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 5 := h1
            have hb : A (v 0) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 0) (v 7)=v 5 := h1
            have hb : A (v 0) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 6 := h1
            have hb : A (v 0) (v 3)=v 6 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 6 := h1
            have hb : A (v 0) (v 4)=v 6 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 6 := h1
            have hb : A (v 0) (v 5)=v 6 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 6 := h1
            have hb : A (v 0) (v 7)=v 6 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 6 := h1
            have hb : A (v 0) (v 8)=v 6 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 6 := h1
            have hb : A (v 0) (v 4)=v 6 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 6 := h1
            have hb : A (v 0) (v 5)=v 6 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 6 := h1
            have hb : A (v 0) (v 7)=v 6 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 6 := h1
            have hb : A (v 0) (v 8)=v 6 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 6) → (A (v 0) (v 5)=v 6) → False
          intro h1 h2
          have ha : A (v 0) (v 4)=v 6 := h1
          have hb : A (v 0) (v 5)=v 6 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 6 := h1
            have hb : A (v 0) (v 7)=v 6 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 6 := h1
            have hb : A (v 0) (v 8)=v 6 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 6 := h1
            have hb : A (v 0) (v 7)=v 6 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 6 := h1
            have hb : A (v 0) (v 8)=v 6 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 0) (v 7)=v 6 := h1
            have hb : A (v 0) (v 8)=v 6 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 3)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 7 := h1
            have hb : A (v 0) (v 3)=v 7 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 7 := h1
            have hb : A (v 0) (v 4)=v 7 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 7 := h1
            have hb : A (v 0) (v 5)=v 7 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 7 := h1
            have hb : A (v 0) (v 6)=v 7 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 7 := h1
            have hb : A (v 0) (v 8)=v 7 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 7 := h1
            have hb : A (v 0) (v 4)=v 7 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 7 := h1
            have hb : A (v 0) (v 5)=v 7 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 7 := h1
            have hb : A (v 0) (v 6)=v 7 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 7 := h1
            have hb : A (v 0) (v 8)=v 7 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))


private theorem in342_nine_chunk22 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 33]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 55]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 20])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 34])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 48]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 34])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 48]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 34]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 48]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 70])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 77]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 84])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 98]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 77]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 84])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 98])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 7) → (A (v 0) (v 5)=v 7) → False
          intro h1 h2
          have ha : A (v 0) (v 4)=v 7 := h1
          have hb : A (v 0) (v 5)=v 7 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 7 := h1
            have hb : A (v 0) (v 6)=v 7 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 7 := h1
            have hb : A (v 0) (v 8)=v 7 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 7 := h1
            have hb : A (v 0) (v 6)=v 7 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 7 := h1
            have hb : A (v 0) (v 8)=v 7 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 7 := h1
            have hb : A (v 0) (v 8)=v 7 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 0) (v 3)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 8 := h1
            have hb : A (v 0) (v 3)=v 8 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 0) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 8 := h1
            have hb : A (v 0) (v 4)=v 8 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 8 := h1
            have hb : A (v 0) (v 5)=v 8 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 8 := h1
            have hb : A (v 0) (v 6)=v 8 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 2)=v 8 := h1
            have hb : A (v 0) (v 7)=v 8 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 8 := h1
            have hb : A (v 0) (v 4)=v 8 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 8 := h1
            have hb : A (v 0) (v 5)=v 8 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 8 := h1
            have hb : A (v 0) (v 6)=v 8 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 3)=v 8 := h1
            have hb : A (v 0) (v 7)=v 8 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 8) → (A (v 0) (v 5)=v 8) → False
          intro h1 h2
          have ha : A (v 0) (v 4)=v 8 := h1
          have hb : A (v 0) (v 5)=v 8 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 8 := h1
            have hb : A (v 0) (v 6)=v 8 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 4)=v 8 := h1
            have hb : A (v 0) (v 7)=v 8 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 8 := h1
            have hb : A (v 0) (v 6)=v 8 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 5)=v 8 := h1
            have hb : A (v 0) (v 7)=v 8 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 8) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 0) (v 6)=v 8 := h1
            have hb : A (v 0) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 0) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 0 := h1
            have hb : A (v 1) (v 4)=v 0 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 0 := h1
            have hb : A (v 1) (v 5)=v 0 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 0 := h1
            have hb : A (v 1) (v 6)=v 0 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 0 := h1
            have hb : A (v 1) (v 7)=v 0 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 0 := h1
            have hb : A (v 1) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 0 := h1
            have hb : A (v 1) (v 5)=v 0 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 0 := h1
            have hb : A (v 1) (v 6)=v 0 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 0 := h1
            have hb : A (v 1) (v 7)=v 0 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 0 := h1
            have hb : A (v 1) (v 8)=v 0 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))


private theorem in342_nine_chunk23 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 84]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 98]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 91]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 98])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 98]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 64])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 71]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 78])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 85]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 92]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 99]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 72])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 79]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 86]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 93]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 79]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 86]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 93])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 86])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 93]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 93])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 100]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 100]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 65]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 80])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 94])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 5)=v 0) → (A (v 1) (v 6)=v 0) → False
          intro h1 h2
          have ha : A (v 1) (v 5)=v 0 := h1
          have hb : A (v 1) (v 6)=v 0 := h2
          exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 0 := h1
            have hb : A (v 1) (v 7)=v 0 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 0 := h1
            have hb : A (v 1) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 0 := h1
            have hb : A (v 1) (v 7)=v 0 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 0 := h1
            have hb : A (v 1) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 1) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 1) (v 7)=v 0 := h1
            have hb : A (v 1) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 3)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 3)=v 2 := h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 4)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 4)=v 2 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 5)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 5)=v 2 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 6)=v 2 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 7)=v 2 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 1) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 1) (v 0)=v 2 := (hsym _ _).trans h1
            have hb : A (v 1) (v 8)=v 2 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 3 := h1
            have hb : A (v 1) (v 4)=v 3 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 3 := h1
            have hb : A (v 1) (v 5)=v 3 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 3 := h1
            have hb : A (v 1) (v 6)=v 3 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 3) → (A (v 1) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 1) (v 2)=v 3 := h1
          have hb : A (v 1) (v 7)=v 3 := h2
          exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 3 := h1
            have hb : A (v 1) (v 8)=v 3 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 3 := h1
            have hb : A (v 1) (v 5)=v 3 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 3 := h1
            have hb : A (v 1) (v 6)=v 3 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 3 := h1
            have hb : A (v 1) (v 7)=v 3 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 3 := h1
            have hb : A (v 1) (v 8)=v 3 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 1) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 3 := h1
            have hb : A (v 1) (v 6)=v 3 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 1) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 3 := h1
            have hb : A (v 1) (v 7)=v 3 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 1) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 3 := h1
            have hb : A (v 1) (v 7)=v 3 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 1) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 3 := h1
            have hb : A (v 1) (v 8)=v 3 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 1) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 1) (v 7)=v 3 := h1
            have hb : A (v 1) (v 8)=v 3 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 4 := h1
            have hb : A (v 1) (v 3)=v 4 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 4 := h1
            have hb : A (v 1) (v 5)=v 4 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 4 := h1
            have hb : A (v 1) (v 6)=v 4 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 4 := h1
            have hb : A (v 1) (v 7)=v 4 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))


private theorem in342_nine_chunk24 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 101]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 80]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 87]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 94]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 101])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 94])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 101]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 101]) (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 101]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 66]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 73])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 95]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 102]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 73]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 88]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 95]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 102])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 95])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 95])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 102]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 74])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 96])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 4) → (A (v 1) (v 8)=v 4) → False
          intro h1 h2
          have ha : A (v 1) (v 2)=v 4 := h1
          have hb : A (v 1) (v 8)=v 4 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 4 := h1
            have hb : A (v 1) (v 5)=v 4 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 4 := h1
            have hb : A (v 1) (v 6)=v 4 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 4 := h1
            have hb : A (v 1) (v 7)=v 4 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 4 := h1
            have hb : A (v 1) (v 8)=v 4 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 4 := h1
            have hb : A (v 1) (v 6)=v 4 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 1) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 4 := h1
            have hb : A (v 1) (v 7)=v 4 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 5)=v 4) → (A (v 1) (v 8)=v 4) → False
          intro h1 h2
          have ha : A (v 1) (v 5)=v 4 := h1
          have hb : A (v 1) (v 8)=v 4 := h2
          exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 1) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 4 := h1
            have hb : A (v 1) (v 8)=v 4 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 4) → (A (v 1) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 1) (v 7)=v 4 := h1
            have hb : A (v 1) (v 8)=v 4 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 5 := h1
            have hb : A (v 1) (v 3)=v 5 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 5 := h1
            have hb : A (v 1) (v 4)=v 5 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 5 := h1
            have hb : A (v 1) (v 6)=v 5 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 5 := h1
            have hb : A (v 1) (v 7)=v 5 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 5) → (A (v 1) (v 8)=v 5) → False
          intro h1 h2
          have ha : A (v 1) (v 2)=v 5 := h1
          have hb : A (v 1) (v 8)=v 5 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 5 := h1
            have hb : A (v 1) (v 4)=v 5 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 5 := h1
            have hb : A (v 1) (v 6)=v 5 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 5 := h1
            have hb : A (v 1) (v 7)=v 5 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 5 := h1
            have hb : A (v 1) (v 8)=v 5 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 5 := h1
            have hb : A (v 1) (v 6)=v 5 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 5 := h1
            have hb : A (v 1) (v 7)=v 5 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 5 := h1
            have hb : A (v 1) (v 8)=v 5 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 1) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 5 := h1
            have hb : A (v 1) (v 7)=v 5 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 1) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 5 := h1
            have hb : A (v 1) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 5) → (A (v 1) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 1) (v 7)=v 5 := h1
            have hb : A (v 1) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 6 := h1
            have hb : A (v 1) (v 3)=v 6 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 6 := h1
            have hb : A (v 1) (v 4)=v 6 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 6 := h1
            have hb : A (v 1) (v 5)=v 6 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 6 := h1
            have hb : A (v 1) (v 7)=v 6 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))


private theorem in342_nine_chunk25 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 103]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 81]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 103])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 96])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 96])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 103]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 68]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 89]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 104]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 89]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 104])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 104])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 69]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 83])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 97])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 6) → (A (v 1) (v 8)=v 6) → False
          intro h1 h2
          have ha : A (v 1) (v 2)=v 6 := h1
          have hb : A (v 1) (v 8)=v 6 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 6 := h1
            have hb : A (v 1) (v 4)=v 6 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 6 := h1
            have hb : A (v 1) (v 5)=v 6 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 6 := h1
            have hb : A (v 1) (v 7)=v 6 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 6 := h1
            have hb : A (v 1) (v 8)=v 6 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 6 := h1
            have hb : A (v 1) (v 5)=v 6 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 6 := h1
            have hb : A (v 1) (v 7)=v 6 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 6 := h1
            have hb : A (v 1) (v 8)=v 6 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 6 := h1
            have hb : A (v 1) (v 7)=v 6 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 6 := h1
            have hb : A (v 1) (v 8)=v 6 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 6) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 1) (v 7)=v 6 := h1
            have hb : A (v 1) (v 8)=v 6 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 1) (v 3)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 7 := h1
            have hb : A (v 1) (v 3)=v 7 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 1) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 7 := h1
            have hb : A (v 1) (v 4)=v 7 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 7 := h1
            have hb : A (v 1) (v 5)=v 7 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 7 := h1
            have hb : A (v 1) (v 6)=v 7 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 7) → (A (v 1) (v 8)=v 7) → False
          intro h1 h2
          have ha : A (v 1) (v 2)=v 7 := h1
          have hb : A (v 1) (v 8)=v 7 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 7 := h1
            have hb : A (v 1) (v 5)=v 7 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 7 := h1
            have hb : A (v 1) (v 6)=v 7 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 7 := h1
            have hb : A (v 1) (v 8)=v 7 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 7 := h1
            have hb : A (v 1) (v 5)=v 7 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 7 := h1
            have hb : A (v 1) (v 6)=v 7 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 7 := h1
            have hb : A (v 1) (v 8)=v 7 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 7 := h1
            have hb : A (v 1) (v 6)=v 7 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 7 := h1
            have hb : A (v 1) (v 8)=v 7 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 7) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 7 := h1
            have hb : A (v 1) (v 8)=v 7 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 8 := h1
            have hb : A (v 1) (v 3)=v 8 := h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 8 := h1
            have hb : A (v 1) (v 4)=v 8 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 8 := h1
            have hb : A (v 1) (v 5)=v 8 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 8 := h1
            have hb : A (v 1) (v 6)=v 8 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 2)=v 8 := h1
            have hb : A (v 1) (v 7)=v 8 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))


private theorem in342_nine_chunk26 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 69,Sat.Literal.neg 83]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 69,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 97]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 112]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 119])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 126]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 133])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 119]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 126]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 133])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 126]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 133]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 133]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 140])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 113]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 120])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 120]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 127])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 3)=v 8) → (A (v 1) (v 5)=v 8) → False
          intro h1 h2
          have ha : A (v 1) (v 3)=v 8 := h1
          have hb : A (v 1) (v 5)=v 8 := h2
          exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 3)=v 8 := h1
            have hb : A (v 1) (v 7)=v 8 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 4)=v 8 := h1
            have hb : A (v 1) (v 7)=v 8 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 5)=v 8 := h1
            have hb : A (v 1) (v 7)=v 8 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 1) (v 6)=v 8 := h1
            have hb : A (v 1) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 1) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 0 := h1
            have hb : A (v 2) (v 4)=v 0 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 0 := h1
            have hb : A (v 2) (v 5)=v 0 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 0 := h1
            have hb : A (v 2) (v 6)=v 0 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 0 := h1
            have hb : A (v 2) (v 7)=v 0 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 0 := h1
            have hb : A (v 2) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 0 := h1
            have hb : A (v 2) (v 5)=v 0 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 0 := h1
            have hb : A (v 2) (v 6)=v 0 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 0 := h1
            have hb : A (v 2) (v 7)=v 0 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 0 := h1
            have hb : A (v 2) (v 8)=v 0 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 0 := h1
            have hb : A (v 2) (v 6)=v 0 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 5)=v 0) → (A (v 2) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 2) (v 5)=v 0 := h1
          have hb : A (v 2) (v 7)=v 0 := h2
          exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 0 := h1
            have hb : A (v 2) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 0 := h1
            have hb : A (v 2) (v 7)=v 0 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 0 := h1
            have hb : A (v 2) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 2) (v 7)=v 0 := h1
            have hb : A (v 2) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 1 := h1
            have hb : A (v 2) (v 4)=v 1 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 1 := h1
            have hb : A (v 2) (v 5)=v 1 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 1 := h1
            have hb : A (v 2) (v 6)=v 1 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 1 := h1
            have hb : A (v 2) (v 7)=v 1 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 1 := h1
            have hb : A (v 2) (v 8)=v 1 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 1 := h1
            have hb : A (v 2) (v 5)=v 1 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 1 := h1
            have hb : A (v 2) (v 6)=v 1 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 1 := h1
            have hb : A (v 2) (v 7)=v 1 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 1 := h1
            have hb : A (v 2) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 1 := h1
            have hb : A (v 2) (v 6)=v 1 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))


private theorem in342_nine_chunk27 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 134]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 134]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 141]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 141])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 57]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 114])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 128])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 142]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 121])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 135]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 142]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 128]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 142])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 135])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 142])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 58]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 122])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 136])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 5)=v 1) → (A (v 2) (v 7)=v 1) → False
          intro h1 h2
          have ha : A (v 2) (v 5)=v 1 := h1
          have hb : A (v 2) (v 7)=v 1 := h2
          exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 1 := h1
            have hb : A (v 2) (v 8)=v 1 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 1 := h1
            have hb : A (v 2) (v 7)=v 1 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 1 := h1
            have hb : A (v 2) (v 8)=v 1 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 2) (v 7)=v 1 := h1
            have hb : A (v 2) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 1) (v 2)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 3 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 3 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 3 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 3 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 3 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 3 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 3 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 3 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 3 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 3) → (A (v 2) (v 8)=v 3) → False
          intro h1 h2
          have ha : A (v 2) (v 1)=v 3 := (hsym _ _).trans h1
          have hb : A (v 2) (v 8)=v 3 := h2
          exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 3 := h1
            have hb : A (v 2) (v 5)=v 3 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 3 := h1
            have hb : A (v 2) (v 6)=v 3 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 3 := h1
            have hb : A (v 2) (v 7)=v 3 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 3 := h1
            have hb : A (v 2) (v 8)=v 3 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 3 := h1
            have hb : A (v 2) (v 6)=v 3 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 3 := h1
            have hb : A (v 2) (v 7)=v 3 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 3 := h1
            have hb : A (v 2) (v 8)=v 3 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 3 := h1
            have hb : A (v 2) (v 8)=v 3 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 2) (v 7)=v 3 := h1
            have hb : A (v 2) (v 8)=v 3 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 1) (v 2)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 4 := h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 4 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 4 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 4 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))


private theorem in342_nine_chunk28 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 143]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 122])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 129]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 136]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 143]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 129]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 59]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 108]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 115]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 130]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 144])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 115])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 137])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 137])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 130])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 4) → (A (v 2) (v 8)=v 4) → False
          intro h1 h2
          have ha : A (v 2) (v 0)=v 4 := (hsym _ _).trans h1
          have hb : A (v 2) (v 8)=v 4 := h2
          exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 4 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 4 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 4 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 4 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 4 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 4 := h1
            have hb : A (v 2) (v 5)=v 4 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 4) → (A (v 2) (v 6)=v 4) → False
          intro h1 h2
          have ha : A (v 2) (v 3)=v 4 := h1
          have hb : A (v 2) (v 6)=v 4 := h2
          exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 4 := h1
            have hb : A (v 2) (v 7)=v 4 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 4 := h1
            have hb : A (v 2) (v 8)=v 4 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 4 := h1
            have hb : A (v 2) (v 6)=v 4 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 4 := h1
            have hb : A (v 2) (v 7)=v 4 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 4 := h1
            have hb : A (v 2) (v 8)=v 4 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 1) (v 2)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 5) → (A (v 2) (v 3)=v 5) → False
          intro h1 h2
          have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
          have hb : A (v 2) (v 3)=v 5 := h2
          exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 5 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 5 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 5 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 5 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 5 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 5 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 5 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 5 := h1
            have hb : A (v 2) (v 4)=v 5 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 5 := h1
            have hb : A (v 2) (v 6)=v 5 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 5 := h1
            have hb : A (v 2) (v 7)=v 5 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 5 := h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 5 := h1
            have hb : A (v 2) (v 6)=v 5 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))


private theorem in342_nine_chunk29 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 137]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 144]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 60])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 116])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 138])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 145]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 116]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 61])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 117]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 131])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 110])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 4)=v 5) → (A (v 2) (v 7)=v 5) → False
          intro h1 h2
          have ha : A (v 2) (v 4)=v 5 := h1
          have hb : A (v 2) (v 7)=v 5 := h2
          exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 5 := h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 5 := h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 2) (v 7)=v 5 := h1
            have hb : A (v 2) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 1) (v 2)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 6 := h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 6 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 6 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 6 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 6 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 6 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 6 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 6 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 6 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 6 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 6) → (A (v 2) (v 4)=v 6) → False
          intro h1 h2
          have ha : A (v 2) (v 3)=v 6 := h1
          have hb : A (v 2) (v 4)=v 6 := h2
          exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 6 := h1
            have hb : A (v 2) (v 5)=v 6 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 6 := h1
            have hb : A (v 2) (v 7)=v 6 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 6 := h1
            have hb : A (v 2) (v 8)=v 6 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 6 := h1
            have hb : A (v 2) (v 5)=v 6 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 6 := h1
            have hb : A (v 2) (v 7)=v 6 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 6 := h1
            have hb : A (v 2) (v 8)=v 6 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 2) (v 7)=v 6 := h1
            have hb : A (v 2) (v 8)=v 6 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 1) (v 2)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 7 := h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 7 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 7 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 7 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 7 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))


private theorem in342_nine_chunk30 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 117]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 131]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 117])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 131])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 124])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 146])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 62]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 118]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 13,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 125])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 62,Sat.Literal.neg 139])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 132])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 7) → (A (v 2) (v 4)=v 7) → False
          intro h1 h2
          have ha : A (v 2) (v 1)=v 7 := (hsym _ _).trans h1
          have hb : A (v 2) (v 4)=v 7 := h2
          exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 7 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 7 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 7 := h1
            have hb : A (v 2) (v 4)=v 7 := h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 7 := h1
            have hb : A (v 2) (v 5)=v 7 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 7 := h1
            have hb : A (v 2) (v 6)=v 7 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 7 := h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 7 := h1
            have hb : A (v 2) (v 5)=v 7 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 7 := h1
            have hb : A (v 2) (v 6)=v 7 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 7 := h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 7 := h1
            have hb : A (v 2) (v 6)=v 7 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 7 := h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 7 := h1
            have hb : A (v 2) (v 8)=v 7 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 1) (v 2)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 1)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 2) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 8) → (A (v 2) (v 4)=v 8) → False
          intro h1 h2
          have ha : A (v 2) (v 0)=v 8 := (hsym _ _).trans h1
          have hb : A (v 2) (v 4)=v 8 := h2
          exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 8 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 8 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 8 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 3)=v 8 := h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 4)=v 8 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 5)=v 8 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 6)=v 8 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 2) (v 7)=v 8 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 8 := h1
            have hb : A (v 2) (v 5)=v 8 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 8 := h1
            have hb : A (v 2) (v 6)=v 8 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 3)=v 8 := h1
            have hb : A (v 2) (v 7)=v 8 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 8 := h1
            have hb : A (v 2) (v 6)=v 8 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 4)=v 8 := h1
            have hb : A (v 2) (v 7)=v 8 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 5)=v 8 := h1
            have hb : A (v 2) (v 6)=v 8 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 2) (ha.trans hb.symm)))


private theorem in342_nine_chunk31 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 139]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 105]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 147]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 154])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 168])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 147])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 161]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 175])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 161]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 168]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 161]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 175])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 175])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 175]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 106])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 155]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 162]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 169])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 155])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 5)=v 8) → (A (v 2) (v 7)=v 8) → False
          intro h1 h2
          have ha : A (v 2) (v 5)=v 8 := h1
          have hb : A (v 2) (v 7)=v 8 := h2
          exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 2) (v 6)=v 8 := h1
            have hb : A (v 2) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 2) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 2) (v 3)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 3) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 0 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 3) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 0 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 0 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 0 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 3) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 0 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 3) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 0 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 0 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 0 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 0 := h1
            have hb : A (v 3) (v 5)=v 0 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 0 := h1
            have hb : A (v 3) (v 6)=v 0 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 0) → (A (v 3) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 3) (v 4)=v 0 := h1
          have hb : A (v 3) (v 7)=v 0 := h2
          exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 0 := h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 0 := h1
            have hb : A (v 3) (v 6)=v 0 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 0 := h1
            have hb : A (v 3) (v 7)=v 0 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 0 := h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 0 := h1
            have hb : A (v 3) (v 7)=v 0 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 0 := h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 0 := h1
            have hb : A (v 3) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 2) (v 3)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 3) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 1 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 3) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 1 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 3) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 1 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 3) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 1 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 3) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 1 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 3) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 1 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))

theorem wild_valid_triples_nine_encoding_part_b {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla in342_nine_formula_b := by
  exact (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk16 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk17 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk18 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk19 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk20 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk21 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk22 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk23 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk24 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk25 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk26 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk27 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk28 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk29 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk30 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk31 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))))
