import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineSatCore

/-!
# wild_valid_triples_nine_encoding_part_c

Topic: graphs   Node: cf426a80f23b

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed. The former combined helper timed out in the180-second interactive gate. This is the SAME checked certificate and mathematical interpretation, split into a core and four soundness modules; no gate budget, axiom or mathematical statement is weakened.

Under the generic normalized-array assumptions and the assumption of no valid nine-vertex rearrangement, the induced equality valuation satisfies this explicit part of the fixed CNF. Every clause is proved from the array assumptions or an explicitly bijective candidate partition. This is an interpretation helper, not a standalone graph result.
-/

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
def in342_nine_formula_c : Sat.Fmla := (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 162]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 176]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 155]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 162])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 176])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 162]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 176]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 176]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 156]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 163])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 177]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 163]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 177]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 177]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 65])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 178]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 178])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 178]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 178]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 66])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 165])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 165])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 179]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 179]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 67])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 151])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 173])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 151]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 158]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 158]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 180]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 110])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 152]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 181])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 181]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 159]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 166]) (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 166]) (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 181])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 111])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 174])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 160]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 112])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 147]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 182])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 189]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 196]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 147])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 182]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 189]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 196]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 182]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 189]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 196])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 189])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 203])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 203]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 113])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 183])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 190]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 197]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 204]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 183])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 197])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 204]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 190]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 197]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 204])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 197]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 197]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 191])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 198]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 198]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 205]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 72])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 192])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 199]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 114]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 199])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 73])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 115]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 193]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 200]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 193]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 193])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 207])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 207]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 74])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 151]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 186]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 201])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 151])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 201]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 75]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 117]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 187]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 152])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 209]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 194])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 209])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 194,Sat.Literal.neg 209]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 118])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 188])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 202]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 195]) (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 202]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 195,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 119])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 182])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 217])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 154]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 182]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 224]))))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 182]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 217]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 224])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 217]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 224]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 120]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 155])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 211]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 218]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 155]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 211])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 225])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 211])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 225]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 218])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 218])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 225]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 219])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 212])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 226])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 226]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 79])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 213]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 220]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 121]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 213]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 213])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 227]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 80])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 122]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 214]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 214])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 228])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 123]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 158]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 222]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 222])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 158])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 229])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 222,Sat.Literal.neg 229]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 124]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 230])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 159])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 215]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 159])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 230]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 187]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 230]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 230])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 215,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 83])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 216]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 188])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 216]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 160]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 216])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 223]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 216,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 126])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 189]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 210]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 238]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 189])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 231])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 189])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 231]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 238])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 231]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 238]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 162])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 211])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 239])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 162]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 190]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 232])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 190]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 211]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 239]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 232])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 232])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 239])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 212]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 240])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 233]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 240]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 240]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 240]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 86])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 213])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 241]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 213]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 164])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 129]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 164]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 164])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 235]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 242])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 130])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 165]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 236]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 193])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 243])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 236,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 166]))))))))))
private theorem in342_nine_chunk32 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 162]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 176]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 155]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 162])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 176])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 162]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 176]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 176]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 156]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 163])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 177]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 163]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 177]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 177]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 65])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 178]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 178])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 1) → (A (v 3) (v 6)=v 1) → False
          intro h1 h2
          have ha : A (v 3) (v 2)=v 1 := (hsym _ _).trans h1
          have hb : A (v 3) (v 6)=v 1 := h2
          exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 3) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 1 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 1 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 1 := h1
            have hb : A (v 3) (v 5)=v 1 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 1 := h1
            have hb : A (v 3) (v 6)=v 1 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 1 := h1
            have hb : A (v 3) (v 7)=v 1 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 1 := h1
            have hb : A (v 3) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 5)=v 1) → (A (v 3) (v 6)=v 1) → False
          intro h1 h2
          have ha : A (v 3) (v 5)=v 1 := h1
          have hb : A (v 3) (v 6)=v 1 := h2
          exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 1 := h1
            have hb : A (v 3) (v 8)=v 1 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 1) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 1 := h1
            have hb : A (v 3) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 5)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 2 := h1
            have hb : A (v 3) (v 5)=v 2 := h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 2 := h1
            have hb : A (v 3) (v 6)=v 2 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 2 := h1
            have hb : A (v 3) (v 7)=v 2 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 2 := h1
            have hb : A (v 3) (v 8)=v 2 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 5)=v 2) → (A (v 3) (v 6)=v 2) → False
          intro h1 h2
          have ha : A (v 3) (v 5)=v 2 := h1
          have hb : A (v 3) (v 6)=v 2 := h2
          exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 3) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 2 := h1
            have hb : A (v 3) (v 7)=v 2 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 3) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 2 := h1
            have hb : A (v 3) (v 8)=v 2 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 3) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 2 := h1
            have hb : A (v 3) (v 7)=v 2 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 3) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 2 := h1
            have hb : A (v 3) (v 8)=v 2 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 3) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 2 := h1
            have hb : A (v 3) (v 8)=v 2 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 1) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 1)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 4 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 4 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 4 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 4 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 4 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 4 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))


private theorem in342_nine_chunk33 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 178]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 178]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 66])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 165])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 165])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 179]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 179]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 67])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 151])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 173])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 151]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 158])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 4) → (A (v 3) (v 6)=v 4) → False
          intro h1 h2
          have ha : A (v 3) (v 2)=v 4 := (hsym _ _).trans h1
          have hb : A (v 3) (v 6)=v 4 := h2
          exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 4 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 4 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 4 := h1
            have hb : A (v 3) (v 7)=v 4 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 4 := h1
            have hb : A (v 3) (v 8)=v 4 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 4 := h1
            have hb : A (v 3) (v 8)=v 4 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 1) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 1)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 5 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 5 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 5 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 5 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 5 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 5 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 5) → (A (v 3) (v 8)=v 5) → False
          intro h1 h2
          have ha : A (v 3) (v 2)=v 5 := (hsym _ _).trans h1
          have hb : A (v 3) (v 8)=v 5 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 5 := h1
            have hb : A (v 3) (v 7)=v 5 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 5 := h1
            have hb : A (v 3) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 5 := h1
            have hb : A (v 3) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 1) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 6 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 6 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 6 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 6 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 6 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 6 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 6 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 6 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 6 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))


private theorem in342_nine_chunk34 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 158]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 180]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 110])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 152]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 181])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 181]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 159]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 166]) (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 166]) (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 181])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 111])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 20,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 111,Sat.Literal.neg 174])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 6) → (A (v 3) (v 5)=v 6) → False
          intro h1 h2
          have ha : A (v 3) (v 4)=v 6 := h1
          have hb : A (v 3) (v 5)=v 6 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 6 := h1
            have hb : A (v 3) (v 7)=v 6 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 6 := h1
            have hb : A (v 3) (v 8)=v 6 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 6 := h1
            have hb : A (v 3) (v 7)=v 6 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 6 := h1
            have hb : A (v 3) (v 8)=v 6 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 3) (v 7)=v 6 := h1
            have hb : A (v 3) (v 8)=v 6 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 3)=v 7) → (A (v 3) (v 4)=v 7) → False
          intro h1 h2
          have ha : A (v 3) (v 0)=v 7 := (hsym _ _).trans h1
          have hb : A (v 3) (v 4)=v 7 := h2
          exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 7 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 7 := h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 7 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 7) → (A (v 3) (v 5)=v 7) → False
          intro h1 h2
          have ha : A (v 3) (v 4)=v 7 := h1
          have hb : A (v 3) (v 5)=v 7 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 7 := h1
            have hb : A (v 3) (v 6)=v 7 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 7 := h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 7) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 7 := h1
            have hb : A (v 3) (v 6)=v 7 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 7 := h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 7 := h1
            have hb : A (v 3) (v 8)=v 7 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 3) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 8 := h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 8 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 8 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 8 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 4)=v 8 := h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 5)=v 8 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 6)=v 8 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 3) (v 7)=v 8 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))


private theorem in342_nine_chunk35 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 160]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 112])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 147]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 182])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 189]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 196]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 147])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 182]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 189]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 196]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 182]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 189]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 196])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 189])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 203])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 203]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 113])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 183])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 8) → (A (v 3) (v 5)=v 8) → False
          intro h1 h2
          have ha : A (v 3) (v 4)=v 8 := h1
          have hb : A (v 3) (v 5)=v 8 := h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 8 := h1
            have hb : A (v 3) (v 6)=v 8 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 4)=v 8 := h1
            have hb : A (v 3) (v 7)=v 8 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 8 := h1
            have hb : A (v 3) (v 6)=v 8 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 5)=v 8 := h1
            have hb : A (v 3) (v 7)=v 8 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 3) (v 6)=v 8 := h1
            have hb : A (v 3) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 3) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 2) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 3) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 4) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 0 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 0 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 0 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 3) (v 4)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 4) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 0 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 0 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 4)=v 0) → (A (v 4) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 4) (v 2)=v 0 := (hsym _ _).trans h1
          have hb : A (v 4) (v 7)=v 0 := h2
          exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 4) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 0 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 0 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 0 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 0 := h1
            have hb : A (v 4) (v 6)=v 0 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 0 := h1
            have hb : A (v 4) (v 7)=v 0 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 0 := h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 0 := h1
            have hb : A (v 4) (v 7)=v 0 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 0 := h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 0 := h1
            have hb : A (v 4) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 2) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 3) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 1 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))


private theorem in342_nine_chunk36 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 190]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 197]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 204]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 148]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 183])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 197])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 204]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 190]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 197]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 204])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 197]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 197]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 191])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 198]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 198]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 205]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 72])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 192])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 1) → (A (v 4) (v 6)=v 1) → False
          intro h1 h2
          have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
          have hb : A (v 4) (v 6)=v 1 := h2
          exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 1 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 4) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 1 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 3) (v 4)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 1 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 1 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 1 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 4)=v 1) → (A (v 4) (v 8)=v 1) → False
          intro h1 h2
          have ha : A (v 4) (v 2)=v 1 := (hsym _ _).trans h1
          have hb : A (v 4) (v 8)=v 1 := h2
          exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 1 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 1 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 1 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 4) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 1 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 1 := h1
            have hb : A (v 4) (v 6)=v 1 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 1 := h1
            have hb : A (v 4) (v 7)=v 1 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 6)=v 1) → (A (v 4) (v 7)=v 1) → False
          intro h1 h2
          have ha : A (v 4) (v 6)=v 1 := h1
          have hb : A (v 4) (v 7)=v 1 := h2
          exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 1) → (A (v 4) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 1 := h1
            have hb : A (v 4) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 4) (v 5)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 2 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 4) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 2 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 4) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 2 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 2 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 2 := h1
            have hb : A (v 4) (v 6)=v 2 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 2 := h1
            have hb : A (v 4) (v 7)=v 2 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 2 := h1
            have hb : A (v 4) (v 8)=v 2 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 4) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 2 := h1
            have hb : A (v 4) (v 7)=v 2 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 2 := h1
            have hb : A (v 4) (v 8)=v 2 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 2 := h1
            have hb : A (v 4) (v 8)=v 2 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 1) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 1)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 3 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))


private theorem in342_nine_chunk37 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 199]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 114]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 199])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 73])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 115]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 193]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 200]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 193]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 193])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 207])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 207]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 74])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 151])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 3) → (A (v 4) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 4) (v 0)=v 3 := (hsym _ _).trans h1
          have hb : A (v 4) (v 7)=v 3 := h2
          exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 3 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 3 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 3 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 3 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 3 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 3 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 3 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 3 := h1
            have hb : A (v 4) (v 7)=v 3 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 3 := h1
            have hb : A (v 4) (v 8)=v 3 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 3 := h1
            have hb : A (v 4) (v 8)=v 3 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 1) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 1)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 5 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 5) → (A (v 4) (v 7)=v 5) → False
          intro h1 h2
          have ha : A (v 4) (v 0)=v 5 := (hsym _ _).trans h1
          have hb : A (v 4) (v 7)=v 5 := h2
          exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 5 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 5 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 5 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 5 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 5 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 5 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 5 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 5 := h1
            have hb : A (v 4) (v 7)=v 5 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 5 := h1
            have hb : A (v 4) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 5 := h1
            have hb : A (v 4) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 1) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))


private theorem in342_nine_chunk38 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 186]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 201])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 151])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 201]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 75]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 117]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 187]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 152])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 209]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 194])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 209])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 6) → (A (v 4) (v 5)=v 6) → False
          intro h1 h2
          have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
          have hb : A (v 4) (v 5)=v 6 := h2
          exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 6 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 6 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 6 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 6 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 6 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 6 := h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 4) (v 7)=v 6 := h1
            have hb : A (v 4) (v 8)=v 6 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 1) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 1)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 4) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 7) → (A (v 2) (v 4)=v 7) → False
          intro h1 h2
          have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
          have hb : A (v 4) (v 2)=v 7 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 7 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 7 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 7 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 7 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 7 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 7 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 7 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 7 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 7 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 4) (v 8)=v 7 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 7 := h1
            have hb : A (v 4) (v 8)=v 7 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))


private theorem in342_nine_chunk39 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 194,Sat.Literal.neg 209]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 27,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 118])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 188])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 76,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 118,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 153,Sat.Literal.neg 202]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 195]) (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 202]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 195,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 119])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 154]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 182])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 217])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 154]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 182]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 224])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 6)=v 7) → (A (v 4) (v 8)=v 7) → False
          intro h1 h2
          have ha : A (v 4) (v 6)=v 7 := h1
          have hb : A (v 4) (v 8)=v 7 := h2
          exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 8 := h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 8 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 8 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 8) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 4) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 8) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 8 := h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 8 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 8) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 8 := h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 7)=v 8 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 5)=v 8 := h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 4) (v 6)=v 8 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 8) → (A (v 4) (v 7)=v 8) → False
          intro h1 h2
          have ha : A (v 4) (v 3)=v 8 := (hsym _ _).trans h1
          have hb : A (v 4) (v 7)=v 8 := h2
          exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 8 := h1
            have hb : A (v 4) (v 6)=v 8 := h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 5)=v 8 := h1
            have hb : A (v 4) (v 7)=v 8 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 4) (v 6)=v 8 := h1
            have hb : A (v 4) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 4) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 2) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 3) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 4) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 0 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 0 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 3) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 4) (v 5)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 0 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 0 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))


private theorem in342_nine_chunk40 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 182]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 217]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 224])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 217]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 224]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 120]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 155])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 211]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 218]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 155]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 211])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 225])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 211])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 225]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 218])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 218])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 5)=v 0) → (A (v 4) (v 5)=v 0) → False
          intro h1 h2
          have ha : A (v 5) (v 3)=v 0 := (hsym _ _).trans h1
          have hb : A (v 5) (v 4)=v 0 := (hsym _ _).trans h2
          exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 0 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 0 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 0 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 0 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 6)=v 0) → (A (v 5) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 5) (v 6)=v 0 := h1
          have hb : A (v 5) (v 7)=v 0 := h2
          exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 0 := h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 5) (v 7)=v 0 := h1
            have hb : A (v 5) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 2) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 3) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 1 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 1) → (A (v 5) (v 7)=v 1) → False
          intro h1 h2
          have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
          have hb : A (v 5) (v 7)=v 1 := h2
          exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 1 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 3) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 1 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 1 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 1 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 1 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 1 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 1 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 1 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 1 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 1 := h1
            have hb : A (v 5) (v 7)=v 1 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))


private theorem in342_nine_chunk41 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 225]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 225]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 219])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 212])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 226])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 226]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 79])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 213]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 220]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 121]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 213]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 213])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 227]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 227]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 80])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 122]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 214])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 6)=v 1) → (A (v 5) (v 8)=v 1) → False
          intro h1 h2
          have ha : A (v 5) (v 6)=v 1 := h1
          have hb : A (v 5) (v 8)=v 1 := h2
          exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 5) (v 7)=v 1 := h1
            have hb : A (v 5) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 4) (v 5)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 2 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 2 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 2 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 2 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 2 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 2 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 2 := h1
            have hb : A (v 5) (v 7)=v 2 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 2 := h1
            have hb : A (v 5) (v 8)=v 2 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 5) (v 7)=v 2 := h1
            have hb : A (v 5) (v 8)=v 2 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 1) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 1)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 3 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 3) → (A (v 5) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 5) (v 0)=v 3 := (hsym _ _).trans h1
          have hb : A (v 5) (v 7)=v 3 := h2
          exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 3 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 3 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 3 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 3 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 3 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 3 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 3 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 3 := h1
            have hb : A (v 5) (v 7)=v 3 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 3 := h1
            have hb : A (v 5) (v 8)=v 3 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 5) (v 7)=v 3 := h1
            have hb : A (v 5) (v 8)=v 3 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 1) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 1)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 4 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))


private theorem in342_nine_chunk42 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 214])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 228])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 123]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 158]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 222]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 123])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 222])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 158])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 229]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 229])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 4) → (A (v 5) (v 7)=v 4) → False
          intro h1 h2
          have ha : A (v 5) (v 0)=v 4 := (hsym _ _).trans h1
          have hb : A (v 5) (v 7)=v 4 := h2
          exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 4 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 4 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 4 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 4 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 4 := h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 5)=v 4) → (A (v 5) (v 7)=v 4) → False
          intro h1 h2
          have ha : A (v 5) (v 2)=v 4 := (hsym _ _).trans h1
          have hb : A (v 5) (v 7)=v 4 := h2
          exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 4 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 4) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 4 := h1
            have hb : A (v 5) (v 7)=v 4 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 4 := h1
            have hb : A (v 5) (v 8)=v 4 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 5) (v 7)=v 4 := h1
            have hb : A (v 5) (v 8)=v 4 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 6) → (A (v 3) (v 5)=v 6) → False
          intro h1 h2
          have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
          have hb : A (v 5) (v 3)=v 6 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 6 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 6 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 6 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 6 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 6 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 6 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 6 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 6 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 6 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 6 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))


private theorem in342_nine_chunk43 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 222,Sat.Literal.neg 229]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 124]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 230])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 159])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 215]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 159])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 230]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 187]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 230]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 230])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 215,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 83])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 216]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 34,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 188])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 7)=v 6) → (A (v 5) (v 8)=v 6) → False
          intro h1 h2
          have ha : A (v 5) (v 7)=v 6 := h1
          have hb : A (v 5) (v 8)=v 6 := h2
          exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 1)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 7 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 7 := h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 5)=v 7) → (A (v 4) (v 5)=v 7) → False
          intro h1 h2
          have ha : A (v 5) (v 3)=v 7 := (hsym _ _).trans h1
          have hb : A (v 5) (v 4)=v 7 := (hsym _ _).trans h2
          exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 7 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 7 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 7 := (hsym _ _).trans h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 7 := h1
            have hb : A (v 5) (v 8)=v 7 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 1)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 8 := h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 8 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 8) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 8) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))


private theorem in342_nine_chunk44 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 216]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 83,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 160]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 125,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 216])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 160,Sat.Literal.neg 223]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 188,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 216,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 126])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 189]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 210]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 238]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 161]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 189])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 231])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 189])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 210]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 231]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 210])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 238])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 5)=v 8) → (A (v 5) (v 6)=v 8) → False
          intro h1 h2
          have ha : A (v 5) (v 1)=v 8 := (hsym _ _).trans h1
          have hb : A (v 5) (v 6)=v 8 := h2
          exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 8 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 8) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 8 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 8) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 8 := h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 5)=v 8) → (A (v 5) (v 7)=v 8) → False
          intro h1 h2
          have ha : A (v 5) (v 3)=v 8 := (hsym _ _).trans h1
          have hb : A (v 5) (v 7)=v 8 := h2
          exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 6)=v 8 := h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 4)=v 8 := (hsym _ _).trans h1
            have hb : A (v 5) (v 7)=v 8 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 5) (v 6)=v 8 := h1
            have hb : A (v 5) (v 7)=v 8 := h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 5) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 2) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 6)=v 0) → (A (v 5) (v 6)=v 0) → False
          intro h1 h2
          have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
          have hb : A (v 6) (v 5)=v 0 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 0 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 3) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 0 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 4) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 0 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 5) (v 6)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 0 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))


private theorem in342_nine_chunk45 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 231]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 238]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 162])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 190]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 211])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 239])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 162]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 190]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 232])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 190]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 211]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 239]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 232])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 232])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 232,Sat.Literal.neg 239])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 212]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 240])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 233])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 6)=v 0) → (A (v 6) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 6) (v 5)=v 0 := (hsym _ _).trans h1
          have hb : A (v 6) (v 7)=v 0 := h2
          exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 0 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 6) (v 7)=v 0 := h1
            have hb : A (v 6) (v 8)=v 0 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 2) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 3) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 1 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 3) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 1 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 4) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 6)=v 1) → (A (v 5) (v 6)=v 1) → False
          intro h1 h2
          have ha : A (v 6) (v 3)=v 1 := (hsym _ _).trans h1
          have hb : A (v 6) (v 5)=v 1 := (hsym _ _).trans h2
          exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 1 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 1) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 1 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 1 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 1 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 6) (v 7)=v 1 := h1
            have hb : A (v 6) (v 8)=v 1 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 4) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 2 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 2) → (A (v 6) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 2 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 2 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 2 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))


private theorem in342_nine_chunk46 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 240]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 233]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 240]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 240]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 86])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 213])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 241]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 213]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 213,Sat.Literal.neg 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 87]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 164])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 129]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 164]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 164])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 6)=v 2) → (A (v 6) (v 8)=v 2) → False
          intro h1 h2
          have ha : A (v 6) (v 4)=v 2 := (hsym _ _).trans h1
          have hb : A (v 6) (v 8)=v 2 := h2
          exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 2 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 6) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 2 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 2 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 2) → (A (v 6) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 6) (v 7)=v 2 := h1
            have hb : A (v 6) (v 8)=v 2 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 1) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 1)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 3 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 3 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 3 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 3 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 3 := h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 3 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 6)=v 3) → (A (v 5) (v 6)=v 3) → False
          intro h1 h2
          have ha : A (v 6) (v 4)=v 3 := (hsym _ _).trans h1
          have hb : A (v 6) (v 5)=v 3 := (hsym _ _).trans h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 3 := h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 3 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 3 := h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 3 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 1)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 4 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 4 := h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 4) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))


private theorem in342_nine_chunk47 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 235]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 235]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 214,Sat.Literal.neg 242]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 242])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 130])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 165]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 236]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 193])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 243])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 236,Sat.Literal.neg 243]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 166])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 6)=v 4) → (A (v 6) (v 7)=v 4) → False
          intro h1 h2
          have ha : A (v 6) (v 2)=v 4 := (hsym _ _).trans h1
          have hb : A (v 6) (v 7)=v 4 := h2
          exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 4 := h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 5)=v 4 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 6) (v 7)=v 4 := h1
            have hb : A (v 6) (v 8)=v 4 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 1)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 7)=v 5 := h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 6)=v 5) → (A (v 6) (v 7)=v 5) → False
          intro h1 h2
          have ha : A (v 6) (v 1)=v 5 := (hsym _ _).trans h1
          have hb : A (v 6) (v 7)=v 5 := h2
          exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 5 := (hsym _ _).trans h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 6) (v 7)=v 5 := h1
            have hb : A (v 6) (v 8)=v 5 := h2
            exact (by decide : (7:Fin 9)≠8) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 1)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 7) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 7) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))

theorem wild_valid_triples_nine_encoding_part_c {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla in342_nine_formula_c := by
  exact (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk32 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk33 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk34 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk35 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk36 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk37 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk38 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk39 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk40 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk41 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk42 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk43 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk44 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk45 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk46 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk47 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))))
