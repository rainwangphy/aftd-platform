import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineSatCore

/-!
# wild_valid_triples_nine_encoding_part_d

Topic: graphs   Node: de5853c9b8a3

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed. The former combined helper timed out in the180-second interactive gate. This is the SAME checked certificate and mathematical interpretation, split into a core and four soundness modules; no gate budget, axiom or mathematical statement is weakened.

Under the generic normalized-array assumptions and the assumption of no valid nine-vertex rearrangement, the induced equality valuation satisfies this explicit part of the fixed CNF. Every clause is proved from the array assumptions or an explicitly bijective candidate partition. This is an interpretation helper, not a standalone graph result.
-/

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
def in342_nine_formula_d : Sat.Fmla := (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 194]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 215]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 194,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 90])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 132]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 216]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 195,Sat.Literal.neg 216])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 133]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 168])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 217]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 196])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 217]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 217])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 245])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 231])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 197]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 218]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 197])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 232])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 246]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 218])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 233]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 247]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 233]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 233])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 247])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 93]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 199]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 234])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 199]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 220]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 234])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 234])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 94]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 171])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 249]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 221]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 235])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 95]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 137]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 172]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 250]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 250])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 236,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 96]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 173])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 222])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 201]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 201])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 201])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 222]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 139]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 139]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 174]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 174,Sat.Literal.neg 202])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 174,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 202,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 175]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 224])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 245])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 175]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 224]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 238])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 224])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 141]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 176]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 225]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 176])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 225])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 246])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 247]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 240]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 247]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 241])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 248])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 143]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 178]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 242])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 242])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 102]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 144])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 144,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 144,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 243,Sat.Literal.neg 250]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 145]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 180]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 229]))))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 208,Sat.Literal.neg 229]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 146])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 181]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 230]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 181,Sat.Literal.neg 209]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 181,Sat.Literal.neg 230]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 209,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 0])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 150]) (Sat.Fmla.one [Sat.Literal.neg 157]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 185]) (Sat.Fmla.one [Sat.Literal.neg 237])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 244]) (Sat.Fmla.one [Sat.Literal.neg 251]))))))))))
private theorem in342_nine_chunk48 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 194]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 215]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 166,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 194,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 90])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 132]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 41,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 90,Sat.Literal.neg 216]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 132,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 167,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 195,Sat.Literal.neg 216])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 133]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 168])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 217]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 168]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 196])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 6)=v 7) → (A (v 4) (v 6)=v 7) → False
          intro h1 h2
          have ha : A (v 6) (v 1)=v 7 := (hsym _ _).trans h1
          have hb : A (v 6) (v 4)=v 7 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 7) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 7) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 7 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 8) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 1)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 6)=v 8) → (A (v 2) (v 6)=v 8) → False
          intro h1 h2
          have ha : A (v 6) (v 0)=v 8 := (hsym _ _).trans h1
          have hb : A (v 6) (v 2)=v 8 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 8) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 6)=v 8) → (A (v 5) (v 6)=v 8) → False
          intro h1 h2
          have ha : A (v 6) (v 1)=v 8 := (hsym _ _).trans h1
          have hb : A (v 6) (v 5)=v 8 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 8) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 8) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 6) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 8) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            have ha : A (v 6) (v 4)=v 8 := (hsym _ _).trans h1
            have hb : A (v 6) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 6) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 2) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 0 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 3) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))


private theorem in342_nine_chunk49 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 217]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 196]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 217])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 245])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 217]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 231])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 231]) (Sat.Fmla.one [Sat.Literal.neg 217,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 231,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 134])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 197]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 218]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 169]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 197])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 232])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 246]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 218])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 218]) (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 218,Sat.Literal.neg 232]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 233])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 7)=v 0) → (A (v 5) (v 7)=v 0) → False
          intro h1 h2
          have ha : A (v 7) (v 2)=v 0 := (hsym _ _).trans h1
          have hb : A (v 7) (v 5)=v 0 := (hsym _ _).trans h2
          exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 0 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 4) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 0 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 5) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 6) (v 7)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 0 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 7) (v 6)=v 0 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 0 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 2) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 3) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 7)=v 1) → (A (v 5) (v 7)=v 1) → False
          intro h1 h2
          have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
          have hb : A (v 7) (v 5)=v 1 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 1 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 3) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 4) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 1 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 1) → (A (v 5) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 1) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 1 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 1) → (A (v 6) (v 7)=v 1) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 1 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 4) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))


private theorem in342_nine_chunk50 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 247]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 219]) (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 233]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 233])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 219,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 233,Sat.Literal.neg 247])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 93]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 199]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 234])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 199]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 220]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 234]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 220]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 234])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 234])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 220,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 94]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 171])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 7)=v 2) → (A (v 7) (v 8)=v 2) → False
          intro h1 h2
          have ha : A (v 7) (v 3)=v 2 := (hsym _ _).trans h1
          have hb : A (v 7) (v 8)=v 2 := h2
          exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 5) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 2 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 2 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 2 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 6) (v 7)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 2 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 2 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 7) (v 6)=v 2 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 2 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 7)=v 3) → (A (v 1) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
          have hb : A (v 7) (v 1)=v 3 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 3 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 3) → (A (v 5) (v 7)=v 3) → False
          intro h1 h2
          have ha : A (v 7) (v 1)=v 3 := (hsym _ _).trans h1
          have hb : A (v 7) (v 5)=v 3 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 3 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 5) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 3 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 3 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 6) (v 7)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 3 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 1) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 1)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 4 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))


private theorem in342_nine_chunk51 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 221]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 249]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 221]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 235])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 221,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 235,Sat.Literal.neg 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 95]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 137]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 172]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 172]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 250]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 250])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 236]) (Sat.Fmla.one [Sat.Literal.neg 200,Sat.Literal.neg 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 236,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 96]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 138]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 173])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 222])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 4) → (A (v 5) (v 7)=v 4) → False
          intro h1 h2
          have ha : A (v 7) (v 1)=v 4 := (hsym _ _).trans h1
          have hb : A (v 7) (v 5)=v 4 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 4) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 4 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 5) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 4 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 4) → (A (v 6) (v 7)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 7)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 5)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 4 := h2
            exact (by decide : (5:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 7) (v 6)=v 4 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 4 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 1) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 1)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (0:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 5) → (A (v 3) (v 7)=v 5) → False
          intro h1 h2
          have ha : A (v 7) (v 1)=v 5 := (hsym _ _).trans h1
          have hb : A (v 7) (v 3)=v 5 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (1:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (2:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 5) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 5) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (3:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 5) → (A (v 6) (v 7)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (4:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 7) (v 6)=v 5 := (hsym _ _).trans h1
            have hb : A (v 7) (v 8)=v 5 := h2
            exact (by decide : (6:Fin 9)≠8) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))


private theorem in342_nine_chunk52 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 201]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 201])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 222]) (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 201])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 222]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 139]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 48,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 139]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 174]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 97,Sat.Literal.neg 223]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 139,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 174,Sat.Literal.neg 202])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 174,Sat.Literal.neg 223]) (Sat.Fmla.one [Sat.Literal.neg 202,Sat.Literal.neg 223])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 140]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 175]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 224])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 245])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 6) → (A (v 2) (v 7)=v 6) → False
          intro h1 h2
          have ha : A (v 7) (v 1)=v 6 := (hsym _ _).trans h1
          have hb : A (v 7) (v 2)=v 6 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 6) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 6) → (A (v 5) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 6) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 7)=v 6) → (A (v 5) (v 7)=v 6) → False
          intro h1 h2
          have ha : A (v 7) (v 4)=v 6 := (hsym _ _).trans h1
          have hb : A (v 7) (v 5)=v 6 := (hsym _ _).trans h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 8) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 1)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 0)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 8) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 2)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 7) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 8) → (A (v 3) (v 7)=v 8) → False
          intro h1 h2
          have ha : A (v 7) (v 1)=v 8 := (hsym _ _).trans h1
          have hb : A (v 7) (v 3)=v 8 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 1)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 8) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 3)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 2)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 8) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 4)=v 8 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 7) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 3)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 8) → (A (v 5) (v 7)=v 8) → False
            intro h1 h2
            have ha : A (v 7) (v 4)=v 8 := (hsym _ _).trans h1
            have hb : A (v 7) (v 5)=v 8 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 7) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 2) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 3) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))


private theorem in342_nine_chunk53 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 175]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 203]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 224]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 224]) (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 238])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 224])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 245]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 238]) (Sat.Fmla.one [Sat.Literal.neg 224,Sat.Literal.neg 245])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 238,Sat.Literal.neg 245]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 141]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 176]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 225]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 176])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 204]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 225])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 246])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 239]) (Sat.Fmla.one [Sat.Literal.neg 225,Sat.Literal.neg 246]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 205]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 226]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 247])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 8)=v 0) → (A (v 3) (v 8)=v 0) → False
          intro h1 h2
          have ha : A (v 8) (v 2)=v 0 := (hsym _ _).trans h1
          have hb : A (v 8) (v 3)=v 0 := (hsym _ _).trans h2
          exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 4) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 5) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 6) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 0 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 0) → (A (v 7) (v 8)=v 0) → False
            intro h1 h2
            have ha : A (v 8) (v 6)=v 0 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 0 := (hsym _ _).trans h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 8)=v 1) → (A (v 3) (v 8)=v 1) → False
          intro h1 h2
          have ha : A (v 8) (v 0)=v 1 := (hsym _ _).trans h1
          have hb : A (v 8) (v 3)=v 1 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 4) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 4) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 5) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 1 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 1) → (A (v 6) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 1 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 1) → (A (v 7) (v 8)=v 1) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 1 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 1 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 2) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 2 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 5) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 2 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 2 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))


private theorem in342_nine_chunk54 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 240]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 226,Sat.Literal.neg 247]) (Sat.Fmla.one [Sat.Literal.neg 240,Sat.Literal.neg 247]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 241])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 241]) (Sat.Fmla.one [Sat.Literal.neg 227,Sat.Literal.neg 248])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 241,Sat.Literal.neg 248]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 143]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 178]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 143]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 242])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 228]) (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 249]) (Sat.Fmla.one [Sat.Literal.neg 228,Sat.Literal.neg 242])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 5) (v 8)=v 2) → (A (v 6) (v 8)=v 2) → False
          intro h1 h2
          have ha : A (v 8) (v 5)=v 2 := (hsym _ _).trans h1
          have hb : A (v 8) (v 6)=v 2 := (hsym _ _).trans h2
          exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 2 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 2) → (A (v 7) (v 8)=v 2) → False
            intro h1 h2
            have ha : A (v 8) (v 6)=v 2 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 2 := (hsym _ _).trans h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 3 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 5) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 3 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 3 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 3) → (A (v 6) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 3 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 3 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 3) → (A (v 7) (v 8)=v 3) → False
            intro h1 h2
            have ha : A (v 8) (v 6)=v 3 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 3 := (hsym _ _).trans h2
            exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 8)=v 4) → (A (v 3) (v 8)=v 4) → False
          intro h1 h2
          have ha : A (v 8) (v 0)=v 4 := (hsym _ _).trans h1
          have hb : A (v 8) (v 3)=v 4 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 4 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 4) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 4 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 5) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 7) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 4 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 8)=v 4) → (A (v 6) (v 8)=v 4) → False
            intro h1 h2
            have ha : A (v 8) (v 5)=v 4 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 4 := (hsym _ _).trans h2
            exact (by decide : (5:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))


private theorem in342_nine_chunk55 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 102]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 144])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 144,Sat.Literal.neg 179]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 144,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 250]) (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 243,Sat.Literal.neg 250]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 103]) (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 145]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 180]) (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 208])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 229]) (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 180]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 229])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 229])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 8)=v 5) → (A (v 1) (v 8)=v 5) → False
          intro h1 h2
          have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
          have hb : A (v 8) (v 1)=v 5 := (hsym _ _).trans h2
          exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 5) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 5) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 5 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 5) → (A (v 6) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 6)=v 5 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠6) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 5 := (hsym _ _).trans h1
            have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 6) (v 8)=v 5) → (A (v 7) (v 8)=v 5) → False
          intro h1 h2
          have ha : A (v 8) (v 6)=v 5 := (hsym _ _).trans h1
          have hb : A (v 8) (v 7)=v 5 := (hsym _ _).trans h2
          exact (by decide : (6:Fin 9)≠7) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 1)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 6) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 6) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 6) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 6 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 6) → (A (v 5) (v 8)=v 6) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 6 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 6 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))


private theorem in342_nine_chunk56 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 208,Sat.Literal.neg 229]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 55,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 146])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 181]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 104,Sat.Literal.neg 230]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 209])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 146,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.neg 181,Sat.Literal.neg 209]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 181,Sat.Literal.neg 230]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 209,Sat.Literal.neg 230]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 1,Sat.Literal.pos 14,Sat.Literal.pos 63,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 8)=v 6) → (A (v 5) (v 8)=v 6) → False
          intro h1 h2
          have ha : A (v 8) (v 4)=v 6 := (hsym _ _).trans h1
          have hb : A (v 8) (v 5)=v 6 := (hsym _ _).trans h2
          exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 7) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 1)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠1) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 0)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (0:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 7) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 2)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠2) (hv (hinj (v 8) (ha.trans hb.symm)))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 8)=v 7) → (A (v 3) (v 8)=v 7) → False
          intro h1 h2
          have ha : A (v 8) (v 1)=v 7 := (hsym _ _).trans h1
          have hb : A (v 8) (v 3)=v 7 := (hsym _ _).trans h2
          exact (by decide : (1:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 1)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (1:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 7) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 3)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠3) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 2)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (2:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 7) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 3)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 4)=v 7 := (hsym _ _).trans h2
            exact (by decide : (3:Fin 9)≠4) (hv (hinj (v 8) (ha.trans hb.symm)))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 8)=v 7) → (A (v 5) (v 8)=v 7) → False
          intro h1 h2
          have ha : A (v 8) (v 3)=v 7 := (hsym _ _).trans h1
          have hb : A (v 8) (v 5)=v 7 := (hsym _ _).trans h2
          exact (by decide : (3:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 7) → (A (v 5) (v 8)=v 7) → False
            intro h1 h2
            have ha : A (v 8) (v 4)=v 7 := (hsym _ _).trans h1
            have hb : A (v 8) (v 5)=v 7 := (hsym _ _).trans h2
            exact (by decide : (4:Fin 9)≠5) (hv (hinj (v 8) (ha.trans hb.symm)))
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 4)=v 5)) → (¬ (A (v 2) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 2)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,4,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 5 ∧ A (v 2) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,4,6,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,4,7,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,4,8,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,5,6,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,5,7,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → (¬ (A (v 4) (v 6)=v 7)) → (¬ (A (v 4) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,5,8,4,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 7 ∧ A (v 4) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,6,7,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → (¬ (A (v 4) (v 5)=v 7)) → (¬ (A (v 4) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,6,8,4,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 7 ∧ A (v 4) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 3)) → (¬ (A (v 0) (v 3)=v 1)) → (¬ (A (v 1) (v 3)=v 0)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,3,2,7,8,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 3 ∧ A (v 0) (v 3)≠v 1 ∧ A (v 1) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 3)=v 5)) → (¬ (A (v 2) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 2)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,3,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 5 ∧ A (v 2) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,3,6,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,3,7,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk57 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 2,Sat.Literal.pos 21,Sat.Literal.pos 70,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 3,Sat.Literal.pos 28,Sat.Literal.pos 77,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 4,Sat.Literal.pos 35,Sat.Literal.pos 84,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 115,Sat.Literal.pos 122,Sat.Literal.pos 184,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,5,6,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
            exact ⟨h3,h4,h5⟩
          · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,5,7,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → (¬ (A (v 3) (v 6)=v 7)) → (¬ (A (v 3) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,5,8,3,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 7 ∧ A (v 3) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,6,7,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,6,8,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 4)) → (¬ (A (v 0) (v 4)=v 1)) → (¬ (A (v 1) (v 4)=v 0)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,4,2,7,8,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 4 ∧ A (v 0) (v 4)≠v 1 ∧ A (v 1) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,3,4,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,3,6,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,3,7,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,4,6,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,4,7,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,6,7,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,6,8,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 5)) → (¬ (A (v 0) (v 5)=v 1)) → (¬ (A (v 1) (v 5)=v 0)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,5,2,7,8,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 5 ∧ A (v 0) (v 5)≠v 1 ∧ A (v 1) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,3,4,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 3)=v 5)) → (¬ (A (v 2) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 2)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,3,5,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 2) (v 3)≠v 5 ∧ A (v 2) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 2
            exact ⟨h3,h4,h5⟩
          · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,3,7,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 4)=v 5)) → (¬ (A (v 2) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 2)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,4,5,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 5 ∧ A (v 2) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,4,7,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,4,8,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,5,7,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,5,8,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 6)) → (¬ (A (v 0) (v 6)=v 1)) → (¬ (A (v 1) (v 6)=v 0)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,6,2,7,8,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 6 ∧ A (v 0) (v 6)≠v 1 ∧ A (v 1) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,3,4,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 3)=v 5)) → (¬ (A (v 2) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 2)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,3,5,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 5 ∧ A (v 2) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,3,6,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 4)=v 5)) → (¬ (A (v 2) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 2)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,4,5,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 5 ∧ A (v 2) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,4,6,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,4,8,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,5,6,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk58 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 5,Sat.Literal.pos 42,Sat.Literal.pos 91,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 6,Sat.Literal.pos 49,Sat.Literal.pos 98,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 8,Sat.Literal.pos 15,Sat.Literal.pos 105,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 9,Sat.Literal.pos 22,Sat.Literal.pos 112,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,5,8,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
            exact ⟨h3,h4,h5⟩
          · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 7)) → (¬ (A (v 0) (v 7)=v 1)) → (¬ (A (v 1) (v 7)=v 0)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,7,2,6,8,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 7 ∧ A (v 0) (v 7)≠v 1 ∧ A (v 1) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,3,4,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,3,7,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,4,7,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,5,6,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,5,7,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 8)) → (¬ (A (v 0) (v 8)=v 1)) → (¬ (A (v 1) (v 8)=v 0)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,1,8,2,6,7,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 1)≠v 8 ∧ A (v 0) (v 8)≠v 1 ∧ A (v 1) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 4)=v 5)) → (¬ (A (v 1) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,4,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 5 ∧ A (v 1) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,4,6,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,4,7,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,4,8,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,5,6,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,5,7,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 4) (v 6)=v 7)) → (¬ (A (v 4) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,5,8,4,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 7 ∧ A (v 4) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,6,7,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 6)=v 8)) → (¬ (A (v 1) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 1)) → (¬ (A (v 4) (v 5)=v 7)) → (¬ (A (v 4) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,6,8,4,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 8 ∧ A (v 1) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 7 ∧ A (v 4) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 3)) → (¬ (A (v 0) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,3,1,7,8,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 3 ∧ A (v 0) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 3)=v 5)) → (¬ (A (v 1) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,3,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 5 ∧ A (v 1) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,3,6,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,3,7,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,3,8,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,5,6,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,5,7,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,6,7,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 6)=v 8)) → (¬ (A (v 1) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,6,8,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 8 ∧ A (v 1) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 4)) → (¬ (A (v 0) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,4,1,7,8,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 4 ∧ A (v 0) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,3,4,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,3,6,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,4,6,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk59 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 10,Sat.Literal.pos 29,Sat.Literal.pos 119,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 11,Sat.Literal.pos 36,Sat.Literal.pos 126,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 12,Sat.Literal.pos 43,Sat.Literal.pos 133,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.one [Sat.Literal.pos 13,Sat.Literal.pos 50,Sat.Literal.pos 140,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,4,7,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 3) (v 6)=v 7)) → (¬ (A (v 3) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,4,8,3,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 7 ∧ A (v 3) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,6,7,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 6)=v 8)) → (¬ (A (v 1) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,6,8,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 8 ∧ A (v 1) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 5)) → (¬ (A (v 0) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,5,1,7,8,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 5 ∧ A (v 0) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,3,4,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,3,7,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 5)) → (¬ (A (v 1) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,4,5,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 5 ∧ A (v 1) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,4,7,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,4,8,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,5,7,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,5,8,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 6)) → (¬ (A (v 0) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,6,1,7,8,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 6 ∧ A (v 0) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,3,4,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 5)) → (¬ (A (v 1) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 1)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,3,5,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 5 ∧ A (v 1) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,3,6,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,3,8,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 5)) → (¬ (A (v 1) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,4,5,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 5 ∧ A (v 1) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,4,6,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,5,6,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,5,8,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 7)) → (¬ (A (v 0) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 0)) → (¬ (A (v 1) (v 6)=v 8)) → (¬ (A (v 1) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,7,1,6,8,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 7 ∧ A (v 0) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 8 ∧ A (v 1) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,3,4,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,3,7,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,4,6,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,5,6,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,5,7,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 2)=v 8)) → (¬ (A (v 0) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,2,8,1,6,7,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 2)≠v 8 ∧ A (v 0) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,2,5,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,2,6,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk60 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 16,Sat.Literal.pos 23,Sat.Literal.pos 147,Sat.Literal.pos 90,Sat.Literal.pos 103,Sat.Literal.pos 239,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 17,Sat.Literal.pos 30,Sat.Literal.pos 154,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205]) (Sat.Fmla.one [Sat.Literal.pos 18,Sat.Literal.pos 37,Sat.Literal.pos 161,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 73,Sat.Literal.pos 80,Sat.Literal.pos 183,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,2,7,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,2,8,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,5,6,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,5,8,2,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,6,7,2,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 4)) → (¬ (A (v 0) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 0)) → (¬ (A (v 1) (v 6)=v 8)) → (¬ (A (v 1) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 1)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,4,1,6,8,2,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 4 ∧ A (v 0) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 8 ∧ A (v 1) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,2,4,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,2,6,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,2,7,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 4) (v 6)=v 7)) → (¬ (A (v 4) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,2,8,4,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 7 ∧ A (v 4) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,4,6,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,4,7,2,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,4,8,2,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 5)) → (¬ (A (v 0) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,5,1,7,8,2,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 5 ∧ A (v 0) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,2,4,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,2,5,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,2,7,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 4) (v 5)=v 7)) → (¬ (A (v 4) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,2,8,4,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 7 ∧ A (v 4) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 5)) → (¬ (A (v 1) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,4,5,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 5 ∧ A (v 1) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,4,7,2,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,4,8,2,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,5,7,2,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 6)) → (¬ (A (v 0) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,6,1,5,8,2,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 6 ∧ A (v 0) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,2,4,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,2,5,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,2,6,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,2,8,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 5)) → (¬ (A (v 1) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 1)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,4,5,2,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 5 ∧ A (v 1) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,4,6,2,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk61 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 19,Sat.Literal.pos 44,Sat.Literal.pos 168,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212]) (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 20,Sat.Literal.pos 51,Sat.Literal.pos 175,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 237,Sat.Literal.pos 244,Sat.Literal.pos 251])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 24,Sat.Literal.pos 31,Sat.Literal.pos 182,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 223,Sat.Literal.pos 230,Sat.Literal.pos 250]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 125,Sat.Literal.pos 144,Sat.Literal.pos 226])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170]) (Sat.Fmla.one [Sat.Literal.pos 25,Sat.Literal.pos 38,Sat.Literal.pos 189,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 216,Sat.Literal.pos 229,Sat.Literal.pos 243]) (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227]) (Sat.Fmla.one [Sat.Literal.pos 26,Sat.Literal.pos 45,Sat.Literal.pos 196,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 3)=v 7)) → (¬ (A (v 0) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,7,1,4,8,2,5,6] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 3)≠v 7 ∧ A (v 0) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,2,4,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 4) (v 6)=v 7)) → (¬ (A (v 4) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,2,5,4,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 7 ∧ A (v 4) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 4) (v 5)=v 7)) → (¬ (A (v 4) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,2,6,4,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 7 ∧ A (v 4) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,2,7,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,4,7,2,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,5,6,2,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 3)=v 8)) → (¬ (A (v 0) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,3,8,1,5,7,2,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 3)≠v 8 ∧ A (v 0) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 6) (v 7)=v 8)) → (¬ (A (v 6) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 6)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,2,3,6,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 6) (v 7)≠v 8 ∧ A (v 6) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 6
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,2,6,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,2,7,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 6)=v 7)) → (¬ (A (v 3) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,2,8,3,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 7 ∧ A (v 3) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,3,6,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,3,7,2,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,3,8,2,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 4)=v 5)) → (¬ (A (v 0) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,5,1,7,8,2,3,6] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 4)≠v 5 ∧ A (v 0) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 5) (v 7)=v 8)) → (¬ (A (v 5) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,2,3,5,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 7)≠v 8 ∧ A (v 5) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,2,5,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,2,7,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,2,8,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 5)) → (¬ (A (v 1) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,3,5,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 5 ∧ A (v 1) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 2) (v 5)=v 8)) → (¬ (A (v 2) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,3,7,2,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 8 ∧ A (v 2) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,3,8,2,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 8)) → (¬ (A (v 2) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,5,7,2,3,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 8 ∧ A (v 2) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,5,8,2,3,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 6)) → (¬ (A (v 0) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 5)) → (¬ (A (v 2) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,6,1,7,8,2,3,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 6 ∧ A (v 0) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 5 ∧ A (v 2) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 2
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 7)) → (¬ (A (v 0) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 5) (v 6)=v 8)) → (¬ (A (v 5) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 5)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,7,1,2,3,5,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 7 ∧ A (v 0) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 5) (v 6)≠v 8 ∧ A (v 5) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 5
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 7)) → (¬ (A (v 0) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,7,1,2,5,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 7 ∧ A (v 0) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 7)) → (¬ (A (v 0) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,7,1,2,6,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 7 ∧ A (v 0) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 7)) → (¬ (A (v 0) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,7,1,2,8,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 7 ∧ A (v 0) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk62 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 215,Sat.Literal.pos 222,Sat.Literal.pos 236]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 66,Sat.Literal.pos 79,Sat.Literal.pos 155,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 124,Sat.Literal.pos 137,Sat.Literal.pos 219]) (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 27,Sat.Literal.pos 52,Sat.Literal.pos 203,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 108,Sat.Literal.pos 121,Sat.Literal.pos 156]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 202,Sat.Literal.pos 209,Sat.Literal.pos 249])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 174,Sat.Literal.pos 181,Sat.Literal.pos 248]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 139,Sat.Literal.pos 146,Sat.Literal.pos 247])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170]) (Sat.Fmla.one [Sat.Literal.pos 32,Sat.Literal.pos 39,Sat.Literal.pos 210,Sat.Literal.pos 97,Sat.Literal.pos 104,Sat.Literal.pos 246,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 195,Sat.Literal.pos 208,Sat.Literal.pos 242]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 167,Sat.Literal.pos 180,Sat.Literal.pos 241])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 132,Sat.Literal.pos 145,Sat.Literal.pos 240]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 118,Sat.Literal.pos 143,Sat.Literal.pos 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 69,Sat.Literal.pos 100,Sat.Literal.pos 176,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 111,Sat.Literal.pos 142,Sat.Literal.pos 177]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 33,Sat.Literal.pos 46,Sat.Literal.pos 217,Sat.Literal.pos 76,Sat.Literal.pos 101,Sat.Literal.pos 204,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 194,Sat.Literal.pos 201,Sat.Literal.pos 235])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 166,Sat.Literal.pos 173,Sat.Literal.pos 234]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 5) (v 6)=v 7)) → (¬ (A (v 5) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 5)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,2,3,5,6,7] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 5) (v 6)≠v 7 ∧ A (v 5) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 5
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 6)=v 7)) → (¬ (A (v 3) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,2,5,3,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 7 ∧ A (v 3) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,2,6,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,2,7,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 5)) → (¬ (A (v 1) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 1)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,3,5,2,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 5 ∧ A (v 1) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 2) (v 5)=v 7)) → (¬ (A (v 2) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,3,6,2,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 7 ∧ A (v 2) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,5,7,2,3,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 4)=v 8)) → (¬ (A (v 0) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 5)) → (¬ (A (v 2) (v 5)=v 3)) → (¬ (A (v 3) (v 5)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,4,8,1,6,7,2,3,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 4)≠v 8 ∧ A (v 0) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 5 ∧ A (v 2) (v 5)≠v 3 ∧ A (v 3) (v 5)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 7)=v 8)) → (¬ (A (v 4) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,2,3,4,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 7)≠v 8 ∧ A (v 4) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 7)=v 8)) → (¬ (A (v 3) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,2,4,3,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 7)≠v 8 ∧ A (v 3) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,2,7,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,2,8,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 2) (v 7)=v 8)) → (¬ (A (v 2) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,3,4,2,7,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 7)≠v 8 ∧ A (v 2) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,3,7,2,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,3,8,2,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 8)) → (¬ (A (v 2) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 2)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,4,7,2,3,8] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 2) (v 3)≠v 8 ∧ A (v 2) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 2
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,4,8,2,3,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 6)) → (¬ (A (v 0) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 0)) → (¬ (A (v 1) (v 7)=v 8)) → (¬ (A (v 1) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,6,1,7,8,2,3,4] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 6 ∧ A (v 0) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 7)≠v 8 ∧ A (v 1) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 6)=v 8)) → (¬ (A (v 4) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,2,3,4,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 8 ∧ A (v 4) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 6)=v 8)) → (¬ (A (v 3) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,2,4,3,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 8 ∧ A (v 3) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,2,6,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,2,8,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 2) (v 6)=v 8)) → (¬ (A (v 2) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,3,4,2,6,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 8 ∧ A (v 2) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 2) (v 4)=v 8)) → (¬ (A (v 2) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,3,6,2,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 8 ∧ A (v 2) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 3)=v 8)) → (¬ (A (v 1) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 1)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,3,8,2,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 8 ∧ A (v 1) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 2) (v 3)=v 8)) → (¬ (A (v 2) (v 8)=v 3)) → (¬ (A (v 3) (v 8)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,4,6,2,3,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 8 ∧ A (v 2) (v 8)≠v 3 ∧ A (v 3) (v 8)≠v 2
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 7)) → (¬ (A (v 0) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 0)) → (¬ (A (v 1) (v 4)=v 8)) → (¬ (A (v 1) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,7,1,4,8,2,3,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 7 ∧ A (v 0) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 8 ∧ A (v 1) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 6)=v 7)) → (¬ (A (v 4) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,2,3,4,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 6)≠v 7 ∧ A (v 4) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 6)=v 7)) → (¬ (A (v 3) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,2,4,3,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 6)≠v 7 ∧ A (v 3) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,2,6,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩


private theorem in342_nine_chunk63 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 131,Sat.Literal.pos 138,Sat.Literal.pos 233]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 67,Sat.Literal.pos 86,Sat.Literal.pos 162,Sat.Literal.pos 117,Sat.Literal.pos 136,Sat.Literal.pos 198]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 68,Sat.Literal.pos 93,Sat.Literal.pos 169,Sat.Literal.pos 116,Sat.Literal.pos 129,Sat.Literal.pos 191]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 74,Sat.Literal.pos 87,Sat.Literal.pos 190,Sat.Literal.pos 110,Sat.Literal.pos 135,Sat.Literal.pos 170])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 75,Sat.Literal.pos 94,Sat.Literal.pos 197,Sat.Literal.pos 109,Sat.Literal.pos 128,Sat.Literal.pos 163]) (Sat.Fmla.one [Sat.Literal.pos 34,Sat.Literal.pos 53,Sat.Literal.pos 224,Sat.Literal.pos 89,Sat.Literal.pos 96,Sat.Literal.pos 232,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 188,Sat.Literal.pos 207,Sat.Literal.pos 228]) (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 160,Sat.Literal.pos 179,Sat.Literal.pos 227])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 153,Sat.Literal.pos 178,Sat.Literal.pos 206]) (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 62,Sat.Literal.pos 99,Sat.Literal.pos 141,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 40,Sat.Literal.pos 47,Sat.Literal.pos 231,Sat.Literal.pos 83,Sat.Literal.pos 102,Sat.Literal.pos 225,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 187,Sat.Literal.pos 200,Sat.Literal.pos 221])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 159,Sat.Literal.pos 172,Sat.Literal.pos 220]) (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 152,Sat.Literal.pos 171,Sat.Literal.pos 199]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 61,Sat.Literal.pos 92,Sat.Literal.pos 134,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 41,Sat.Literal.pos 54,Sat.Literal.pos 238,Sat.Literal.pos 82,Sat.Literal.pos 95,Sat.Literal.pos 218,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 57,Sat.Literal.pos 64,Sat.Literal.pos 106,Sat.Literal.pos 186,Sat.Literal.pos 193,Sat.Literal.pos 214]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 58,Sat.Literal.pos 71,Sat.Literal.pos 113,Sat.Literal.pos 158,Sat.Literal.pos 165,Sat.Literal.pos 213]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 59,Sat.Literal.pos 78,Sat.Literal.pos 120,Sat.Literal.pos 151,Sat.Literal.pos 164,Sat.Literal.pos 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 60,Sat.Literal.pos 85,Sat.Literal.pos 127,Sat.Literal.pos 150,Sat.Literal.pos 157,Sat.Literal.pos 185]) (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 65,Sat.Literal.pos 72,Sat.Literal.pos 148,Sat.Literal.pos 123,Sat.Literal.pos 130,Sat.Literal.pos 212])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.pos 48,Sat.Literal.pos 55,Sat.Literal.pos 245,Sat.Literal.pos 81,Sat.Literal.pos 88,Sat.Literal.pos 211,Sat.Literal.pos 107,Sat.Literal.pos 114,Sat.Literal.pos 149]) (Sat.Fmla.one [Sat.Literal.pos 0])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 150]) (Sat.Fmla.one [Sat.Literal.neg 157]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 185]) (Sat.Fmla.one [Sat.Literal.neg 237])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 244]) (Sat.Fmla.one [Sat.Literal.neg 251])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,2,7,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 2) (v 6)=v 7)) → (¬ (A (v 2) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,3,4,2,6,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 6)≠v 7 ∧ A (v 2) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 6)) → (¬ (A (v 1) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 1)) → (¬ (A (v 2) (v 4)=v 7)) → (¬ (A (v 2) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,3,6,2,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 6 ∧ A (v 1) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 7 ∧ A (v 2) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 7)) → (¬ (A (v 1) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 1)) → (¬ (A (v 2) (v 4)=v 6)) → (¬ (A (v 2) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,3,7,2,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 7 ∧ A (v 1) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 4)≠v 6 ∧ A (v 2) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 4)=v 6)) → (¬ (A (v 1) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 1)) → (¬ (A (v 2) (v 3)=v 7)) → (¬ (A (v 2) (v 7)=v 3)) → (¬ (A (v 3) (v 7)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,4,6,2,3,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 6 ∧ A (v 1) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 7 ∧ A (v 2) (v 7)≠v 3 ∧ A (v 3) (v 7)≠v 2
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 4)=v 7)) → (¬ (A (v 1) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 6)) → (¬ (A (v 2) (v 6)=v 3)) → (¬ (A (v 3) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,4,7,2,3,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 4)≠v 7 ∧ A (v 1) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 6 ∧ A (v 2) (v 6)≠v 3 ∧ A (v 3) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 5)=v 8)) → (¬ (A (v 0) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 0)) → (¬ (A (v 1) (v 6)=v 7)) → (¬ (A (v 1) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,5,8,1,6,7,2,3,4] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 5)≠v 8 ∧ A (v 0) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 6)≠v 7 ∧ A (v 1) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 7)) → (¬ (A (v 0) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 5)=v 8)) → (¬ (A (v 4) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,7,1,2,3,4,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 7 ∧ A (v 0) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 8 ∧ A (v 4) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 4
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 7)) → (¬ (A (v 0) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 5)=v 8)) → (¬ (A (v 3) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,7,1,2,4,3,5,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 7 ∧ A (v 0) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 8 ∧ A (v 3) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 7)) → (¬ (A (v 0) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 4)=v 8)) → (¬ (A (v 3) (v 8)=v 4)) → (¬ (A (v 4) (v 8)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,7,1,2,5,3,4,8] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 7 ∧ A (v 0) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 8 ∧ A (v 3) (v 8)≠v 4 ∧ A (v 4) (v 8)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 7)) → (¬ (A (v 0) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 0)) → (¬ (A (v 1) (v 2)=v 8)) → (¬ (A (v 1) (v 8)=v 2)) → (¬ (A (v 2) (v 8)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,7,1,2,8,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 7 ∧ A (v 0) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 8 ∧ A (v 1) (v 8)≠v 2 ∧ A (v 2) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 7)) → (¬ (A (v 0) (v 7)=v 6)) → (¬ (A (v 6) (v 7)=v 0)) → (¬ (A (v 1) (v 5)=v 8)) → (¬ (A (v 1) (v 8)=v 5)) → (¬ (A (v 5) (v 8)=v 1)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,7,1,5,8,2,3,4] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 7 ∧ A (v 0) (v 7)≠v 6 ∧ A (v 6) (v 7)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 8 ∧ A (v 1) (v 8)≠v 5 ∧ A (v 5) (v 8)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 8)) → (¬ (A (v 0) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 5)=v 7)) → (¬ (A (v 4) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,8,1,2,3,4,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 8 ∧ A (v 0) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 7 ∧ A (v 4) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 4
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 8)) → (¬ (A (v 0) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 5)=v 7)) → (¬ (A (v 3) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,8,1,2,4,3,5,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 8 ∧ A (v 0) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 7 ∧ A (v 3) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 8)) → (¬ (A (v 0) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 4)=v 7)) → (¬ (A (v 3) (v 7)=v 4)) → (¬ (A (v 4) (v 7)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,8,1,2,5,3,4,7] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 8 ∧ A (v 0) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 7 ∧ A (v 3) (v 7)≠v 4 ∧ A (v 4) (v 7)≠v 3
              exact ⟨h6,h7,h8⟩
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (¬ (A (v 0) (v 6)=v 8)) → (¬ (A (v 0) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 7)) → (¬ (A (v 1) (v 7)=v 2)) → (¬ (A (v 2) (v 7)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
          intro h0 h1 h2 h3 h4 h5 h6 h7 h8
          apply hno
          let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,8,1,2,7,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
          refine ⟨σ,?_⟩
          intro t
          fin_cases t
          · change A (v 0) (v 6)≠v 8 ∧ A (v 0) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 0
            exact ⟨h0,h1,h2⟩
          · change A (v 1) (v 2)≠v 7 ∧ A (v 1) (v 7)≠v 2 ∧ A (v 2) (v 7)≠v 1
            exact ⟨h3,h4,h5⟩
          · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
            exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 6)=v 8)) → (¬ (A (v 0) (v 8)=v 6)) → (¬ (A (v 6) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 7)) → (¬ (A (v 1) (v 7)=v 5)) → (¬ (A (v 5) (v 7)=v 1)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,6,8,1,5,7,2,3,4] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 6)≠v 8 ∧ A (v 0) (v 8)≠v 6 ∧ A (v 6) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 7 ∧ A (v 1) (v 7)≠v 5 ∧ A (v 5) (v 7)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 3)) → (¬ (A (v 1) (v 3)=v 2)) → (¬ (A (v 2) (v 3)=v 1)) → (¬ (A (v 4) (v 5)=v 6)) → (¬ (A (v 4) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 4)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,2,3,4,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 3 ∧ A (v 1) (v 3)≠v 2 ∧ A (v 2) (v 3)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 4) (v 5)≠v 6 ∧ A (v 4) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 4
              exact ⟨h6,h7,h8⟩
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 4)) → (¬ (A (v 1) (v 4)=v 2)) → (¬ (A (v 2) (v 4)=v 1)) → (¬ (A (v 3) (v 5)=v 6)) → (¬ (A (v 3) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,2,4,3,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 4 ∧ A (v 1) (v 4)≠v 2 ∧ A (v 2) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 5)≠v 6 ∧ A (v 3) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 5)) → (¬ (A (v 1) (v 5)=v 2)) → (¬ (A (v 2) (v 5)=v 1)) → (¬ (A (v 3) (v 4)=v 6)) → (¬ (A (v 3) (v 6)=v 4)) → (¬ (A (v 4) (v 6)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,2,5,3,4,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 5 ∧ A (v 1) (v 5)≠v 2 ∧ A (v 2) (v 5)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 6 ∧ A (v 3) (v 6)≠v 4 ∧ A (v 4) (v 6)≠v 3
              exact ⟨h6,h7,h8⟩
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 2)=v 6)) → (¬ (A (v 1) (v 6)=v 2)) → (¬ (A (v 2) (v 6)=v 1)) → (¬ (A (v 3) (v 4)=v 5)) → (¬ (A (v 3) (v 5)=v 4)) → (¬ (A (v 4) (v 5)=v 3)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,2,6,3,4,5] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 2)≠v 6 ∧ A (v 1) (v 6)≠v 2 ∧ A (v 2) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 3) (v 4)≠v 5 ∧ A (v 3) (v 5)≠v 4 ∧ A (v 4) (v 5)≠v 3
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 3)=v 4)) → (¬ (A (v 1) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 1)) → (¬ (A (v 2) (v 5)=v 6)) → (¬ (A (v 2) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,3,4,2,5,6] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 3)≠v 4 ∧ A (v 1) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 5)≠v 6 ∧ A (v 2) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 2
              exact ⟨h6,h7,h8⟩
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 7)=v 8)) → (¬ (A (v 0) (v 8)=v 7)) → (¬ (A (v 7) (v 8)=v 0)) → (¬ (A (v 1) (v 5)=v 6)) → (¬ (A (v 1) (v 6)=v 5)) → (¬ (A (v 5) (v 6)=v 1)) → (¬ (A (v 2) (v 3)=v 4)) → (¬ (A (v 2) (v 4)=v 3)) → (¬ (A (v 3) (v 4)=v 2)) → False
            intro h0 h1 h2 h3 h4 h5 h6 h7 h8
            apply hno
            let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective (![0,7,8,1,5,6,2,3,4] : Fin 9 → Fin 9) (by decide +kernel)
            refine ⟨σ,?_⟩
            intro t
            fin_cases t
            · change A (v 0) (v 7)≠v 8 ∧ A (v 0) (v 8)≠v 7 ∧ A (v 7) (v 8)≠v 0
              exact ⟨h0,h1,h2⟩
            · change A (v 1) (v 5)≠v 6 ∧ A (v 1) (v 6)≠v 5 ∧ A (v 5) (v 6)≠v 1
              exact ⟨h3,h4,h5⟩
            · change A (v 2) (v 3)≠v 4 ∧ A (v 2) (v 4)≠v 3 ∧ A (v 3) (v 4)≠v 2
              exact ⟨h6,h7,h8⟩
          ·
            apply in342_nine_sat_one
            change (¬ (A (v 0) (v 1)=v 2)) → False
            intro h
            exact h hbad
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 5) → False
            intro h
            exact hT1.1 h
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 4) → False
            intro h
            exact hT1.2.1 h
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 3) → False
            intro h
            exact hT1.2.2 h
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 7)=v 8) → False
            intro h
            exact hT2.1 h
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 6) (v 8)=v 7) → False
            intro h
            exact hT2.2.1 h
          ·
            apply in342_nine_sat_one
            change (A (v 7) (v 8)=v 6) → False
            intro h
            exact hT2.2.2 h

theorem wild_valid_triples_nine_encoding_part_d {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla in342_nine_formula_d := by
  exact (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk48 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk49 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk50 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk51 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk52 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk53 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk54 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk55 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk56 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk57 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk58 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk59 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk60 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk61 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk62 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk63 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))))
