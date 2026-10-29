import AFTD.Prelude
import AFTD.Kb.Tcs.WildValidTriplesNineSatCore

/-!
# wild_valid_triples_nine_encoding_part_a

Topic: graphs   Node: d8eb7c42e8bc

Provenance: helper lemma. IN-342 supporting steps for OP-306, arXiv:2610.22142 Sections3.3.2/6. The target remains prescribed-coloring sharpness; these are local validity and conditioning-family helpers, not a seal-free partition theorem or new wild-number bound. No research advance is claimed. The former combined helper timed out in the180-second interactive gate. This is the SAME checked certificate and mathematical interpretation, split into a core and four soundness modules; no gate budget, axiom or mathematical statement is weakened.

Under the generic normalized-array assumptions and the assumption of no valid nine-vertex rearrangement, the induced equality valuation satisfies this explicit part of the fixed CNF. Every clause is proved from the array assumptions or an explicitly bijective candidate partition. This is an interpretation helper, not a standalone graph result.
-/

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
def in342_nine_formula_a : Sat.Fmla := (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 1]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 2]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 3]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 4]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 5])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 6]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 9])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 10]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 12]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 10])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 12]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 13]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 12]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 12])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 13])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 16]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 17])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 19]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 17])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 19])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 20]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 19]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 19])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 20])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 23]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 24])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 26]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 24])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 26]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 27]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 26]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 26])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 27])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 30]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 31])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 33]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 31])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 33]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 34]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 33]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 34])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 37]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 38]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 39]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 41])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 38]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 39]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 40]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 39]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 41])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 41])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 46]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 46])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 47]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 46]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 48])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 51])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 53]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 54]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 55])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 58])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 59]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 60]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 62])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 59]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 60])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 61]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 62]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 60]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 62])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 62])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 62]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 65]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 66]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 68])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 66]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 67]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 68]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 69]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 68])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 68])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 69])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 72]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 73]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 73])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 74]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 75]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 76]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 75])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 76])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 79]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 80]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 80]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 81]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 83]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 82])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 83])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 86]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 87]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 87]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 88]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 90]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 89])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 90])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 93]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 94]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 97]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 96]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 96]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 101]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 103])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 101])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 103]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 103])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 103])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 104]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 106]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 108])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 110])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 107])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 109]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 110]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 111])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 113])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 117])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 114]))))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 115]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 117]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 115])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 117])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 116]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 118]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 118])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 120]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 121]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 122]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 123]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 122])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 124])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 124])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 125]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 125]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 128])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 132])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 129])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 131]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 129])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 132]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 130]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 134])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 135])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 136]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 137]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 136]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 138])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 137])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 141])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 143]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 144]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 143])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 143])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 145]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 145])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 148])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 149]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 152]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 149])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 152])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 151])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 153])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 155]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 156]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 159]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 156])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 159])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 158])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 160]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 163])))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 166])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 166])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 169]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 170]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 172]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 171])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 173]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 172])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 174])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 173]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 176]) (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 178]) (Sat.Fmla.one [Sat.Literal.neg 176,Sat.Literal.neg 178])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 176,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 181]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 181]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 184])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 186]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 188])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 188]))))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 188]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 193]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 194])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 195]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 197]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 200]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 201])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 200]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 205])))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 206]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 208])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 207])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 209]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 208]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 208,Sat.Literal.neg 209]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 212])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 213]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 214])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 216])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 213]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 213]))))))))))
private theorem in342_nine_chunk0 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 1]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 2]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 3]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 4]) (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 5])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 0,Sat.Literal.neg 6]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 9])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 10]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 12]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 8,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 10])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 12]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 9,Sat.Literal.neg 13]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 11]) (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 12]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 10,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 12])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 11,Sat.Literal.neg 13]) (Sat.Fmla.one [Sat.Literal.neg 12,Sat.Literal.neg 13])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 16]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 17])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 19]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 14,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 17])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 19])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 3) → False
          intro h1 h2
          exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 1)=v 2) → (A (v 0) (v 1)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 2)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 3) → (A (v 0) (v 2)=v 5) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 3) → (A (v 0) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 2)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 4) → (A (v 0) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 2)=v 4) → (A (v 0) (v 2)=v 8) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 5) → (A (v 0) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 6) → (A (v 0) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 2)=v 7) → (A (v 0) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 3)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 1) → (A (v 0) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 4) → (A (v 0) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk1 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 16,Sat.Literal.neg 20]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 18]) (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 19]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 17,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 19])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 18,Sat.Literal.neg 20]) (Sat.Fmla.one [Sat.Literal.neg 19,Sat.Literal.neg 20])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 23]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 24])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 26]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 21,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 24])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 26]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 23,Sat.Literal.neg 27]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 25]) (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 26]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 24,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 26])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 25,Sat.Literal.neg 27]) (Sat.Fmla.one [Sat.Literal.neg 26,Sat.Literal.neg 27])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 30]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 31])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 33]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 28,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 31])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 33])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 3)=v 4) → (A (v 0) (v 3)=v 8) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 5) → (A (v 0) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 6) → (A (v 0) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 3)=v 7) → (A (v 0) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 4)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 1) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 3) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 4)=v 3) → (A (v 0) (v 4)=v 8) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 0) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 5) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 0) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 6) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 4)=v 7) → (A (v 0) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 5)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 1) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 0) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 0) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 3) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk2 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 30,Sat.Literal.neg 34]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 32]) (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 33]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 31,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 33])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 32,Sat.Literal.neg 34]) (Sat.Fmla.one [Sat.Literal.neg 33,Sat.Literal.neg 34])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 37]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 38]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 39]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 35,Sat.Literal.neg 41])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 38]) (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 39]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 40]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 37,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 39]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 38,Sat.Literal.neg 41])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 40]) (Sat.Fmla.one [Sat.Literal.neg 39,Sat.Literal.neg 41])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 40,Sat.Literal.neg 41]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 44])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 46]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 42,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 45]) (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 46])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 5)=v 3) → (A (v 0) (v 5)=v 8) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 0) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 4) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 0) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 6) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 5)=v 7) → (A (v 0) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 6)=v 1) → (A (v 0) (v 6)=v 3) → False
          intro h1 h2
          exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 1) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 0) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 0) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 6)=v 3) → (A (v 0) (v 6)=v 7) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 3) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 0) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 4) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 0) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 5) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 6)=v 7) → (A (v 0) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 1) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 0) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk3 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 47]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 44,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 46]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 45,Sat.Literal.neg 48])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 47]) (Sat.Fmla.one [Sat.Literal.neg 46,Sat.Literal.neg 48])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 47,Sat.Literal.neg 48]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 51])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 49,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 52]) (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 53]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 54]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 51,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 53]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 52,Sat.Literal.neg 55])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 54]) (Sat.Fmla.one [Sat.Literal.neg 53,Sat.Literal.neg 55])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 54,Sat.Literal.neg 55]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 58])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 59]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 60]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 57,Sat.Literal.neg 62])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 59]) (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 60])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 7)=v 3) → (A (v 0) (v 7)=v 6) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 3) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 0) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 4) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 0) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 5) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 7)=v 6) → (A (v 0) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 0) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 1) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 3) → (A (v 0) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 3) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 0) (v 8)=v 3) → (A (v 0) (v 8)=v 6) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 3) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 0) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 4) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 0) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 5) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 0) (v 8)=v 6) → (A (v 0) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 2)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 2)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 3) → (A (v 1) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 2)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk4 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 61]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 58,Sat.Literal.neg 62]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 60]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 59,Sat.Literal.neg 62])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 61]) (Sat.Fmla.one [Sat.Literal.neg 60,Sat.Literal.neg 62])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 61,Sat.Literal.neg 62]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 65]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 66]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 68])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 63,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 66]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 67]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 68]) (Sat.Fmla.one [Sat.Literal.neg 65,Sat.Literal.neg 69]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 67]) (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 68])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 66,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 68])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 67,Sat.Literal.neg 69]) (Sat.Fmla.one [Sat.Literal.neg 68,Sat.Literal.neg 69])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 72]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 73]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 70,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 73])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 4) → (A (v 1) (v 2)=v 7) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 4) → (A (v 1) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 2)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 5) → (A (v 1) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 2)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 2)=v 6) → (A (v 1) (v 2)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 2)=v 7) → (A (v 1) (v 2)=v 8) → False
          intro h1 h2
          exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 3)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 0) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 3)=v 4) → (A (v 1) (v 3)=v 6) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 4) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 5) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 3)=v 7) → False
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
            change (A (v 1) (v 3)=v 6) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 3)=v 7) → (A (v 1) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 4)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 0) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk5 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 74]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 75]) (Sat.Fmla.one [Sat.Literal.neg 72,Sat.Literal.neg 76]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 74]) (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 75])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 73,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 75])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 74,Sat.Literal.neg 76]) (Sat.Fmla.one [Sat.Literal.neg 75,Sat.Literal.neg 76])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 79]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 80]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 77,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 80]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 81]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 82]) (Sat.Fmla.one [Sat.Literal.neg 79,Sat.Literal.neg 83]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 81]) (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 82])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 80,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 82])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 81,Sat.Literal.neg 83]) (Sat.Fmla.one [Sat.Literal.neg 82,Sat.Literal.neg 83])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 86]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 87]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 84,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 87])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 4)=v 3) → (A (v 1) (v 4)=v 6) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 3) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 5) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 6) → (A (v 1) (v 4)=v 7) → False
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
            change (A (v 1) (v 4)=v 6) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 4)=v 7) → (A (v 1) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 5)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 0) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 1) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 5)=v 3) → (A (v 1) (v 5)=v 6) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 3) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 1) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 1) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 4) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 6) → (A (v 1) (v 5)=v 7) → False
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
            change (A (v 1) (v 5)=v 6) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 5)=v 7) → (A (v 1) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 0) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 1) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk6 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 88]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 89]) (Sat.Fmla.one [Sat.Literal.neg 86,Sat.Literal.neg 90]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 88]) (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 89])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 87,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 89])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 88,Sat.Literal.neg 90]) (Sat.Fmla.one [Sat.Literal.neg 89,Sat.Literal.neg 90])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 93]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 94]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 91,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 96]) (Sat.Fmla.one [Sat.Literal.neg 93,Sat.Literal.neg 97]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 96]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 94,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 96]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 95,Sat.Literal.neg 97]) (Sat.Fmla.one [Sat.Literal.neg 96,Sat.Literal.neg 97])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 101]) (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 103])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 98,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 101])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 102]) (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 103]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 100,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 103])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 101,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 103])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 6)=v 3) → (A (v 1) (v 6)=v 5) → False
          intro h1 h2
          exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 3) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 1) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 4) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 1) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 5) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 6)=v 7) → (A (v 1) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 1) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 1) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 0) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 3) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 7)=v 4) → (A (v 1) (v 7)=v 6) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 4) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 5) → (A (v 1) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 5) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 7)=v 6) → (A (v 1) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 1) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 0) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 3) → (A (v 1) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 3) → (A (v 1) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 3) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 3) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 4) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 5) → (A (v 1) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk7 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 102,Sat.Literal.neg 104]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 103,Sat.Literal.neg 104]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 106]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 107]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 108])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 109]) (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 110])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 105,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 107])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 106,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 108]) (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 109]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 110]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 107,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 109]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 108,Sat.Literal.neg 111])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 110]) (Sat.Fmla.one [Sat.Literal.neg 109,Sat.Literal.neg 111])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 110,Sat.Literal.neg 111]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 113])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 114]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 115]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 117])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 112,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 114])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 1) (v 8)=v 5) → (A (v 1) (v 8)=v 7) → False
          intro h1 h2
          exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 1) (v 8)=v 6) → (A (v 1) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 0) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 3)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 1) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 3)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 3)=v 4) → (A (v 2) (v 3)=v 7) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 4) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 3)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 5) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 2) (v 3)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 6) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 3)=v 7) → (A (v 2) (v 3)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 0) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 4)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk8 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 115]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 117]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 113,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 115])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 116]) (Sat.Fmla.one [Sat.Literal.neg 114,Sat.Literal.neg 117])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 116]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 115,Sat.Literal.neg 118]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 117]) (Sat.Fmla.one [Sat.Literal.neg 116,Sat.Literal.neg 118])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 117,Sat.Literal.neg 118]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 120]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 121]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 122]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 123]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 119,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 121]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 122])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 124])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 120,Sat.Literal.neg 125]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 122]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 121,Sat.Literal.neg 125])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 123]) (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 124])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 4)=v 1) → (A (v 2) (v 4)=v 5) → False
          intro h1 h2
          exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 1) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 4)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 3) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 4)=v 5) → (A (v 2) (v 4)=v 6) → False
          intro h1 h2
          exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 5) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 2) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 6) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 4)=v 7) → (A (v 2) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 1) → False
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
          change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 3) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 0) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 5)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 5)=v 4) → False
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
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 1) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 5)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 3) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 2) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 4) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk9 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 122,Sat.Literal.neg 125]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 123,Sat.Literal.neg 124]) (Sat.Fmla.one [Sat.Literal.neg 124,Sat.Literal.neg 125]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 127]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 128])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 126,Sat.Literal.neg 132])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 128]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 129])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 131]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 127,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 129])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 130]) (Sat.Fmla.one [Sat.Literal.neg 128,Sat.Literal.neg 132]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 130]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 129,Sat.Literal.neg 132]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 131]) (Sat.Fmla.one [Sat.Literal.neg 130,Sat.Literal.neg 132])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 131,Sat.Literal.neg 132]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 134])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 135]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 136])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 133,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 135])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 136]) (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 137])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 5)=v 4) → (A (v 2) (v 5)=v 8) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 6) → (A (v 2) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 5)=v 7) → (A (v 2) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 6)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 0) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 1) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 2) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 2) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 3) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 6)=v 4) → (A (v 2) (v 6)=v 5) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 4) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 4) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 5) → (A (v 2) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 5) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 6)=v 7) → (A (v 2) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 1) → False
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
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 0) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 2) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk10 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 134,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 136]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 137]) (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 138])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 135,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 137])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 138]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 136,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 137,Sat.Literal.neg 138]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 138,Sat.Literal.neg 139]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 141])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 143]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 144]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 145]) (Sat.Fmla.one [Sat.Literal.neg 140,Sat.Literal.neg 146]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 142]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 143])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 145])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 141,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 143])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 142,Sat.Literal.neg 145]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 144]) (Sat.Fmla.one [Sat.Literal.neg 143,Sat.Literal.neg 145])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 145,Sat.Literal.neg 146]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 148])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 7)=v 1) → (A (v 2) (v 7)=v 6) → False
          intro h1 h2
          exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 1) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 2) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 3) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 4) → (A (v 2) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 7)=v 4) → (A (v 2) (v 7)=v 6) → False
          intro h1 h2
          exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 4) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 5) → (A (v 2) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 7)=v 6) → (A (v 2) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 5) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 0) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 2) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 1) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 2) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 3) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 4) → (A (v 2) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 4) → (A (v 2) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 2) (v 8)=v 6) → (A (v 2) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 4)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk11 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 149]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 152]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 147,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 149])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 151]) (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 152])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 148,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 151])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 149,Sat.Literal.neg 153]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 152]) (Sat.Fmla.one [Sat.Literal.neg 151,Sat.Literal.neg 153])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 152,Sat.Literal.neg 153]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 155]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 156]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 159]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 154,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 156])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 158]) (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 159])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 155,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 158])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 156,Sat.Literal.neg 160]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 159]) (Sat.Fmla.one [Sat.Literal.neg 158,Sat.Literal.neg 160])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 159,Sat.Literal.neg 160]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 163])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 4)=v 0) → (A (v 3) (v 4)=v 2) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 0) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 4)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 1) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 4)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 2) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 3) (v 4)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 6) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 4)=v 7) → (A (v 3) (v 4)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 5)=v 1) → False
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
          change (A (v 3) (v 5)=v 0) → (A (v 3) (v 5)=v 2) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 0) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 3) (v 5)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 1) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 3) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 2) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 3) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 6) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 5)=v 7) → (A (v 3) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 6)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk12 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 161,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 164])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 162,Sat.Literal.neg 166])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 163,Sat.Literal.neg 164]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 165]) (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 166]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 164,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 166])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 165,Sat.Literal.neg 167]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 169]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 170]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 172]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 168,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 170]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 171])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 169,Sat.Literal.neg 174])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 171]) (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 173]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 170,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 172])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 173]) (Sat.Fmla.one [Sat.Literal.neg 171,Sat.Literal.neg 174])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 6)=v 0) → (A (v 3) (v 6)=v 4) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 0) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 3) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 1) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 6)=v 2) → (A (v 3) (v 6)=v 4) → False
          intro h1 h2
          exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 3) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 4) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 3) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 6)=v 5) → (A (v 3) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 1) → False
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
          change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 2) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 0) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 1) → (A (v 3) (v 7)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 1) → (A (v 3) (v 7)=v 4) → False
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
            change (A (v 3) (v 7)=v 1) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 1) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 3) (v 7)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 2) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 3) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 3) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 4) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠8) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk13 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 173]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 172,Sat.Literal.neg 174]) (Sat.Fmla.one [Sat.Literal.neg 173,Sat.Literal.neg 174]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 176]) (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 177])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 175,Sat.Literal.neg 178]) (Sat.Fmla.one [Sat.Literal.neg 176,Sat.Literal.neg 178])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 176,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 178])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 177,Sat.Literal.neg 181]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 179]) (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 180])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 178,Sat.Literal.neg 181]) (Sat.Fmla.one [Sat.Literal.neg 179,Sat.Literal.neg 181]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 180,Sat.Literal.neg 181]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 183]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 184]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 182,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 184])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 186]) (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 187])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 183,Sat.Literal.neg 188]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 186]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 184,Sat.Literal.neg 188])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 187]) (Sat.Fmla.one [Sat.Literal.neg 186,Sat.Literal.neg 188])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 7)=v 5) → (A (v 3) (v 7)=v 6) → False
          intro h1 h2
          exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 5) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 7)=v 6) → (A (v 3) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 3) (v 8)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 3) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 0) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 1) → (A (v 3) (v 8)=v 4) → False
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
            change (A (v 3) (v 8)=v 1) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 2) → (A (v 3) (v 8)=v 4) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠4) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 2) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 2) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 3) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 3) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 4) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (4:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 3) (v 8)=v 5) → (A (v 3) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 3) (v 8)=v 6) → (A (v 3) (v 8)=v 7) → False
          intro h1 h2
          exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 5)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 5)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 0) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 5)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 1) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 5)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 2) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 6) → (A (v 4) (v 5)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 5)=v 6) → (A (v 4) (v 5)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk14 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 187,Sat.Literal.neg 188]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 192]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 193]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 189,Sat.Literal.neg 195])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 191]) (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 192])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 190,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 192])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 194]) (Sat.Fmla.one [Sat.Literal.neg 191,Sat.Literal.neg 195]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 193]) (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 194])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 192,Sat.Literal.neg 195]) (Sat.Fmla.one [Sat.Literal.neg 193,Sat.Literal.neg 195]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 197]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 200]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 196,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 200]) (Sat.Fmla.one [Sat.Literal.neg 197,Sat.Literal.neg 201])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 199]) (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 200])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 198,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 200]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 201]) (Sat.Fmla.one [Sat.Literal.neg 199,Sat.Literal.neg 202])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 201,Sat.Literal.neg 202]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 205])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 5)=v 7) → (A (v 4) (v 5)=v 8) → False
          intro h1 h2
          exact (by decide : (7:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 0) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 1) → (A (v 4) (v 6)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 1) → (A (v 4) (v 6)=v 3) → False
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
            change (A (v 4) (v 6)=v 1) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 4) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 2) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 4) (v 6)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 4) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 3) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 6)=v 5) → (A (v 4) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠8) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 7)=v 0) → (A (v 4) (v 7)=v 1) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 0) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 1) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 1) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 4) (v 7)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 2) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 4) (v 7)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 4) (v 7)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 3) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 7)=v 6) → (A (v 4) (v 7)=v 8) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))


private theorem in342_nine_chunk15 {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 206]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 203,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 205])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 206]) (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 208])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 204,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 206])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 207]) (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 208]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 205,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 207])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 208]) (Sat.Fmla.one [Sat.Literal.neg 206,Sat.Literal.neg 209]))))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 208]) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 207,Sat.Literal.neg 209]) (Sat.Fmla.one [Sat.Literal.neg 208,Sat.Literal.neg 209]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 211]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 212])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 213]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 214])))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 215]) (Sat.Fmla.one [Sat.Literal.neg 210,Sat.Literal.neg 216])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 212]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 213]))) (Sat.Fmla.and (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 214]) (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 215])) (Sat.Fmla.and (Sat.Fmla.one [Sat.Literal.neg 211,Sat.Literal.neg 216]) (Sat.Fmla.one [Sat.Literal.neg 212,Sat.Literal.neg 213])))))) := by
  apply in342_nine_sat_and
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 8)=v 0) → (A (v 4) (v 8)=v 3) → False
          intro h1 h2
          exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 0) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 1) → (A (v 4) (v 8)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 1) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 1) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠6) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 1) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 4) (v 8)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠5) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠6) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 2) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 4) (v 8)=v 5) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠5) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 4) (v 8)=v 6) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠6) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 3) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (3:Fin 9)≠7) (hv (h1.symm.trans h2))
  ·
    apply in342_nine_sat_and
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_one
          change (A (v 4) (v 8)=v 5) → (A (v 4) (v 8)=v 6) → False
          intro h1 h2
          exact (by decide : (5:Fin 9)≠6) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 5) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (5:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 4) (v 8)=v 6) → (A (v 4) (v 8)=v 7) → False
            intro h1 h2
            exact (by decide : (6:Fin 9)≠7) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 1) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠1) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠2) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠3) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠4) (hv (h1.symm.trans h2))
    ·
      apply in342_nine_sat_and
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠7) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 0) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (0:Fin 9)≠8) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 6)=v 2) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠2) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠3) (hv (h1.symm.trans h2))
      ·
        apply in342_nine_sat_and
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 6)=v 4) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠4) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 6)=v 7) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠7) (hv (h1.symm.trans h2))
        ·
          apply in342_nine_sat_and
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 1) → (A (v 5) (v 6)=v 8) → False
            intro h1 h2
            exact (by decide : (1:Fin 9)≠8) (hv (h1.symm.trans h2))
          ·
            apply in342_nine_sat_one
            change (A (v 5) (v 6)=v 2) → (A (v 5) (v 6)=v 3) → False
            intro h1 h2
            exact (by decide : (2:Fin 9)≠3) (hv (h1.symm.trans h2))

theorem wild_valid_triples_nine_encoding_part_a {C : Type*} (A : C → C → C)
    (hdiag : ∀ u,A u u=u) (hsym : ∀ u w,A u w=A w u)
    (hinj : ∀ u,Function.Injective (A u))
    (v : Fin 9 → C) (hv : Function.Injective v)
    (hbad : A (v 0) (v 1)=v 2)
    (hT1 : in342_nine_valid A (v 3) (v 4) (v 5))
    (hT2 : in342_nine_valid A (v 6) (v 7) (v 8))
    (hno : ¬ in342_nine_goal A v) :
    (in342_nine_val A v).satisfies_fmla in342_nine_formula_a := by
  exact (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk0 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk1 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk2 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk3 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk4 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk5 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk6 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk7 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk8 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk9 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk10 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk11 A hdiag hsym hinj v hv hbad hT1 hT2 hno))) (in342_nine_sat_and (in342_nine_sat_and (in342_nine_chunk12 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk13 A hdiag hsym hinj v hv hbad hT1 hT2 hno)) (in342_nine_sat_and (in342_nine_chunk14 A hdiag hsym hinj v hv hbad hT1 hT2 hno) (in342_nine_chunk15 A hdiag hsym hinj v hv hbad hT1 hT2 hno)))))
