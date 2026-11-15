import AFTD.Prelude

/-!
# good_slopes_prime11_three_anchor

Topic: elementary_number_theory   Node: 227141e21b05

Provenance: helper lemma. The three-anchor 11-point special case of arXiv:2611.04551 Lemma 2.7, with certificate from experiment 27617.

A finite set of points over the field of eleven elements cannot contain the three noncollinear points (0,0), (1,0), (0,1), while at least six nonzero direction forms are both injective and surjective on the set. The six-direction hypothesis is expressed by requiring every five of the ten nonzero directions to contain a marked direction.
-/

set_option Elab.async false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000
open Lean Elab Command in
elab "aftd_n11_lrat_core " cnf:term:max ppSpace lrat:term:max : command => do
  Command.liftTermElabM do
    let cnf ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat `aftd_n11_lrat
    addDecl <| Declaration.defnDecl {
      name := `aftd_n11_formula, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := `aftd_n11_sat_proof, levelParams := [], type := ← Meta.inferType proof, value := proof }
aftd_n11_lrat_core "p cnf 131 365\n1 0\n12 0\n2 0\n122 123 124 125 126 0\n122 123 124 125 127 0\n122 123 124 125 128 0\n122 123 124 125 130 0\n122 123 124 125 131 0\n122 123 124 126 130 0\n122 123 124 126 131 0\n122 123 124 127 128 0\n122 123 124 127 130 0\n122 123 124 127 131 0\n122 123 124 128 129 0\n122 123 124 128 130 0\n122 123 124 128 131 0\n122 123 124 129 130 0\n122 123 124 129 131 0\n122 123 124 130 131 0\n122 123 125 126 127 0\n122 123 125 126 128 0\n122 123 125 126 129 0\n122 123 125 126 130 0\n122 123 125 126 131 0\n122 123 125 127 129 0\n122 123 125 127 130 0\n122 123 125 127 131 0\n122 123 125 128 130 0\n122 123 125 129 130 0\n122 123 125 129 131 0\n122 123 125 130 131 0\n122 123 126 127 128 0\n122 123 126 127 129 0\n122 123 126 127 130 0\n122 123 126 127 131 0\n122 123 126 128 129 0\n122 123 126 128 130 0\n122 123 126 128 131 0\n122 123 126 129 130 0\n122 123 126 129 131 0\n122 123 126 130 131 0\n122 123 127 128 129 0\n122 123 127 128 130 0\n122 123 127 128 131 0\n122 123 127 129 130 0\n122 123 127 129 131 0\n122 123 128 129 130 0\n122 123 128 129 131 0\n122 123 128 130 131 0\n122 123 129 130 131 0\n122 124 125 126 127 0\n122 124 125 126 128 0\n122 124 125 126 129 0\n122 124 125 126 130 0\n122 124 125 126 131 0\n122 124 125 127 130 0\n122 124 125 127 131 0\n122 124 125 128 129 0\n122 124 125 128 130 0\n122 124 125 128 131 0\n122 124 125 129 130 0\n122 124 125 129 131 0\n122 124 125 130 131 0\n122 124 126 127 128 0\n122 124 126 127 130 0\n122 124 126 127 131 0\n122 124 126 128 129 0\n122 124 126 128 131 0\n122 124 126 129 130 0\n122 124 126 130 131 0\n122 124 127 128 129 0\n122 124 127 128 130 0\n122 124 127 128 131 0\n122 124 127 129 130 0\n122 124 127 129 131 0\n122 124 127 130 131 0\n122 124 128 129 130 0\n122 124 128 129 131 0\n122 124 128 130 131 0\n122 124 129 130 131 0\n122 125 126 127 128 0\n122 125 126 127 129 0\n122 125 126 127 130 0\n122 125 126 127 131 0\n122 125 126 128 129 0\n122 125 126 128 130 0\n122 125 126 128 131 0\n122 125 126 129 131 0\n122 125 126 130 131 0\n122 125 127 128 129 0\n122 125 127 128 130 0\n122 125 127 128 131 0\n122 125 127 129 130 0\n122 125 127 129 131 0\n122 125 128 129 130 0\n122 125 128 129 131 0\n122 125 128 130 131 0\n122 125 129 130 131 0\n122 126 127 128 129 0\n122 126 127 128 130 0\n122 126 127 128 131 0\n122 126 127 129 131 0\n122 126 127 130 131 0\n122 126 128 129 130 0\n122 126 128 129 131 0\n122 126 128 130 131 0\n122 126 129 130 131 0\n122 127 128 129 130 0\n122 127 128 129 131 0\n122 127 129 130 131 0\n122 128 129 130 131 0\n-122 -2 -12 0\n-123 -1 -21 0\n-123 -1 -30 0\n-123 -1 -57 0\n-123 -1 -86 0\n-123 -1 -95 0\n-123 -1 -113 0\n-123 -2 -22 0\n-123 -2 -40 0\n-123 -2 -58 0\n-123 -2 -67 0\n-123 -2 -105 0\n-123 -2 -114 0\n-123 -3 -12 0\n-123 -12 -41 0\n-123 -12 -59 0\n-123 -12 -88 0\n-123 -12 -97 0\n-123 -12 -106 0\n-123 6 15 24 44 53 62 71 80 89 109 118 0\n-123 7 16 25 34 54 63 72 81 90 110 119 0\n-123 9 18 27 36 45 65 74 83 92 101 121 0\n-123 10 19 28 37 46 66 75 84 93 102 111 0\n-124 -1 -28 0\n-124 -1 -36 0\n-124 -1 -55 0\n-124 -1 -63 0\n-124 -1 -71 0\n-124 -1 -79 0\n-124 -1 -98 0\n-124 -1 -106 0\n-124 -1 -114 0\n-124 -2 -21 0\n-124 -2 -45 0\n-124 -2 -64 0\n-124 -2 -72 0\n-124 -2 -80 0\n-124 -2 -99 0\n-124 -2 -107 0\n-124 -4 -12 0\n-124 -12 -31 0\n-124 -12 -39 0\n-124 -12 -74 0\n-124 -12 -82 0\n-124 -12 -90 0\n-124 -12 -109 0\n-124 6 14 33 41 49 57 76 84 92 100 119 0\n-124 7 15 23 42 50 58 77 85 93 101 120 0\n-124 8 16 24 43 51 59 67 86 94 102 121 0\n-124 -16 -43 0\n-124 -10 -112 0\n-124 -18 -112 0\n-124 -11 -113 0\n-125 -1 -19 0\n-125 -1 -26 0\n-125 -1 -44 0\n-125 -1 -58 0\n-125 -1 -76 0\n-125 -1 -83 0\n-125 -1 -90 0\n-125 -1 -108 0\n-125 -2 -20 0\n-125 -2 -27 0\n-125 -2 -34 0\n-125 -2 -52 0\n-125 -2 -59 0\n-125 -2 -77 0\n-125 -2 -84 0\n-125 -2 -116 0\n-125 -5 -12 0\n-125 -12 -30 0\n-125 -12 -37 0\n-125 -12 -62 0\n-125 -12 -94 0\n-125 -12 -101 0\n-125 -12 -119 0\n-125 6 13 31 38 45 63 70 88 95 102 120 0\n-125 -45 -63 0\n-125 -8 -65 0\n-125 10 17 24 42 49 56 74 81 99 106 113 0\n-125 11 18 25 43 50 57 75 82 89 107 114 0\n-126 -1 -18 0\n-126 -1 -24 0\n-126 -1 -41 0\n-126 -1 -47 0\n-126 -1 -87 0\n-126 -1 -93 0\n-126 -1 -110 0\n-126 -1 -116 0\n-126 -2 -19 0\n-126 -2 -25 0\n-126 -2 -42 0\n-126 -2 -48 0\n-126 -2 -65 0\n-126 -2 -71 0\n-126 -2 -88 0\n-126 -2 -94 0\n-126 -2 -100 0\n-126 -2 -117 0\n-126 3 20 26 43 49 66 72 78 95 101 118 0\n-126 4 21 27 44 50 56 73 79 96 102 119 0\n-126 -44 -102 0\n-126 -6 -12 0\n-126 -12 -35 0\n-126 -12 -58 0\n-126 -12 -75 0\n-126 -12 -81 0\n-126 -12 -104 0\n-126 -12 -121 0\n-126 7 13 30 36 53 59 76 82 99 105 111 0\n-126 8 14 31 37 54 60 77 83 89 106 112 0\n-127 -1 -17 0\n-127 -1 -33 0\n-127 -1 -54 0\n-127 -1 -59 0\n-127 -1 -75 0\n-127 -1 -101 0\n-127 -1 -117 0\n-127 -2 -18 0\n-127 -2 -23 0\n-127 -2 -55 0\n-127 -2 -76 0\n-127 -2 -81 0\n-127 -2 -97 0\n-127 -2 -102 0\n-127 -7 -12 0\n-127 -12 -49 0\n-127 -12 -65 0\n-127 -12 -70 0\n-127 -12 -112 0\n-127 -34 -92 0\n-127 9 14 30 35 51 56 72 88 93 109 114 0\n-127 11 16 32 37 53 58 74 79 95 100 116 0\n-128 -1 -16 0\n-128 -1 -31 0\n-128 -1 -50 0\n-128 -1 -65 0\n-128 -1 -84 0\n-128 -1 -99 0\n-128 -1 -103 0\n-128 -1 -118 0\n-128 -2 -17 0\n-128 -2 -32 0\n-128 -2 -36 0\n-128 -2 -51 0\n-128 -2 -66 0\n-128 -2 -85 0\n-128 -2 -89 0\n-128 -2 -119 0\n-128 -3 -56 0\n-128 6 21 25 40 55 59 74 78 93 108 112 0\n-128 -8 -12 0\n-128 -12 -27 0\n-128 -12 -42 0\n-128 -12 -46 0\n-128 -12 -76 0\n-128 -12 -80 0\n-128 -12 -95 0\n-128 -12 -110 0\n-128 -12 -114 0\n-128 11 15 30 34 49 64 68 83 98 102 117 0\n-128 -11 -49 0\n-128 -30 -102 0\n-128 -34 -83 0\n-129 -1 -15 0\n-129 -1 -29 0\n-129 -1 -43 0\n-129 -1 -46 0\n-129 -1 -60 0\n-129 -1 -74 0\n-129 -1 -88 0\n-129 -1 -119 0\n-129 -2 -16 0\n-129 -2 -30 0\n-129 -2 -44 0\n-129 -2 -75 0\n-129 -2 -78 0\n-129 -2 -92 0\n-129 -2 -106 0\n-129 3 17 31 34 48 62 76 79 93 107 121 0\n-129 -17 -93 0\n-129 5 19 33 36 50 64 67 81 95 109 112 0\n-129 -100 -114 0\n-129 -9 -12 0\n-129 -12 -40 0\n-129 -12 -54 0\n-129 -12 -57 0\n-129 -12 -99 0\n-129 -12 -102 0\n-129 -12 -116 0\n-129 10 13 27 41 55 58 72 86 89 103 117 0\n-129 11 14 28 42 45 59 73 87 90 104 118 0\n-130 -1 -14 0\n-130 -1 -27 0\n-130 -1 -53 0\n-130 -1 -66 0\n-130 -1 -68 0\n-130 -1 -81 0\n-130 -1 -94 0\n-130 -1 -107 0\n-130 -2 -15 0\n-130 -2 -28 0\n-130 -2 -41 0\n-130 -2 -56 0\n-130 -2 -82 0\n-130 -2 -95 0\n-130 -2 -108 0\n-130 -2 -121 0\n-130 4 17 30 43 45 58 71 84 97 110 112 0\n-130 5 18 31 44 46 59 72 85 98 100 113 0\n-130 -32 -114 0\n-130 -7 -102 0\n-130 8 21 23 36 49 62 75 88 90 103 116 0\n-130 -10 -12 0\n-130 -12 -51 0\n-130 -12 -64 0\n-130 -12 -77 0\n-130 -12 -79 0\n-130 -12 -92 0\n-130 -12 -105 0\n-130 -12 -118 0\n-130 11 13 26 39 52 65 67 80 93 106 119 0\n-131 -1 -13 0\n-131 -1 -25 0\n-131 -1 -37 0\n-131 -1 -49 0\n-131 -1 -73 0\n-131 -1 -85 0\n-131 -1 -109 0\n-131 -1 -121 0\n-131 -2 -14 0\n-131 -2 -38 0\n-131 -2 -50 0\n-131 -2 -62 0\n-131 -2 -74 0\n-131 -2 -86 0\n-131 -2 -98 0\n-131 -2 -110 0\n-131 -2 -111 0\n-131 4 16 28 40 52 64 76 88 89 101 113 0\n-131 5 17 29 41 53 65 77 78 90 102 114 0\n-131 -53 -114 0\n-131 -9 -34 0\n-131 -21 -58 0\n-131 10 22 23 35 47 59 71 83 95 107 119 0\n-131 -11 -12 0\n-131 -12 -24 0\n-131 -12 -36 0\n-131 -12 -60 0\n-131 -12 -72 0\n-131 -12 -84 0\n-131 -12 -96 0\n-131 -12 -108 0\n-131 -12 -120 0\n" "365 d 6 148 153 179 197 199 207 213 219 274 276 297 303 332 333 340 353 0\n367 -123 -21 0 1 113 0\n367 d 113 0\n368 -123 -30 0 1 114 0\n368 d 114 0\n369 -123 -57 0 1 115 0\n369 d 115 0\n370 -123 -86 0 1 116 0\n370 d 116 0\n371 -123 -95 0 1 117 0\n371 d 117 0\n372 -123 -113 0 1 118 0\n372 d 118 0\n373 -123 -22 0 3 119 0\n373 d 119 0\n374 -123 -40 0 3 120 0\n374 d 120 0\n375 -123 -58 0 3 121 0\n375 d 121 0\n376 -123 -67 0 3 122 0\n376 d 122 0\n377 -123 -105 0 3 123 0\n377 d 123 0\n378 -123 -114 0 3 124 0\n378 d 124 0\n379 -123 -3 0 2 125 0\n379 d 125 0\n380 -123 -41 0 2 126 0\n380 d 126 0\n381 -123 -59 0 2 127 0\n381 d 127 0\n382 -123 -88 0 2 128 0\n382 d 128 0\n383 -123 -97 0 2 129 0\n383 d 129 0\n384 -123 -106 0 2 130 0\n384 d 130 0\n385 -124 -28 0 1 135 0\n385 d 135 0\n386 -124 -36 0 1 136 0\n386 d 136 0\n387 -124 -55 0 1 137 0\n387 d 137 0\n388 -124 -63 0 1 138 0\n388 d 138 0\n389 -124 -71 0 1 139 0\n389 d 139 0\n390 -124 -79 0 1 140 0\n390 d 140 0\n391 -124 -98 0 1 141 0\n391 d 141 0\n392 -124 -106 0 1 142 0\n392 d 142 0\n393 -124 -114 0 1 143 0\n393 d 143 0\n394 -124 -21 0 3 144 0\n394 d 144 0\n395 -124 -45 0 3 145 0\n395 d 145 0\n396 -124 -64 0 3 146 0\n396 d 146 0\n397 -124 -72 0 3 147 0\n397 d 147 0\n399 -124 -99 0 3 149 0\n399 d 149 0\n400 -124 -107 0 3 150 0\n400 d 150 0\n401 -124 -4 0 2 151 0\n401 d 151 0\n402 -124 -31 0 2 152 0\n402 d 152 0\n404 -124 -74 0 2 154 0\n404 d 154 0\n405 -124 -82 0 2 155 0\n405 d 155 0\n406 -124 -90 0 2 156 0\n406 d 156 0\n407 -124 -109 0 2 157 0\n407 d 157 0\n408 -125 -19 0 1 165 0\n408 d 165 0\n409 -125 -26 0 1 166 0\n409 d 166 0\n410 -125 -44 0 1 167 0\n410 d 167 0\n411 -125 -58 0 1 168 0\n411 d 168 0\n412 -125 -76 0 1 169 0\n412 d 169 0\n413 -125 -83 0 1 170 0\n413 d 170 0\n414 -125 -90 0 1 171 0\n414 d 171 0\n415 -125 -108 0 1 172 0\n415 d 172 0\n416 -125 -20 0 3 173 0\n416 d 173 0\n417 -125 -27 0 3 174 0\n417 d 174 0\n418 -125 -34 0 3 175 0\n418 d 175 0\n419 -125 -52 0 3 176 0\n419 d 176 0\n420 -125 -59 0 3 177 0\n420 d 177 0\n421 -125 -77 0 3 178 0\n421 d 178 0\n423 -125 -116 0 3 180 0\n423 d 180 0\n424 -125 -5 0 2 181 0\n424 d 181 0\n425 -125 -30 0 2 182 0\n425 d 182 0\n426 -125 -37 0 2 183 0\n426 d 183 0\n427 -125 -62 0 2 184 0\n427 d 184 0\n428 -125 -94 0 2 185 0\n428 d 185 0\n429 -125 -101 0 2 186 0\n429 d 186 0\n430 -125 -119 0 2 187 0\n430 d 187 0\n431 -126 -18 0 1 193 0\n431 d 193 0\n432 -126 -24 0 1 194 0\n432 d 194 0\n433 -126 -41 0 1 195 0\n433 d 195 0\n434 -126 -47 0 1 196 0\n434 d 196 0\n436 -126 -93 0 1 198 0\n436 d 198 0\n438 -126 -116 0 1 200 0\n438 d 200 0\n439 -126 -19 0 3 201 0\n439 d 201 0\n440 -126 -25 0 3 202 0\n440 d 202 0\n441 -126 -42 0 3 203 0\n441 d 203 0\n442 -126 -48 0 3 204 0\n442 d 204 0\n443 -126 -65 0 3 205 0\n443 d 205 0\n444 -126 -71 0 3 206 0\n444 d 206 0\n446 -126 -94 0 3 208 0\n446 d 208 0\n447 -126 -100 0 3 209 0\n447 d 209 0\n448 -126 -117 0 3 210 0\n448 d 210 0\n449 -126 -6 0 2 214 0\n449 d 214 0\n450 -126 -35 0 2 215 0\n450 d 215 0\n451 -126 -58 0 2 216 0\n451 d 216 0\n452 -126 -75 0 2 217 0\n452 d 217 0\n453 -126 -81 0 2 218 0\n453 d 218 0\n455 -126 -121 0 2 220 0\n455 d 220 0\n456 -127 -17 0 1 223 0\n456 d 223 0\n457 -127 -33 0 1 224 0\n457 d 224 0\n458 -127 -54 0 1 225 0\n458 d 225 0\n459 -127 -59 0 1 226 0\n459 d 226 0\n460 -127 -75 0 1 227 0\n460 d 227 0\n461 -127 -101 0 1 228 0\n461 d 228 0\n462 -127 -117 0 1 229 0\n462 d 229 0\n463 -127 -18 0 3 230 0\n463 d 230 0\n464 -127 -23 0 3 231 0\n464 d 231 0\n465 -127 -55 0 3 232 0\n465 d 232 0\n466 -127 -76 0 3 233 0\n466 d 233 0\n467 -127 -81 0 3 234 0\n467 d 234 0\n468 -127 -97 0 3 235 0\n468 d 235 0\n469 -127 -102 0 3 236 0\n469 d 236 0\n470 -127 -7 0 2 237 0\n470 d 237 0\n471 -127 -49 0 2 238 0\n471 d 238 0\n472 -127 -65 0 2 239 0\n472 d 239 0\n473 -127 -70 0 2 240 0\n473 d 240 0\n474 -127 -112 0 2 241 0\n474 d 241 0\n475 -128 -16 0 1 245 0\n475 d 245 0\n476 -128 -31 0 1 246 0\n476 d 246 0\n477 -128 -50 0 1 247 0\n477 d 247 0\n478 -128 -65 0 1 248 0\n478 d 248 0\n479 -128 -84 0 1 249 0\n479 d 249 0\n480 -128 -99 0 1 250 0\n480 d 250 0\n481 -128 -103 0 1 251 0\n481 d 251 0\n482 -128 -118 0 1 252 0\n482 d 252 0\n483 -128 -17 0 3 253 0\n483 d 253 0\n484 -128 -32 0 3 254 0\n484 d 254 0\n485 -128 -36 0 3 255 0\n485 d 255 0\n486 -128 -51 0 3 256 0\n486 d 256 0\n487 -128 -66 0 3 257 0\n487 d 257 0\n488 -128 -85 0 3 258 0\n488 d 258 0\n489 -128 -89 0 3 259 0\n489 d 259 0\n490 -128 -119 0 3 260 0\n490 d 260 0\n491 -128 -8 0 2 263 0\n491 d 263 0\n492 -128 -27 0 2 264 0\n492 d 264 0\n493 -128 -42 0 2 265 0\n493 d 265 0\n494 -128 -46 0 2 266 0\n494 d 266 0\n495 -128 -76 0 2 267 0\n495 d 267 0\n496 -128 -80 0 2 268 0\n496 d 268 0\n497 -128 -95 0 2 269 0\n497 d 269 0\n498 -128 -110 0 2 270 0\n498 d 270 0\n499 -128 -114 0 2 271 0\n499 d 271 0\n501 -129 -29 0 1 277 0\n501 d 277 0\n502 -129 -43 0 1 278 0\n502 d 278 0\n503 -129 -46 0 1 279 0\n503 d 279 0\n504 -129 -60 0 1 280 0\n504 d 280 0\n505 -129 -74 0 1 281 0\n505 d 281 0\n506 -129 -88 0 1 282 0\n506 d 282 0\n507 -129 -119 0 1 283 0\n507 d 283 0\n508 -129 -16 0 3 284 0\n508 d 284 0\n509 -129 -30 0 3 285 0\n509 d 285 0\n510 -129 -44 0 3 286 0\n510 d 286 0\n511 -129 -75 0 3 287 0\n511 d 287 0\n512 -129 -78 0 3 288 0\n512 d 288 0\n513 -129 -92 0 3 289 0\n513 d 289 0\n514 -129 -106 0 3 290 0\n514 d 290 0\n515 -129 -9 0 2 295 0\n515 d 295 0\n516 -129 -40 0 2 296 0\n516 d 296 0\n518 -129 -57 0 2 298 0\n518 d 298 0\n519 -129 -99 0 2 299 0\n519 d 299 0\n520 -129 -102 0 2 300 0\n520 d 300 0\n521 -129 -116 0 2 301 0\n521 d 301 0\n522 -130 -14 0 1 304 0\n522 d 304 0\n523 -130 -27 0 1 305 0\n523 d 305 0\n524 -130 -53 0 1 306 0\n524 d 306 0\n525 -130 -66 0 1 307 0\n525 d 307 0\n526 -130 -68 0 1 308 0\n526 d 308 0\n527 -130 -81 0 1 309 0\n527 d 309 0\n528 -130 -94 0 1 310 0\n528 d 310 0\n529 -130 -107 0 1 311 0\n529 d 311 0\n530 -130 -15 0 3 312 0\n530 d 312 0\n531 -130 -28 0 3 313 0\n531 d 313 0\n532 -130 -41 0 3 314 0\n532 d 314 0\n533 -130 -56 0 3 315 0\n533 d 315 0\n534 -130 -82 0 3 316 0\n534 d 316 0\n535 -130 -95 0 3 317 0\n535 d 317 0\n536 -130 -108 0 3 318 0\n536 d 318 0\n537 -130 -121 0 3 319 0\n537 d 319 0\n538 -130 -10 0 2 325 0\n538 d 325 0\n539 -130 -51 0 2 326 0\n539 d 326 0\n540 -130 -64 0 2 327 0\n540 d 327 0\n541 -130 -77 0 2 328 0\n541 d 328 0\n542 -130 -79 0 2 329 0\n542 d 329 0\n543 -130 -92 0 2 330 0\n543 d 330 0\n544 -130 -105 0 2 331 0\n544 d 331 0\n546 -131 -13 0 1 334 0\n546 d 334 0\n547 -131 -25 0 1 335 0\n547 d 335 0\n548 -131 -37 0 1 336 0\n548 d 336 0\n549 -131 -49 0 1 337 0\n549 d 337 0\n550 -131 -73 0 1 338 0\n550 d 338 0\n551 -131 -85 0 1 339 0\n551 d 339 0\n553 -131 -121 0 1 341 0\n553 d 341 0\n554 -131 -14 0 3 342 0\n554 d 342 0\n555 -131 -38 0 3 343 0\n555 d 343 0\n556 -131 -50 0 3 344 0\n556 d 344 0\n557 -131 -62 0 3 345 0\n557 d 345 0\n558 -131 -74 0 3 346 0\n558 d 346 0\n559 -131 -86 0 3 347 0\n559 d 347 0\n560 -131 -98 0 3 348 0\n560 d 348 0\n561 -131 -110 0 3 349 0\n561 d 349 0\n562 -131 -111 0 3 350 0\n562 d 350 0\n563 -131 -11 0 2 357 0\n563 d 357 0\n564 -131 -24 0 2 358 0\n564 d 358 0\n565 -131 -36 0 2 359 0\n565 d 359 0\n566 -131 -60 0 2 360 0\n566 d 360 0\n567 -131 -72 0 2 361 0\n567 d 361 0\n568 -131 -84 0 2 362 0\n568 d 362 0\n569 -131 -96 0 2 363 0\n569 d 363 0\n570 -131 -108 0 2 364 0\n570 d 364 0\n571 -131 -120 0 2 365 0\n571 d 365 0\n572 -127 -128 -129 -130 -131 0 2 3 112 459 460 462 463 464 465 466 470 471 546 547 556 559 562 567 563 565 502 506 509 519 518 481 489 499 491 492 524 529 532 534 544 538 192 302 221 375 557 521 355 324 406 4 0\n572 d 557 521 355 4 0\n573 125 126 -128 -129 -130 -131 0 2 3 112 502 508 520 486 491 528 537 559 564 572 20 376 381 160 51 0\n573 d 20 51 0\n574 -125 -128 -129 -130 -131 0 414 421 424 501 512 520 478 483 499 524 532 352 0\n575 -128 -129 -130 -131 0 2 3 112 479 481 487 489 492 494 531 532 538 511 520 546 548 559 562 567 572 574 573 436 439 448 451 134 302 387 5 0\n575 d 572 574 573 302 5 0\n576 -124 -126 -129 -130 -131 0 390 394 401 550 556 569 507 520 523 533 212 510 0\n576 d 510 0\n577 -126 -129 -130 -131 0 2 3 112 436 439 452 524 525 531 534 544 538 575 503 509 519 520 546 548 562 568 565 134 576 11 459 466 470 221 0\n577 d 576 11 0\n578 124 -129 -130 -131 0 2 3 112 524 532 535 541 542 575 577 501 505 508 512 520 548 563 52 414 423 424 64 456 472 352 411 294 244 322 0\n578 d 52 64 411 294 322 0\n579 -127 -129 -130 -131 0 2 3 112 456 469 472 474 524 541 575 577 578 502 509 512 561 568 389 393 395 401 406 468 320 375 532 501 352 424 21 0\n579 d 468 532 501 352 21 0\n580 -129 -130 -131 0 2 3 112 502 505 508 509 513 520 515 548 553 559 561 562 568 564 565 523 528 531 538 539 503 511 525 575 577 578 389 395 401 579 81 408 413 420 429 32 375 376 383 134 160 292 320 163 133 190 0\n580 d 503 511 525 575 577 578 579 81 32 292 190 0\n581 126 128 -130 -131 0 2 3 112 527 547 561 568 567 580 85 414 418 425 430 99 456 458 470 474 67 388 389 395 401 36 375 383 132 320 161 0\n581 d 85 99 67 36 161 0\n582 -127 128 -130 -131 0 2 3 112 459 461 464 470 529 530 541 538 581 556 580 571 436 441 450 451 535 551 159 434 444 58 413 430 14 356 373 0\n582 d 535 551 159 434 444 58 14 356 373 0\n583 128 -130 -131 0 2 3 112 546 556 562 565 580 523 524 533 534 542 544 550 569 581 582 42 367 368 381 90 410 430 71 399 401 412 221 323 212 0\n583 d 550 569 581 582 42 90 71 412 212 0\n584 -123 -125 -130 -131 0 372 384 533 538 549 558 583 564 480 483 493 191 527 0\n584 d 527 0\n585 -125 127 -130 -131 0 2 3 112 413 418 420 425 524 526 530 534 544 540 546 549 560 562 583 563 565 580 480 495 584 33 221 323 272 448 0\n585 d 584 33 448 0\n586 127 -130 -131 0 2 3 112 546 548 562 568 565 580 583 524 534 538 480 487 494 495 531 544 585 82 436 452 25 368 381 221 439 323 134 0\n586 d 531 544 585 82 25 439 323 134 0\n587 -123 125 -130 -131 0 2 3 112 368 381 546 547 553 558 561 567 586 565 580 583 523 524 543 458 461 463 466 467 470 472 475 490 377 562 534 480 221 53 388 395 406 132 354 275 133 0\n587 d 377 562 534 480 221 53 0\n588 -126 -130 -131 0 438 447 451 558 586 563 583 524 542 475 484 497 244 548 0\n588 d 548 0\n589 125 -130 -131 0 2 3 112 580 588 587 22 0\n589 d 580 588 587 22 0\n590 -130 -131 0 530 549 563 526 540 560 589 413 418 583 586 469 425 462 272 0\n590 d 526 540 560 589 583 586 425 462 272 0\n591 123 124 -125 -127 -128 -131 0 2 3 112 476 489 491 458 474 413 421 426 554 590 566 17 514 222 9 0\n591 d 17 9 0\n592 124 -125 -127 -128 -131 0 2 3 112 547 553 554 558 561 590 565 566 567 458 461 463 467 470 472 474 413 414 417 418 421 426 430 475 476 489 491 591 384 132 222 189 69 513 515 133 0\n592 d 591 69 0\n593 -128 -125 -127 -131 0 2 3 112 475 476 477 489 490 498 491 547 554 590 563 567 458 460 463 467 470 474 413 414 418 426 499 592 388 392 400 405 132 566 421 222 39 502 518 192 0\n593 d 499 592 566 421 39 0\n594 123 -125 -127 -131 0 2 3 112 549 554 568 593 590 457 466 37 447 449 15 430 47 513 518 158 433 0\n594 d 37 15 430 47 433 0\n595 -129 -125 -127 -131 0 505 507 513 515 547 553 594 565 567 458 461 463 467 470 472 413 414 417 418 133 508 561 132 189 0\n595 d 508 561 189 0\n596 -127 -125 -131 0 2 3 112 590 469 473 546 555 595 571 593 594 371 382 104 449 77 388 395 188 402 0\n596 d 469 473 546 555 595 571 593 594 104 77 188 402 0\n597 129 -123 -125 -131 0 2 3 112 429 372 374 382 596 590 74 396 401 108 475 489 495 419 385 351 0\n597 d 74 108 419 385 351 0\n598 -128 -123 -125 -131 0 2 3 112 475 482 486 491 497 553 559 596 590 420 429 597 376 379 502 512 520 487 549 564 567 409 416 428 160 211 65 0\n598 d 487 549 564 567 409 416 428 211 65 0\n599 -123 -125 -131 0 2 3 112 553 558 590 596 413 417 429 598 565 597 513 515 100 431 443 133 395 72 0\n599 d 598 565 597 100 72 0\n600 -125 -131 0 2 3 112 547 590 556 599 563 596 34 431 452 12 393 400 405 45 502 518 192 489 43 0\n600 d 556 599 563 596 34 12 45 43 0\n601 127 -131 0 2 3 112 553 600 590 83 432 446 93 502 520 559 56 91 475 486 491 26 376 381 160 0\n601 d 83 93 559 56 91 26 0\n602 -124 -123 -128 -131 0 386 388 395 397 404 406 547 601 475 478 490 498 492 458 463 467 470 132 553 461 354 275 133 242 0\n602 d 553 461 354 275 242 0\n603 -128 -123 -131 0 2 3 112 547 558 601 600 590 570 367 374 381 465 474 602 54 436 449 262 512 61 0\n603 d 602 54 61 0\n604 -123 -131 0 2 3 112 369 380 601 600 590 457 471 554 603 568 466 86 447 449 95 513 59 158 507 0\n604 d 554 603 568 466 86 95 59 507 0\n605 -131 0 2 3 112 547 558 604 601 465 474 600 590 570 459 29 512 516 28 23 436 449 262 394 7 0\n605 d 547 558 604 601 600 590 570 459 29 28 23 7 0\n606 125 123 -124 -128 0 2 3 112 605 486 393 397 407 30 506 509 515 31 522 533 24 436 450 243 27 0\n606 d 30 31 24 27 0\n607 -126 123 -124 -128 -130 0 2 3 112 605 431 438 440 447 452 475 476 477 489 606 524 529 542 393 397 404 405 410 420 424 426 451 484 488 494 497 391 321 164 244 46 502 518 192 0\n607 d 451 484 488 494 497 391 321 244 46 0\n608 -130 123 -124 -128 0 2 3 112 605 481 485 491 606 394 406 423 427 607 35 460 464 471 324 506 40 0\n608 d 607 35 40 0\n609 -124 123 -128 0 2 3 112 605 390 393 399 400 404 476 477 483 489 495 387 392 394 405 608 493 606 415 418 427 41 431 432 436 440 442 453 455 449 452 50 502 512 291 420 518 516 262 261 192 162 273 191 164 0\n609 d 387 392 394 405 608 493 606 41 50 420 518 516 261 192 162 273 164 0\n610 -128 123 0 2 3 112 605 476 489 491 609 19 522 18 8 413 10 13 458 474 541 504 514 426 222 0\n610 d 609 19 18 8 10 13 541 504 514 426 222 0\n611 128 123 0 2 3 112 605 49 48 44 38 16 522 533 539 506 509 515 436 450 393 397 407 243 0\n611 d 49 48 44 38 16 506 509 393 0\n612 123 0 610 611 0\n612 d 610 611 0\n631 9 -124 -126 128 -130 0 2 3 112 605 612 368 378 382 522 523 533 537 543 386 395 397 404 407 431 436 443 539 450 243 92 413 429 133 0\n631 d 378 539 450 243 92 0\n632 -126 -124 128 -130 0 2 3 112 605 612 372 384 432 441 453 533 538 404 631 515 399 96 109 456 471 191 0\n632 d 631 399 96 109 0\n633 -130 -124 128 0 2 3 112 605 612 537 543 386 395 404 523 632 87 413 429 105 515 101 463 133 472 0\n633 d 523 632 87 105 101 463 472 0\n634 -124 128 0 2 3 112 605 612 395 404 386 633 97 413 429 106 455 111 515 417 431 443 133 513 0\n634 d 386 633 97 106 111 417 431 443 513 0\n635 124 128 0 2 3 112 605 612 372 384 60 68 78 73 79 432 441 453 505 519 456 471 533 538 191 0\n635 d 372 384 60 68 78 73 79 441 519 456 533 538 191 0\n636 128 0 634 635 0\n636 d 634 635 0\n660 -125 -126 -129 -130 0 612 379 636 476 483 495 418 427 537 436 442 529 291 542 0\n660 d 529 542 0\n661 -129 124 -126 -130 0 2 3 112 605 612 367 374 381 636 505 512 436 440 449 660 536 57 465 474 262 0\n661 d 660 536 57 0\n662 -126 124 -130 0 2 3 112 605 612 367 382 636 481 485 491 438 452 661 75 464 471 62 414 427 324 0\n662 d 438 452 661 75 62 0\n663 -130 124 0 2 3 112 605 612 367 382 636 481 485 491 662 55 423 427 66 460 464 471 324 414 0\n663 d 662 55 66 414 0\n664 130 124 0 2 3 112 605 612 367 374 381 636 63 80 70 76 415 505 512 436 440 449 465 474 262 0\n664 d 374 63 80 70 76 415 505 512 465 262 0\n665 124 0 663 664 0\n665 d 663 664 0\n682 -125 -126 130 0 2 3 112 605 612 379 636 475 476 483 490 495 498 665 388 390 397 400 406 427 455 418 436 440 442 453 291 110 458 470 132 0\n682 d 379 476 388 390 397 400 418 436 440 442 453 291 110 458 470 132 0\n683 -126 130 0 2 3 112 605 612 370 376 381 636 475 486 491 665 432 446 682 455 98 502 520 160 0\n683 d 446 682 455 98 0\n684 126 130 0 2 3 112 605 612 371 376 636 477 485 665 396 407 89 107 103 408 424 457 467 474 293 0\n684 d 371 477 396 89 107 103 408 424 467 293 0\n685 130 0 683 684 0\n685 d 683 684 0\n698 -129 -125 0 612 368 375 383 636 478 479 483 485 492 498 665 389 395 401 404 685 537 543 502 320 515 413 429 163 133 0\n698 d 478 492 404 515 413 429 163 133 0\n699 -125 126 0 2 3 112 605 612 367 382 636 481 485 491 665 406 685 427 423 698 102 471 460 464 324 0\n699 d 367 382 481 485 406 423 698 102 460 464 324 0\n700 125 126 0 2 3 112 605 612 368 375 383 636 479 483 498 665 389 395 401 685 88 84 502 474 320 0\n700 d 368 375 383 483 498 395 401 88 84 474 320 0\n701 126 0 699 700 0\n701 d 699 700 0\n717 -129 0 612 370 376 381 636 475 486 491 665 685 528 537 701 432 502 520 160 0\n717 d 370 376 381 475 486 491 528 537 502 520 160 0\n718 -127 0 612 369 380 636 479 490 495 665 685 522 543 701 447 449 457 471 158 0\n718 d 369 380 479 490 495 522 543 447 457 471 158 0\n732 0 2 3 112 605 612 636 482 489 496 665 389 407 685 524 530 701 432 449 717 718 94 410 427 131 0\n"

private def f11_opt : Finset (ZMod 11) := {1,2,3,4,5,6,7,8,9,10}
private def f11_point (i : Nat) : ZMod 11 × ZMod 11 := (((i / 11 : Nat) : ZMod 11), ((i % 11 : Nat) : ZMod 11))
private def f11_form (a : ZMod 11) (p : ZMod 11 × ZMod 11) : ZMod 11 := p.2 + a * p.1
private def f11_flag (i : Nat) : ZMod 11 := if i = 121 then 1 else if i = 122 then 2 else if i = 123 then 3 else if i = 124 then 4 else if i = 125 then 5 else if i = 126 then 6 else if i = 127 then 7 else if i = 128 then 8 else if i = 129 then 9 else if i = 130 then 10 else 0
private def f11_val (S : Finset (ZMod 11 × ZMod 11)) (g : ZMod 11 → Prop) : Sat.Valuation := fun i => if i < 121 then f11_point i ∈ S else g (f11_flag i)

private theorem f11_sat_and {v : Sat.Valuation} {f g : Sat.Fmla} (hf : v.satisfies_fmla f) (hg : v.satisfies_fmla g) : v.satisfies_fmla (f.and g) := by
  refine ⟨?_⟩
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hf.prop c h
  · exact hg.prop c h
private theorem f11_sat_one {v : Sat.Valuation} {c : Sat.Clause} (h : v.satisfies c) : v.satisfies_fmla (Sat.Fmla.one c) := by
  refine ⟨?_⟩
  intro c' hc'
  have hc : c' = c := List.mem_singleton.mp hc'
  simpa only [hc] using h
private theorem f11_sat_positive_mem (v : Sat.Valuation) (L : Sat.Clause) (i : Nat)
    (hi : List.Mem (Sat.Literal.pos i) L) (hv : v i) : v.satisfies L := by
  change List Sat.Literal at L
  induction L with
  | nil => cases hi
  | cons a as ih =>
    change v.neg a → v.satisfies as
    intro hn
    rcases List.mem_cons.mp hi with h | h
    · subst a
      exact False.elim (hn hv)
    · exact ih h
private theorem f11_point_index (p : ZMod 11 × ZMod 11) :
    f11_point (11*p.1.val + p.2.val) = p := by
  have hy := ZMod.val_lt p.2
  have hdiv : (11*p.1.val+p.2.val)/11 = p.1.val := by omega
  have hmod : (11*p.1.val+p.2.val)%11 = p.2.val := by omega
  apply Prod.ext
  · simp [f11_point,hdiv]
  · simp [f11_point,hmod]
private theorem f11_sat_line (S : Finset (ZMod 11 × ZMod 11)) (g : ZMod 11 → Prop)
    (a t : ZMod 11) (L : List (Fin 121))
    (hcover : ∃ p ∈ S, f11_form a p = t)
    (hidx : ∀ x : ZMod 11, 11*x.val + (t-a*x).val ∈ L.map Fin.val) :
    (f11_val S g).satisfies (L.map fun i => Sat.Literal.pos i.val) := by
  obtain ⟨p,hp,hpform⟩ := hcover
  have hp2 : p.2 = t-a*p.1 := by
    dsimp [f11_form] at hpform
    linear_combination hpform
  have hm : 11*p.1.val+p.2.val ∈ L.map Fin.val := by
    simpa only [hp2] using hidx p.1
  obtain ⟨i,hi,hieq⟩ := List.mem_map.mp hm
  apply f11_sat_positive_mem (f11_val S g) (L.map fun i => Sat.Literal.pos i.val) i.val
  · exact List.mem_map.mpr ⟨i,hi,rfl⟩
  · have hpoint : f11_point i.val = p := by rw [hieq]; exact f11_point_index p
    simp only [f11_val, i.isLt, if_true, hpoint]
    exact hp

theorem good_slopes_prime11_three_anchor (S : Finset (ZMod 11 × ZMod 11)) (g : ZMod 11 → Prop)
  (h0 : (0,0) ∈ S) (h1 : (1,0) ∈ S) (h2 : (0,1) ∈ S)
  (hinj : ∀ a ∈ ({1,2,3,4,5,6,7,8,9,10} : Finset (ZMod 11)), g a → Set.InjOn (fun p : ZMod 11 × ZMod 11 => p.2 + a*p.1) S)
  (hcover : ∀ a ∈ ({1,2,3,4,5,6,7,8,9,10} : Finset (ZMod 11)), g a → ∀ t : ZMod 11, ∃ p ∈ S, p.2 + a*p.1 = t)
  (hfive : ∀ T : Finset (ZMod 11), T ⊆ ({1,2,3,4,5,6,7,8,9,10} : Finset (ZMod 11)) → T.card = 5 → ∃ a ∈ T, g a)
  : False := by
  change ∀ a ∈ f11_opt, g a → Set.InjOn (f11_form a) S at hinj
  change ∀ a ∈ f11_opt, g a → ∀ t : ZMod 11, ∃ p ∈ S, f11_form a p = t at hcover
  change ∀ T : Finset (ZMod 11), T ⊆ f11_opt → T.card = 5 → ∃ a ∈ T, g a at hfive
  have hF : (f11_val S g).satisfies_fmla aftd_n11_formula := by
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ f11_point 0 ∈ S) → False
    intro h; apply h
    simpa [f11_point] using h0
    apply f11_sat_one
    change (¬ f11_point 11 ∈ S) → False
    intro h; apply h
    simpa [f11_point] using h1
    apply f11_sat_and
    apply f11_sat_one
    change (¬ f11_point 1 ∈ S) → False
    intro h; apply h
    simpa [f11_point] using h2
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 4) → (¬ g 5) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,4,5} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 4) → (¬ g 6) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,4,6} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 4) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,4,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 4) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,4,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 4) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,4,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 5) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,5,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 5) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,5,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 6) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,6,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 3) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,3,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 5) → (¬ g 6) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,5,6} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 5) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,5,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 5) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,5,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 5) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,5,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 5) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,5,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 6) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,6,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 4) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,4,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 6) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,6,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 6) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,6,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 5) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,5,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 6) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,6,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 6) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,6,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 6) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,6,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 6) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,6,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 6) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,6,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 7) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,7,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 7) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,7,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 7) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,7,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 2) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,2,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 5) → (¬ g 6) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,5,6} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 5) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,5,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 5) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,5,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 5) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,5,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 5) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,5,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 4) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,4,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 6) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,6,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 5) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,5,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 6) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,6,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 7) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,7,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 7) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,7,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 7) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,7,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 3) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,3,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 6) → (¬ g 7) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,6,7} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 6) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,6,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 6) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,6,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 6) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,6,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 5) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,5,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 6) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,6,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 6) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,6,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 6) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,6,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 6) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,6,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 6) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,6,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 7) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,7,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 7) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,7,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 7) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,7,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 4) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,4,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 6) → (¬ g 7) → (¬ g 8) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,6,7,8} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 6) → (¬ g 7) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,6,7,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 6) → (¬ g 7) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,6,7,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 6) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,6,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 6) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,6,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 7) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,7,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 7) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,7,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 7) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,7,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 5) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,5,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 6) → (¬ g 7) → (¬ g 8) → (¬ g 9) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,6,7,8,9} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 6) → (¬ g 7) → (¬ g 8) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,6,7,8,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_one
    change (¬ g 1) → (¬ g 6) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,6,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change (¬ g 1) → (¬ g 7) → (¬ g 8) → (¬ g 9) → (¬ g 10) → False
    intro ha hb hc hd he
    obtain ⟨a,ha,hg⟩ := hfive {1,7,8,9,10} (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> contradiction
    apply f11_sat_and
    apply f11_sat_one
    change g 1 → f11_point 1 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 11) (hinj 1 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 20 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 20) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 29 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 29) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 56 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 56) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 85 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 85) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 94 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 94) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 0 ∈ S → f11_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 112) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 21 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 21) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 39 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 39) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 57 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 57) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 66 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 66) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 104 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 104) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 1 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 113) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 2 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 2 ≠ f11_point 11) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 11 ∈ S → f11_point 40 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 40) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 11 ∈ S → f11_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 58) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 11 ∈ S → f11_point 87 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 87) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → f11_point 11 ∈ S → f11_point 96 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 96) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 2 → f11_point 11 ∈ S → f11_point 105 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 105) (hinj 2 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → (f11_val S g).satisfies (([5, 14, 23, 43, 52, 61, 70, 79, 88, 108, 117] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 2 5 ([5, 14, 23, 43, 52, 61, 70, 79, 88, 108, 117] : List (Fin 121)) (hcover 2 (by decide) hg 5)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → (f11_val S g).satisfies (([6, 15, 24, 33, 53, 62, 71, 80, 89, 109, 118] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 2 6 ([6, 15, 24, 33, 53, 62, 71, 80, 89, 109, 118] : List (Fin 121)) (hcover 2 (by decide) hg 6)
    decide +revert
    apply f11_sat_one
    change g 2 → (f11_val S g).satisfies (([8, 17, 26, 35, 44, 64, 73, 82, 91, 100, 120] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 2 8 ([8, 17, 26, 35, 44, 64, 73, 82, 91, 100, 120] : List (Fin 121)) (hcover 2 (by decide) hg 8)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 2 → (f11_val S g).satisfies (([9, 18, 27, 36, 45, 65, 74, 83, 92, 101, 110] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 2 9 ([9, 18, 27, 36, 45, 65, 74, 83, 92, 101, 110] : List (Fin 121)) (hcover 2 (by decide) hg 9)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 27 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 27) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 35 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 35) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 54 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 54) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 62 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 62) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 70 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 70) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 78 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 78) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 97 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 97) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 105 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 105) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 0 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 113) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 20 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 20) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 44 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 44) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 63 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 63) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 71 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 71) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 79 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 79) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 98 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 98) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 1 ∈ S → f11_point 106 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 106) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 3 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 3 ≠ f11_point 11) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 30 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 30) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 38 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 38) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 73 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 73) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 81 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 81) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 89 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 89) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 11 ∈ S → f11_point 108 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 108) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → (f11_val S g).satisfies (([5, 13, 32, 40, 48, 56, 75, 83, 91, 99, 118] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 3 5 ([5, 13, 32, 40, 48, 56, 75, 83, 91, 99, 118] : List (Fin 121)) (hcover 3 (by decide) hg 5)
    decide +revert
    apply f11_sat_one
    change g 3 → (f11_val S g).satisfies (([6, 14, 22, 41, 49, 57, 76, 84, 92, 100, 119] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 3 6 ([6, 14, 22, 41, 49, 57, 76, 84, 92, 100, 119] : List (Fin 121)) (hcover 3 (by decide) hg 6)
    decide +revert
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → (f11_val S g).satisfies (([7, 15, 23, 42, 50, 58, 66, 85, 93, 101, 120] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 3 7 ([7, 15, 23, 42, 50, 58, 66, 85, 93, 101, 120] : List (Fin 121)) (hcover 3 (by decide) hg 7)
    decide +revert
    apply f11_sat_one
    change g 3 → f11_point 15 ∈ S → f11_point 42 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 15 ≠ f11_point 42) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 9 ∈ S → f11_point 111 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 9 ≠ f11_point 111) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 3 → f11_point 17 ∈ S → f11_point 111 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 17 ≠ f11_point 111) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 3 → f11_point 10 ∈ S → f11_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 10 ≠ f11_point 112) (hinj 3 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 18 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 18) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 25 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 25) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 43 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 43) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 57 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 57) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 75 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 75) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 82 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 82) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 89 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 89) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 0 ∈ S → f11_point 107 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 107) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 19 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 19) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 26) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 33 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 33) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 51 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 51) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 58) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 76 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 76) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 83 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 83) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 1 ∈ S → f11_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 115) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 4 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 4 ≠ f11_point 11) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 29 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 29) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 36 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 36) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 61 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 61) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 93 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 93) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 100 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 100) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 11 ∈ S → f11_point 118 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 118) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → (f11_val S g).satisfies (([5, 12, 30, 37, 44, 62, 69, 87, 94, 101, 119] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 4 5 ([5, 12, 30, 37, 44, 62, 69, 87, 94, 101, 119] : List (Fin 121)) (hcover 4 (by decide) hg 5)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → f11_point 44 ∈ S → f11_point 62 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 44 ≠ f11_point 62) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 4 → f11_point 7 ∈ S → f11_point 64 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 7 ≠ f11_point 64) (hinj 4 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → (f11_val S g).satisfies (([9, 16, 23, 41, 48, 55, 73, 80, 98, 105, 112] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 4 9 ([9, 16, 23, 41, 48, 55, 73, 80, 98, 105, 112] : List (Fin 121)) (hcover 4 (by decide) hg 9)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 4 → (f11_val S g).satisfies (([10, 17, 24, 42, 49, 56, 74, 81, 88, 106, 113] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 4 10 ([10, 17, 24, 42, 49, 56, 74, 81, 88, 106, 113] : List (Fin 121)) (hcover 4 (by decide) hg 10)
    decide +revert
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 17 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 17) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 23 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 23) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 40 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 40) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 46 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 46) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 86 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 86) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 92 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 92) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 109 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 109) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 0 ∈ S → f11_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 115) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 18 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 18) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 24 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 24) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 41) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 47 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 47) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 64 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 64) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 70 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 70) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 87 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 87) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 93 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 93) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 99 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 99) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 1 ∈ S → f11_point 116 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 116) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → (f11_val S g).satisfies (([2, 19, 25, 42, 48, 65, 71, 77, 94, 100, 117] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 5 2 ([2, 19, 25, 42, 48, 65, 71, 77, 94, 100, 117] : List (Fin 121)) (hcover 5 (by decide) hg 2)
    decide +revert
    apply f11_sat_one
    change g 5 → (f11_val S g).satisfies (([3, 20, 26, 43, 49, 55, 72, 78, 95, 101, 118] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 5 3 ([3, 20, 26, 43, 49, 55, 72, 78, 95, 101, 118] : List (Fin 121)) (hcover 5 (by decide) hg 3)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 43 ∈ S → f11_point 101 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 43 ≠ f11_point 101) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 5 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 5 ≠ f11_point 11) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 34 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 34) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 57 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 57) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 74 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 74) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 80 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 80) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 103 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 103) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → f11_point 11 ∈ S → f11_point 120 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 120) (hinj 5 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 5 → (f11_val S g).satisfies (([6, 12, 29, 35, 52, 58, 75, 81, 98, 104, 110] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 5 6 ([6, 12, 29, 35, 52, 58, 75, 81, 98, 104, 110] : List (Fin 121)) (hcover 5 (by decide) hg 6)
    decide +revert
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 5 → (f11_val S g).satisfies (([7, 13, 30, 36, 53, 59, 76, 82, 88, 105, 111] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 5 7 ([7, 13, 30, 36, 53, 59, 76, 82, 88, 105, 111] : List (Fin 121)) (hcover 5 (by decide) hg 7)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 16 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 16) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 32 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 32) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 53 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 53) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 58) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 74 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 74) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 100 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 100) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 0 ∈ S → f11_point 116 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 116) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 17 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 17) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 22 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 22) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 54 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 54) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 75 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 75) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 80 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 80) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 96 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 96) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 1 ∈ S → f11_point 101 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 101) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 6 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 6 ≠ f11_point 11) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 11 ∈ S → f11_point 48 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 48) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 11 ∈ S → f11_point 64 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 64) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 11 ∈ S → f11_point 69 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 69) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 6 → f11_point 11 ∈ S → f11_point 111 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 111) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → f11_point 33 ∈ S → f11_point 91 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 33 ≠ f11_point 91) (hinj 6 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 6 → (f11_val S g).satisfies (([8, 13, 29, 34, 50, 55, 71, 87, 92, 108, 113] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 6 8 ([8, 13, 29, 34, 50, 55, 71, 87, 92, 108, 113] : List (Fin 121)) (hcover 6 (by decide) hg 8)
    decide +revert
    apply f11_sat_one
    change g 6 → (f11_val S g).satisfies (([10, 15, 31, 36, 52, 57, 73, 78, 94, 99, 115] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 6 10 ([10, 15, 31, 36, 52, 57, 73, 78, 94, 99, 115] : List (Fin 121)) (hcover 6 (by decide) hg 10)
    decide +revert
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 15 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 15) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 30 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 30) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 49 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 49) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 64 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 64) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 83 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 83) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 98 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 98) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 102 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 102) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 0 ∈ S → f11_point 117 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 117) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 16 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 16) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 31 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 31) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 35 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 35) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 50 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 50) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 65 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 65) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 84 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 84) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 88 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 88) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 1 ∈ S → f11_point 118 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 118) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 2 ∈ S → f11_point 55 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 2 ≠ f11_point 55) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → (f11_val S g).satisfies (([5, 20, 24, 39, 54, 58, 73, 77, 92, 107, 111] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 7 5 ([5, 20, 24, 39, 54, 58, 73, 77, 92, 107, 111] : List (Fin 121)) (hcover 7 (by decide) hg 5)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 7 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 7 ≠ f11_point 11) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 26) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 41) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 45 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 45) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 75 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 75) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 79 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 79) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 94 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 94) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 109 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 109) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 11 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 113) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → (f11_val S g).satisfies (([10, 14, 29, 33, 48, 63, 67, 82, 97, 101, 116] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 7 10 ([10, 14, 29, 33, 48, 63, 67, 82, 97, 101, 116] : List (Fin 121)) (hcover 7 (by decide) hg 10)
    decide +revert
    apply f11_sat_one
    change g 7 → f11_point 10 ∈ S → f11_point 48 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 10 ≠ f11_point 48) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 7 → f11_point 29 ∈ S → f11_point 101 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 29 ≠ f11_point 101) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 7 → f11_point 33 ∈ S → f11_point 82 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 33 ≠ f11_point 82) (hinj 7 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 14 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 14) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 28 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 28) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 42 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 42) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 45 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 45) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 59 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 59) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 73 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 73) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 87 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 87) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 0 ∈ S → f11_point 118 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 118) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 15 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 15) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 29 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 29) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 43 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 43) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 74 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 74) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 77 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 77) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 91 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 91) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 1 ∈ S → f11_point 105 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 105) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → (f11_val S g).satisfies (([2, 16, 30, 33, 47, 61, 75, 78, 92, 106, 120] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 8 2 ([2, 16, 30, 33, 47, 61, 75, 78, 92, 106, 120] : List (Fin 121)) (hcover 8 (by decide) hg 2)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 16 ∈ S → f11_point 92 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 16 ≠ f11_point 92) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → (f11_val S g).satisfies (([4, 18, 32, 35, 49, 63, 66, 80, 94, 108, 111] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 8 4 ([4, 18, 32, 35, 49, 63, 66, 80, 94, 108, 111] : List (Fin 121)) (hcover 8 (by decide) hg 4)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 99 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 99 ≠ f11_point 113) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 8 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 8 ≠ f11_point 11) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 39 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 39) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 53 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 53) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 56 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 56) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 98 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 98) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 101 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 101) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 8 → f11_point 11 ∈ S → f11_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 115) (hinj 8 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → (f11_val S g).satisfies (([9, 12, 26, 40, 54, 57, 71, 85, 88, 102, 116] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 8 9 ([9, 12, 26, 40, 54, 57, 71, 85, 88, 102, 116] : List (Fin 121)) (hcover 8 (by decide) hg 9)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 8 → (f11_val S g).satisfies (([10, 13, 27, 41, 44, 58, 72, 86, 89, 103, 117] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 8 10 ([10, 13, 27, 41, 44, 58, 72, 86, 89, 103, 117] : List (Fin 121)) (hcover 8 (by decide) hg 10)
    decide +revert
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 13 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 13) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 26) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 52 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 52) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 65 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 65) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 67 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 67) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 80 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 80) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 93 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 93) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 0 ∈ S → f11_point 106 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 106) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 14 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 14) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 27 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 27) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 40 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 40) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 55 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 55) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 81 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 81) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 94 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 94) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 107 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 107) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 1 ∈ S → f11_point 120 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 120) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → (f11_val S g).satisfies (([3, 16, 29, 42, 44, 57, 70, 83, 96, 109, 111] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 9 3 ([3, 16, 29, 42, 44, 57, 70, 83, 96, 109, 111] : List (Fin 121)) (hcover 9 (by decide) hg 3)
    decide +revert
    apply f11_sat_one
    change g 9 → (f11_val S g).satisfies (([4, 17, 30, 43, 45, 58, 71, 84, 97, 99, 112] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 9 4 ([4, 17, 30, 43, 45, 58, 71, 84, 97, 99, 112] : List (Fin 121)) (hcover 9 (by decide) hg 4)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 31 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 31 ≠ f11_point 113) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 6 ∈ S → f11_point 101 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 6 ≠ f11_point 101) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → (f11_val S g).satisfies (([7, 20, 22, 35, 48, 61, 74, 87, 89, 102, 115] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 9 7 ([7, 20, 22, 35, 48, 61, 74, 87, 89, 102, 115] : List (Fin 121)) (hcover 9 (by decide) hg 7)
    decide +revert
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 9 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 9 ≠ f11_point 11) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 50 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 50) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 63 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 63) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 76 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 76) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 78 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 78) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 91 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 91) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 104 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 104) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 9 → f11_point 11 ∈ S → f11_point 117 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 117) (hinj 9 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 9 → (f11_val S g).satisfies (([10, 12, 25, 38, 51, 64, 66, 79, 92, 105, 118] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 9 10 ([10, 12, 25, 38, 51, 64, 66, 79, 92, 105, 118] : List (Fin 121)) (hcover 9 (by decide) hg 10)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 12 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 12) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 24 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 24) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 36 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 36) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 48 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 48) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 72 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 72) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 84 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 84) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 108 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 108) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 0 ∈ S → f11_point 120 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 0 ≠ f11_point 120) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 13 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 13) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 37 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 37) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 49 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 49) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 61 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 61) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 73 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 73) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 85 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 85) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 97 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 97) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 109 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 109) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 1 ∈ S → f11_point 110 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 1 ≠ f11_point 110) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → (f11_val S g).satisfies (([3, 15, 27, 39, 51, 63, 75, 87, 88, 100, 112] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 10 3 ([3, 15, 27, 39, 51, 63, 75, 87, 88, 100, 112] : List (Fin 121)) (hcover 10 (by decide) hg 3)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → (f11_val S g).satisfies (([4, 16, 28, 40, 52, 64, 76, 77, 89, 101, 113] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 10 4 ([4, 16, 28, 40, 52, 64, 76, 77, 89, 101, 113] : List (Fin 121)) (hcover 10 (by decide) hg 4)
    decide +revert
    apply f11_sat_one
    change g 10 → f11_point 52 ∈ S → f11_point 113 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 52 ≠ f11_point 113) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 8 ∈ S → f11_point 33 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 8 ≠ f11_point 33) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 20 ∈ S → f11_point 57 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 20 ≠ f11_point 57) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → (f11_val S g).satisfies (([9, 21, 22, 34, 46, 58, 70, 82, 94, 106, 118] : List (Fin 121)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f11_sat_line S g 10 9 ([9, 21, 22, 34, 46, 58, 70, 82, 94, 106, 118] : List (Fin 121)) (hcover 10 (by decide) hg 9)
    decide +revert
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 10 ∈ S → f11_point 11 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 10 ≠ f11_point 11) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 23 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 23) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 35 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 35) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 59 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 59) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 71 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 71) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 83 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 83) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 95 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 95) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_and
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 107 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 107) (hinj 10 (by decide) hg hi hj (by decide))
    apply f11_sat_one
    change g 10 → f11_point 11 ∈ S → f11_point 119 ∈ S → False
    intro hg hi hj
    exact (by decide : f11_point 11 ≠ f11_point 119) (hinj 10 (by decide) hg hi hj (by decide))
  exact aftd_n11_sat_proof (f11_val S g) hF
