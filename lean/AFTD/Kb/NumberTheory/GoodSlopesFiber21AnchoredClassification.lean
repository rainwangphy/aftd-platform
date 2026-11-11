import AFTD.Prelude

/-!
# good_slopes_fiber21_anchored_classification

Topic: elementary_number_theory   Node: 1479c65e53ef

Provenance: helper lemma. Normalized classification of the 21-point fiber for OP-1027, tested in experiment 22086. The LRAT proof and interpretation are checked by Lean.

Let S be a set of points over the residues modulo 21 containing (0,0) and (1,20), and let g select directions among 4, 10, 13, 16 and 19. Suppose the six directions 2, 5, 8, 11, 17 and 20 are injective on S, the selected directions are injective and surjective on S, and every three distinct selectable directions include a selected one. Then 10, 13 and 19 are selected while 4 and 16 are not.
-/

set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
open Lean Elab Command in
elab "aftd_fiber21_lrat_core " cnf:term:max ppSpace lrat:term:max : command => do
  Command.liftTermElabM do
    let cnf ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat `aftd_fiber21_lrat
    addDecl <| Declaration.defnDecl {
      name := `aftd_fiber21_formula, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := `aftd_fiber21_sat_proof, levelParams := [], type := ← Meta.inferType proof, value := proof }
aftd_fiber21_lrat_core "p cnf 446 485\n1 0\n42 0\n-1 -79 0\n-1 -136 0\n-1 -193 0\n-1 -271 0\n-1 -328 0\n-1 -385 0\n-42 -99 0\n-42 -156 0\n-42 -213 0\n-42 -291 0\n-42 -348 0\n-42 -405 0\n-62 -311 0\n-176 -311 0\n-176 -425 0\n-44 -122 0\n-122 -236 0\n-122 -314 0\n-122 -371 0\n-179 -236 0\n-27 -105 0\n-47 -239 0\n-47 -296 0\n-50 -242 0\n-50 -434 0\n-107 -242 0\n-242 -299 0\n-242 -434 0\n-33 -168 0\n-53 -245 0\n-188 -245 0\n-188 -437 0\n-245 -437 0\n-16 -379 0\n-56 -362 0\n-170 -362 0\n-248 -362 0\n-305 -362 0\n-59 -308 0\n-173 -308 0\n-173 -422 0\n-251 -308 0\n-308 -365 0\n-1 -70 0\n-1 -139 0\n-1 -208 0\n-1 -256 0\n-1 -325 0\n-1 -394 0\n-56 -242 0\n-173 -311 0\n-242 -311 0\n-242 -359 0\n-242 -428 0\n-42 -90 0\n-42 -159 0\n-42 -228 0\n-42 -276 0\n-42 -345 0\n-42 -414 0\n-59 -176 0\n-59 -314 0\n-176 -245 0\n-176 -362 0\n-245 -362 0\n-314 -362 0\n-62 -179 0\n-62 -365 0\n-62 -434 0\n-179 -365 0\n-13 -316 0\n-30 -168 0\n-33 -357 0\n-50 -188 0\n-188 -422 0\n-36 -105 0\n-53 -239 0\n-122 -170 0\n-122 -308 0\n-122 -377 0\n-170 -308 0\n-308 -425 0\n-1 -82 0\n-1 -142 0\n-1 -202 0\n-1 -262 0\n-1 -382 0\n-50 -170 0\n-50 -371 0\n-4 -64 0\n-42 -102 0\n-42 -222 0\n-42 -282 0\n-42 -342 0\n-42 -402 0\n-56 -377 0\n-236 -377 0\n-296 -437 0\n-119 -440 0\n-62 -122 0\n-62 -242 0\n-62 -422 0\n-122 -242 0\n-122 -362 0\n-242 -362 0\n-242 -422 0\n-362 -422 0\n-30 -231 0\n-305 -365 0\n-47 -188 0\n-248 -308 0\n-1 -73 0\n-1 -145 0\n-1 -196 0\n-1 -268 0\n-1 -319 0\n-1 -391 0\n-33 -105 0\n-44 -311 0\n-188 -434 0\n-239 -311 0\n-311 -362 0\n-4 -127 0\n-36 -231 0\n-47 -242 0\n-119 -242 0\n-170 -242 0\n-242 -314 0\n-7 -253 0\n-39 -357 0\n-173 -440 0\n-10 -379 0\n-42 -93 0\n-42 -165 0\n-42 -216 0\n-42 -288 0\n-42 -339 0\n-42 -411 0\n-125 -422 0\n-299 -422 0\n-24 -168 0\n-56 -107 0\n-107 -179 0\n-27 -294 0\n-305 -377 0\n-377 -428 0\n-62 -113 0\n-62 -185 0\n-62 -236 0\n-62 -308 0\n-62 -431 0\n-236 -308 0\n-1 -76 0\n-1 -130 0\n-1 -205 0\n-1 -259 0\n-1 -334 0\n-1 -388 0\n-107 -365 0\n-236 -365 0\n-311 -440 0\n-365 -440 0\n-185 -422 0\n-239 -422 0\n-314 -368 0\n-7 -190 0\n-33 -420 0\n-59 -425 0\n-113 -242 0\n-188 -242 0\n-188 -296 0\n-242 -425 0\n-10 -64 0\n-62 -245 0\n-62 -299 0\n-62 -428 0\n-116 -170 0\n-44 -119 0\n-44 -173 0\n-42 -96 0\n-42 -150 0\n-42 -225 0\n-42 -279 0\n-42 -354 0\n-42 -408 0\n-47 -122 0\n-176 -251 0\n-176 -359 0\n-359 -434 0\n-50 -125 0\n-50 -362 0\n-233 -308 0\n-362 -437 0\n-1 -67 0\n-1 -133 0\n-1 -199 0\n-1 -265 0\n-1 -331 0\n-1 -397 0\n-47 -245 0\n-179 -422 0\n-50 -116 0\n-50 -248 0\n-116 -314 0\n-248 -314 0\n-314 -425 0\n-7 -316 0\n-30 -294 0\n-119 -362 0\n-10 -253 0\n-56 -365 0\n-122 -188 0\n-122 -365 0\n-13 -190 0\n-36 -168 0\n-170 -236 0\n-170 -368 0\n-170 -434 0\n-236 -434 0\n-368 -434 0\n-107 -305 0\n-239 -437 0\n-42 -87 0\n-42 -153 0\n-42 -219 0\n-42 -285 0\n-42 -351 0\n-42 -417 0\n-44 -176 0\n-44 -440 0\n-176 -242 0\n-176 -308 0\n-242 -308 0\n-308 -440 0\n-442 -1 -39 0\n-442 -1 -56 0\n-442 -1 -107 0\n-442 -1 -179 0\n-442 -1 -251 0\n-442 -1 -357 0\n-442 -1 -374 0\n-442 -1 -425 0\n-442 -4 -42 0\n-442 -42 -59 0\n-442 -42 -110 0\n-442 -42 -127 0\n-442 -42 -233 0\n-442 -42 -305 0\n-442 -42 -377 0\n-442 -42 -428 0\n-442 7 24 62 79 96 113 130 168 185 202 219 236 253 291 308 325 342 359 397 414 431 0\n-442 -7 -113 0\n-442 -62 -253 0\n-442 -113 -168 0\n-442 -168 -236 0\n-442 -168 -253 0\n-442 10 27 44 82 99 116 133 150 188 205 222 239 256 294 311 328 345 362 379 417 434 0\n-442 -10 -27 0\n-442 -10 -188 0\n-442 -10 -239 0\n-442 -10 -362 0\n-442 -27 -434 0\n-442 -188 -294 0\n-442 -311 -379 0\n-442 13 30 47 64 102 119 136 153 170 208 225 242 259 276 314 331 348 365 382 420 437 0\n-442 -30 -64 0\n-442 -30 -242 0\n-442 16 33 50 67 105 122 139 156 173 190 228 245 262 279 296 334 351 368 385 402 440 0\n-442 -33 -440 0\n-442 -105 -173 0\n-442 19 36 53 70 87 125 142 159 176 193 231 248 265 282 299 316 354 371 388 405 422 0\n-442 -36 -371 0\n-442 -231 -316 0\n-442 -316 -371 0\n-443 -1 -33 0\n-443 -1 -44 0\n-443 -1 -119 0\n-443 -1 -173 0\n-443 -1 -248 0\n-443 -1 -377 0\n-443 -1 -420 0\n-443 -1 -431 0\n-443 4 36 47 79 90 122 133 165 176 208 219 251 262 294 305 316 348 359 391 402 434 0\n-443 -36 -251 0\n-443 -36 -359 0\n-443 -251 -316 0\n-443 -294 -359 0\n-443 -316 -359 0\n-443 7 39 50 82 93 125 136 168 179 190 222 233 265 276 308 319 351 362 394 405 437 0\n-443 -7 -39 0\n-443 -7 -179 0\n-443 -7 -233 0\n-443 -125 -190 0\n-443 -168 -190 0\n-443 -168 -233 0\n-443 -190 -362 0\n-443 -10 -42 0\n-443 -42 -53 0\n-443 -42 -64 0\n-443 -42 -107 0\n-443 -42 -236 0\n-443 -42 -311 0\n-443 -42 -365 0\n-443 -42 -440 0\n-443 13 24 56 67 99 110 142 153 185 196 228 239 271 282 314 325 357 368 379 411 422 0\n-443 -13 -368 0\n-443 -13 -422 0\n-443 -24 -422 0\n-443 -379 -422 0\n-443 16 27 59 70 102 113 145 156 188 199 231 242 253 285 296 328 339 371 382 414 425 0\n-443 -16 -27 0\n-443 -16 -188 0\n-443 -27 -242 0\n-443 -27 -296 0\n-443 -242 -253 0\n-443 19 30 62 73 105 116 127 159 170 202 213 245 256 288 299 331 342 374 385 417 428 0\n-443 -19 -62 0\n-443 -30 -116 0\n-443 -62 -105 0\n-443 -62 -127 0\n-444 -1 -30 0\n-444 -1 -59 0\n-444 -1 -125 0\n-444 -1 -170 0\n-444 -1 -236 0\n-444 -1 -294 0\n-444 -1 -368 0\n-444 -1 -434 0\n-444 4 33 62 70 99 107 136 165 173 202 231 239 268 276 305 334 342 371 379 408 437 0\n-444 -4 -107 0\n-444 -33 -379 0\n-444 -379 -437 0\n-444 7 36 44 73 102 110 139 168 176 205 213 242 271 279 308 316 345 374 382 411 440 0\n-444 -7 -36 0\n-444 -7 -176 0\n-444 -7 -242 0\n-444 -7 -440 0\n-444 -36 -44 0\n-444 -36 -242 0\n-444 -36 -308 0\n-444 -44 -316 0\n-444 -168 -176 0\n-444 -168 -242 0\n-444 -168 -316 0\n-444 -168 -440 0\n-444 -242 -316 0\n-444 -308 -316 0\n-444 10 39 47 76 105 113 142 150 179 208 216 245 253 282 311 319 348 377 385 414 422 0\n-444 -10 -113 0\n-444 -10 -422 0\n-444 -39 -422 0\n-444 -47 -105 0\n-444 -13 -42 0\n-444 -42 -50 0\n-444 -42 -116 0\n-444 -42 -190 0\n-444 -42 -248 0\n-444 -42 -314 0\n-444 -42 -359 0\n-444 -42 -425 0\n-444 -16 -362 0\n-444 -127 -251 0\n-444 -362 -420 0\n-444 19 27 56 64 93 122 130 159 188 196 225 233 262 291 299 328 357 365 394 402 431 0\n-444 -19 -233 0\n-444 -27 -122 0\n-444 -122 -357 0\n-445 -1 -27 0\n-445 -1 -53 0\n-445 -1 -105 0\n-445 -1 -110 0\n-445 -1 -188 0\n-445 -1 -245 0\n-445 -1 -359 0\n-445 -1 -437 0\n-445 4 30 56 82 87 113 139 165 170 196 222 248 253 279 305 331 357 362 388 414 440 0\n-445 -4 -357 0\n-445 -4 -362 0\n-445 -30 -113 0\n-445 -30 -248 0\n-445 -30 -253 0\n-445 -30 -362 0\n-445 -305 -357 0\n-445 -357 -362 0\n-445 7 33 59 64 90 116 142 168 173 199 225 251 256 282 308 334 339 365 391 417 422 0\n-445 -7 -33 0\n-445 -7 -173 0\n-445 -7 -251 0\n-445 -7 -365 0\n-445 -7 -422 0\n-445 -33 -308 0\n-445 -168 -173 0\n-445 -168 -251 0\n-445 -168 -365 0\n-445 10 36 62 67 93 119 145 150 176 202 228 233 259 285 311 316 342 368 394 420 425 0\n-445 -10 -62 0\n-445 -36 -311 0\n-445 -36 -425 0\n-445 -311 -316 0\n-445 -316 -425 0\n-445 13 39 44 70 96 122 127 153 179 205 231 236 262 288 314 319 345 371 397 402 428 0\n-445 -13 -122 0\n-445 -39 -236 0\n-445 -16 -42 0\n-445 -42 -47 0\n-445 -42 -125 0\n-445 -42 -239 0\n-445 -42 -296 0\n-445 -42 -374 0\n-445 -42 -379 0\n-445 -42 -431 0\n-445 19 24 50 76 102 107 133 159 185 190 216 242 268 294 299 325 351 377 382 408 434 0\n-445 -19 -242 0\n-445 -50 -294 0\n-445 -190 -294 0\n-445 -190 -434 0\n-446 -1 -24 0\n-446 -1 -47 0\n-446 -1 -116 0\n-446 -1 -185 0\n-446 -1 -231 0\n-446 -1 -233 0\n-446 -1 -371 0\n-446 -1 -440 0\n-446 4 27 50 73 96 119 142 165 188 190 213 236 259 282 305 328 351 374 397 420 422 0\n-446 -27 -50 0\n-446 -27 -190 0\n-446 -27 -422 0\n-446 -188 -190 0\n-446 7 30 53 76 99 122 145 168 170 193 216 239 262 285 308 331 354 377 379 402 425 0\n-446 -7 -30 0\n-446 -7 -122 0\n-446 -7 -170 0\n-446 -7 -425 0\n-446 -30 -308 0\n-446 -53 -379 0\n-446 -122 -168 0\n-446 -168 -170 0\n-446 -168 -425 0\n-446 10 33 56 79 102 125 127 150 173 196 219 242 265 288 311 334 357 359 382 405 428 0\n-446 -10 -33 0\n-446 -10 -173 0\n-446 -33 -311 0\n-446 -127 -357 0\n-446 -173 -357 0\n-446 -242 -357 0\n-446 -357 -428 0\n-446 13 36 59 82 105 107 130 153 176 199 222 245 268 291 314 316 339 362 385 408 431 0\n-446 -13 -36 0\n-446 -13 -59 0\n-446 -13 -362 0\n-446 -36 -59 0\n-446 -36 -245 0\n-446 -36 -362 0\n-446 -59 -316 0\n-446 -105 -176 0\n-446 -105 -316 0\n-446 -105 -362 0\n-446 -245 -316 0\n-446 -316 -362 0\n-446 16 39 62 64 87 110 133 156 179 202 225 248 271 294 296 319 342 365 388 411 434 0\n-446 -39 -62 0\n-446 -39 -365 0\n-446 -62 -294 0\n-446 -19 -42 0\n-446 -42 -44 0\n-446 -42 -113 0\n-446 -42 -251 0\n-446 -42 -253 0\n-446 -42 -299 0\n-446 -42 -368 0\n-446 -42 -437 0\n442 443 444 0\n442 443 445 0\n442 443 446 0\n442 444 445 0\n442 444 446 0\n442 445 446 0\n443 444 445 0\n443 444 446 0\n443 445 446 0\n444 445 446 0\n-443 -444 -446 442 445 0\n" "486 -79 0 1 3 0\n487 -136 0 1 4 0\n488 -193 0 1 5 0\n489 -271 0 1 6 0\n490 -328 0 1 7 0\n491 -385 0 1 8 0\n492 -99 0 2 9 0\n493 -156 0 2 10 0\n494 -213 0 2 11 0\n495 -291 0 2 12 0\n496 -348 0 2 13 0\n497 -405 0 2 14 0\n498 -70 0 1 46 0\n499 -139 0 1 47 0\n500 -208 0 1 48 0\n501 -256 0 1 49 0\n502 -325 0 1 50 0\n503 -394 0 1 51 0\n504 -90 0 2 57 0\n505 -159 0 2 58 0\n506 -228 0 2 59 0\n507 -276 0 2 60 0\n508 -345 0 2 61 0\n509 -414 0 2 62 0\n510 -82 0 1 85 0\n511 -142 0 1 86 0\n512 -202 0 1 87 0\n513 -262 0 1 88 0\n514 -382 0 1 89 0\n515 -102 0 2 93 0\n516 -222 0 2 94 0\n517 -282 0 2 95 0\n518 -342 0 2 96 0\n519 -402 0 2 97 0\n520 -73 0 1 114 0\n521 -145 0 1 115 0\n522 -196 0 1 116 0\n523 -268 0 1 117 0\n524 -319 0 1 118 0\n525 -391 0 1 119 0\n526 -93 0 2 135 0\n527 -165 0 2 136 0\n528 -216 0 2 137 0\n529 -288 0 2 138 0\n530 -339 0 2 139 0\n531 -411 0 2 140 0\n532 -76 0 1 155 0\n533 -130 0 1 156 0\n534 -205 0 1 157 0\n535 -259 0 1 158 0\n536 -334 0 1 159 0\n537 -388 0 1 160 0\n538 -96 0 2 182 0\n539 -150 0 2 183 0\n540 -225 0 2 184 0\n541 -279 0 2 185 0\n542 -354 0 2 186 0\n543 -408 0 2 187 0\n544 -67 0 1 196 0\n545 -133 0 1 197 0\n546 -199 0 1 198 0\n547 -265 0 1 199 0\n548 -331 0 1 200 0\n549 -397 0 1 201 0\n550 -87 0 2 225 0\n551 -153 0 2 226 0\n552 -219 0 2 227 0\n553 -285 0 2 228 0\n554 -351 0 2 229 0\n555 -417 0 2 230 0\n556 -442 -39 0 1 237 0\n557 -442 -56 0 1 238 0\n558 -442 -107 0 1 239 0\n559 -442 -179 0 1 240 0\n560 -442 -251 0 1 241 0\n561 -442 -357 0 1 242 0\n562 -442 -374 0 1 243 0\n563 -442 -425 0 1 244 0\n564 -442 -4 0 2 245 0\n565 -442 -59 0 2 246 0\n566 -442 -110 0 2 247 0\n567 -442 -127 0 2 248 0\n568 -442 -233 0 2 249 0\n569 -442 -305 0 2 250 0\n570 -442 -377 0 2 251 0\n571 -442 -428 0 2 252 0\n572 -442 7 24 62 113 168 185 236 253 308 359 431 0 486 538 533 512 552 495 502 518 549 509 253 0\n573 -442 10 27 44 116 188 239 294 311 362 379 434 0 510 492 545 539 534 516 501 490 508 555 259 0\n574 -442 13 30 47 64 119 170 242 314 365 420 437 0 515 487 551 500 540 535 507 548 496 514 267 0\n575 -442 16 33 50 105 122 173 190 245 296 368 440 0 544 499 493 506 513 541 536 554 491 519 270 0\n576 -442 19 36 53 125 176 231 248 299 316 371 422 0 498 550 511 505 488 547 517 542 537 497 273 0\n577 -443 -33 0 1 277 0\n578 -443 -44 0 1 278 0\n579 -443 -119 0 1 279 0\n580 -443 -173 0 1 280 0\n581 -443 -248 0 1 281 0\n582 -443 -377 0 1 282 0\n583 -443 -420 0 1 283 0\n584 -443 -431 0 1 284 0\n585 -443 4 36 47 122 176 251 294 305 316 359 434 0 486 504 545 527 500 552 513 496 525 519 285 0\n586 -443 7 39 50 125 168 179 190 233 308 362 437 0 510 526 487 516 547 507 524 554 503 497 291 0\n587 -443 -10 0 2 299 0\n588 -443 -53 0 2 300 0\n589 -443 -64 0 2 301 0\n590 -443 -107 0 2 302 0\n591 -443 -236 0 2 303 0\n592 -443 -311 0 2 304 0\n593 -443 -365 0 2 305 0\n594 -443 -440 0 2 306 0\n595 -443 13 24 56 110 185 239 314 357 368 379 422 0 544 492 511 551 522 506 489 517 502 531 307 0\n596 -443 16 27 59 113 188 231 242 253 296 371 425 0 498 515 521 493 546 553 490 530 514 509 312 0\n597 -443 19 30 62 105 116 127 170 245 299 374 428 0 520 505 512 494 501 529 548 518 491 555 318 0\n598 -444 -30 0 1 323 0\n599 -444 -59 0 1 324 0\n600 -444 -125 0 1 325 0\n601 -444 -170 0 1 326 0\n602 -444 -236 0 1 327 0\n603 -444 -294 0 1 328 0\n604 -444 -368 0 1 329 0\n605 -444 -434 0 1 330 0\n606 -444 4 33 62 107 173 231 239 305 371 379 437 0 498 492 487 527 512 523 507 536 518 543 331 0\n607 -444 7 36 44 110 168 176 242 308 316 374 440 0 520 515 499 534 494 489 541 508 514 531 335 0\n608 -444 10 39 47 105 113 179 245 253 311 377 422 0 532 511 539 500 528 517 524 496 491 509 350 0\n609 -444 -13 0 2 355 0\n610 -444 -50 0 2 356 0\n611 -444 -116 0 2 357 0\n612 -444 -190 0 2 358 0\n613 -444 -248 0 2 359 0\n614 -444 -314 0 2 360 0\n615 -444 -359 0 2 361 0\n616 -444 -425 0 2 362 0\n617 -444 19 27 56 64 122 188 233 299 357 365 431 0 526 533 505 522 540 513 495 490 503 519 366 0\n618 -445 -27 0 1 370 0\n619 -445 -53 0 1 371 0\n620 -445 -105 0 1 372 0\n621 -445 -110 0 1 373 0\n622 -445 -188 0 1 374 0\n623 -445 -245 0 1 375 0\n624 -445 -359 0 1 376 0\n625 -445 -437 0 1 377 0\n626 -445 4 30 56 113 170 248 253 305 357 362 440 0 510 550 499 527 522 516 541 548 537 509 378 0\n627 -445 7 33 59 64 116 168 173 251 308 365 422 0 504 511 546 540 501 517 536 530 525 555 387 0\n628 -445 10 36 62 119 176 233 311 316 368 420 425 0 544 526 521 539 512 506 535 553 518 503 397 0\n629 -445 13 39 44 122 127 179 231 236 314 371 428 0 498 538 551 534 513 529 524 508 549 519 403 0\n630 -445 -16 0 2 406 0\n631 -445 -47 0 2 407 0\n632 -445 -125 0 2 408 0\n633 -445 -239 0 2 409 0\n634 -445 -296 0 2 410 0\n635 -445 -374 0 2 411 0\n636 -445 -379 0 2 412 0\n637 -445 -431 0 2 413 0\n638 -445 19 24 50 107 185 190 242 294 299 377 434 0 532 515 545 505 528 523 502 554 514 543 414 0\n639 -446 -24 0 1 419 0\n640 -446 -47 0 1 420 0\n641 -446 -116 0 1 421 0\n642 -446 -185 0 1 422 0\n643 -446 -231 0 1 423 0\n644 -446 -233 0 1 424 0\n645 -446 -371 0 1 425 0\n646 -446 -440 0 1 426 0\n647 -446 4 27 50 119 188 190 236 305 374 420 422 0 520 538 511 527 494 535 517 490 554 549 427 0\n648 -446 7 30 53 122 168 170 239 308 377 379 425 0 532 492 521 488 528 513 553 548 542 519 432 0\n649 -446 10 33 56 125 127 173 242 311 357 359 428 0 486 515 539 522 552 547 529 536 514 497 442 0\n650 -446 13 36 59 105 107 176 245 314 316 362 431 0 510 533 551 546 516 523 495 530 491 543 450 0\n651 -446 16 39 62 64 110 179 248 294 296 365 434 0 550 545 493 512 540 489 524 518 537 531 463 0\n652 -446 -19 0 2 467 0\n653 -446 -44 0 2 468 0\n654 -446 -113 0 2 469 0\n655 -446 -251 0 2 470 0\n656 -446 -253 0 2 471 0\n657 -446 -299 0 2 472 0\n658 -446 -368 0 2 473 0\n659 -446 -437 0 2 474 0\n660 -242 -444 -445 -446 0 614 609 599 637 623 620 28 107 233 348 341 650 0\n661 -377 362 357 365 -444 -445 -446 0 613 601 598 637 622 618 657 656 654 652 646 644 82 98 147 617 626 92 0\n662 362 357 365 -444 -445 -446 0 660 613 612 610 605 603 601 598 657 656 654 652 646 642 639 661 638 144 223 332 626 0\n663 -362 -444 -445 -446 0 612 610 602 635 622 618 40 109 211 365 380 647 0\n664 -357 -444 -445 -446 0 614 609 602 636 633 659 653 645 643 75 132 449 379 446 447 385 369 629 69 145 606 0\n665 -444 -445 -446 0 657 656 654 653 652 646 645 643 642 639 598 601 602 603 605 609 610 612 613 614 660 663 664 662 72 111 161 213 215 465 626 638 125 148 629 0\n666 -365 -445 -446 0 665 637 624 656 654 642 639 45 70 162 593 391 396 475 572 0\n667 -7 -442 362 -445 -446 0 569 564 561 557 634 630 623 620 658 656 654 646 168 389 434 435 433 388 626 575 205 0\n668 -168 -442 236 362 -445 -446 0 571 569 567 564 561 559 557 556 634 630 623 620 658 656 654 653 646 645 643 31 74 394 440 439 626 205 207 575 629 216 0\n669 -442 62 236 362 -445 -446 0 637 624 656 654 646 642 639 557 561 564 569 667 668 572 83 113 437 626 0\n670 -308 -443 -445 -446 0 634 630 622 618 656 654 645 643 41 84 235 596 0\n671 59 242 -443 362 -445 -446 0 670 590 589 580 577 666 637 634 630 623 622 620 618 656 655 654 645 643 641 596 17 208 402 436 441 400 650 627 309 0\n672 -59 311 10 420 119 62 -445 -446 0 658 644 63 170 457 454 628 0\n673 62 236 362 -445 -446 0 665 636 633 621 658 644 642 639 669 475 579 583 587 592 672 671 52 108 130 174 233 448 595 73 451 628 0\n674 236 362 -445 -446 0 665 636 633 622 618 653 645 643 641 673 15 69 71 102 103 178 466 464 398 573 475 322 671 64 452 629 0\n675 362 -445 -446 0 666 665 636 634 633 630 621 619 674 19 22 99 151 154 218 221 591 405 475 563 667 257 648 210 268 382 651 0\n676 -445 -446 0 658 657 652 645 643 642 639 619 621 632 633 636 665 675 37 39 66 68 109 462 453 456 386 576 595 475 0\n677 -362 443 -446 0 676 476 570 559 556 481 656 654 640 67 109 124 460 263 608 0\n678 -105 10 311 422 443 -446 0 676 481 615 613 600 476 571 569 567 564 561 558 557 659 657 652 645 643 78 120 272 458 459 649 576 103 79 438 606 0\n679 -245 422 443 -446 0 676 481 613 600 476 657 652 645 643 32 65 461 455 576 0\n680 10 311 422 443 -446 0 679 676 476 570 559 556 481 656 654 640 678 608 0\n681 -10 443 -446 0 676 476 569 564 561 558 557 481 659 657 652 645 644 643 134 175 260 261 262 444 443 606 70 102 153 617 0\n682 -311 443 -446 0 676 476 569 564 558 481 659 645 643 15 53 123 266 445 606 0\n683 443 -446 0 676 653 641 476 481 557 561 567 571 600 603 605 615 677 681 682 680 43 77 108 166 430 649 573 333 0\n684 -444 -446 0 683 593 589 584 583 579 676 659 657 652 644 640 598 601 609 614 485 557 561 574 105 172 315 617 0\n685 -242 27 188 -446 0 676 684 478 569 564 562 683 591 584 583 579 656 654 642 639 26 55 103 108 235 647 168 296 572 0\n686 -125 422 27 188 -446 0 676 684 478 569 564 562 683 591 583 579 192 295 647 0\n687 422 27 188 -446 0 685 676 684 478 571 567 561 557 683 592 588 587 581 580 577 657 652 645 643 686 649 190 290 287 576 0\n688 27 188 -446 0 676 684 478 571 567 561 557 683 592 587 580 577 653 641 685 687 109 141 166 311 649 191 289 573 0\n689 -27 -446 0 676 684 478 566 559 556 683 593 589 581 580 577 658 646 23 146 264 316 428 429 313 651 102 176 575 0\n690 -446 0 646 658 676 683 577 580 581 589 593 684 478 556 559 566 689 688 33 76 122 173 214 265 431 314 575 651 321 0\n691 -188 -443 0 690 593 589 583 579 34 112 172 622 480 484 598 601 609 614 574 0\n692 -47 -444 -442 -443 0 612 611 610 605 604 603 691 594 592 587 580 578 577 24 25 188 202 354 575 36 313 363 573 0\n693 -444 242 -442 -443 0 691 594 593 592 589 587 583 580 579 578 577 598 601 603 604 605 609 610 611 612 614 692 574 35 100 195 224 334 573 23 368 313 575 0\n694 -30 242 -442 -443 0 690 693 484 636 634 633 630 623 620 618 565 563 691 594 592 587 580 578 577 110 210 320 381 383 384 596 573 21 91 222 418 575 0\n695 -170 -445 -442 -443 0 636 634 633 630 623 620 618 691 594 592 587 580 578 577 38 80 90 179 219 220 575 573 417 0\n696 -50 -445 -442 -443 0 636 633 618 691 592 587 578 27 193 204 416 573 0\n697 -368 242 -442 -443 0 690 693 484 695 694 631 625 593 589 583 579 167 308 574 0\n698 -122 242 -442 -443 0 690 693 484 695 694 631 625 593 589 583 579 20 404 574 0\n699 242 -442 -443 0 690 691 594 593 592 589 587 583 580 579 578 577 693 484 618 620 623 625 630 631 633 634 636 694 695 696 697 698 575 216 298 574 206 417 573 418 0\n700 -442 -443 0 690 594 581 557 560 561 564 569 699 30 55 105 107 127 129 171 233 317 269 626 484 603 348 341 585 0\n701 -242 -443 0 690 700 479 611 601 599 598 480 635 623 620 593 589 580 577 29 56 103 108 235 415 338 345 597 627 364 0\n702 -251 -443 0 690 701 700 480 635 621 479 594 578 44 189 288 395 286 390 607 0\n703 7 168 308 -443 0 690 702 701 700 479 612 611 610 605 603 599 480 632 625 593 590 589 582 580 577 627 109 142 165 203 310 353 638 586 367 0\n704 -7 -443 0 690 700 479 616 604 480 631 623 620 592 587 583 582 579 131 209 293 294 337 392 336 292 628 608 149 0\n705 -168 -443 0 690 701 700 479 616 612 610 605 604 603 480 592 590 587 583 582 579 143 217 297 344 346 628 150 177 319 638 0\n706 -443 0 690 579 583 587 592 700 480 479 604 616 704 705 703 152 194 234 349 342 628 0\n707 442 0 706 690 477 0\n708 444 0 706 690 482 0\n709 445 0 706 690 483 0\n710 -39 0 707 556 0\n711 -56 0 707 557 0\n712 -179 0 707 559 0\n713 -251 0 707 560 0\n714 -357 0 707 561 0\n715 -374 0 707 562 0\n716 -425 0 707 563 0\n717 -4 0 707 564 0\n718 -59 0 707 565 0\n719 -110 0 707 566 0\n720 -127 0 707 567 0\n721 -233 0 707 568 0\n722 -305 0 707 569 0\n723 -377 0 707 570 0\n724 -428 0 707 571 0\n725 -30 0 708 598 0\n726 -170 0 708 601 0\n727 -236 0 708 602 0\n728 -294 0 708 603 0\n729 -368 0 708 604 0\n730 -434 0 708 605 0\n731 -13 0 708 609 0\n732 -50 0 708 610 0\n733 -116 0 708 611 0\n734 -190 0 708 612 0\n735 -248 0 708 613 0\n736 -314 0 708 614 0\n737 -27 0 709 618 0\n738 -105 0 709 620 0\n739 -188 0 709 622 0\n740 -245 0 709 623 0\n741 -16 0 709 630 0\n742 -47 0 709 631 0\n743 -239 0 709 633 0\n744 -296 0 709 634 0\n745 -379 0 709 636 0\n746 -308 0 709 740 741 734 707 729 744 732 738 42 81 236 393 575 0\n747 -10 7 168 0 708 725 711 717 726 722 714 735 707 713 718 746 733 709 175 212 263 351 352 626 133 164 271 627 0\n748 -311 36 176 316 7 168 0 715 708 719 746 54 121 163 607 0\n749 -119 36 176 316 7 168 0 715 708 719 746 101 128 180 607 0\n750 -420 311 10 0 708 733 739 737 728 730 745 743 740 741 734 707 729 744 732 738 169 365 573 18 181 232 575 0\n751 420 311 36 10 176 316 119 0 740 723 712 710 708 742 738 707 716 729 709 721 628 104 149 255 608 0\n752 36 176 316 7 168 0 747 748 749 750 751 0\n753 -36 10 0 708 709 720 727 712 731 724 736 710 733 739 737 728 730 745 743 707 126 274 340 399 629 573 106 0\n754 -176 10 0 733 739 737 728 730 745 743 707 16 66 231 573 0\n755 7 168 0 707 743 745 730 728 737 739 733 710 736 724 731 712 727 720 709 708 747 753 754 752 275 276 401 343 629 573 106 0\n756 -7 0 708 725 711 717 726 709 722 714 735 740 741 734 707 729 744 732 738 131 254 339 389 388 626 575 106 0\n757 168 0 756 755 0\n758 -33 0 757 31 0\n759 -253 0 757 707 258 0\n760 -440 0 757 708 347 0\n761 -173 0 757 709 394 0\n762 -113 0 757 707 256 0\n763 122 0 760 738 758 732 744 729 761 707 734 741 740 575 0\n764 362 0 762 735 714 722 709 726 717 759 711 725 760 626 0\n765  0 763 764 106 0\n"



set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

private def f21_row : Finset (ZMod 21) := {2,5,8,11,17,20}
private def f21_opt : Finset (ZMod 21) := {4,10,13,16,19}
private def f21_point (i : Nat) : ZMod 21 × ZMod 21 := (((i / 21 : Nat) : ZMod 21), ((i % 21 : Nat) : ZMod 21))
private def f21_form (a : ZMod 21) (p : ZMod 21 × ZMod 21) : ZMod 21 := p.2 + a * p.1
private def f21_flag (i : Nat) : ZMod 21 := if i = 441 then 4 else if i = 442 then 10 else if i = 443 then 13 else if i = 444 then 16 else if i = 445 then 19 else 0
private def f21_val (S : Finset (ZMod 21 × ZMod 21)) (g : ZMod 21 → Prop) : Sat.Valuation := fun i => if i < 441 then f21_point i ∈ S else g (f21_flag i)

private theorem f21_sat_and {v : Sat.Valuation} {f g : Sat.Fmla} (hf : v.satisfies_fmla f) (hg : v.satisfies_fmla g) : v.satisfies_fmla (f.and g) := by
  refine ⟨?_⟩
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hf.prop c h
  · exact hg.prop c h

private theorem f21_sat_one {v : Sat.Valuation} {c : Sat.Clause} (h : v.satisfies c) : v.satisfies_fmla (Sat.Fmla.one c) := by
  refine ⟨?_⟩
  intro c' hc'
  have hc : c' = c := List.mem_singleton.mp hc'
  simpa only [hc] using h

private theorem f21_sat_positive_mem (v : Sat.Valuation) (L : Sat.Clause) (i : Nat)
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

private theorem f21_sat_line (S : Finset (ZMod 21 × ZMod 21)) (g : ZMod 21 → Prop)
    (a t : ZMod 21) (L : List (Fin 441))
    (hcover : ∃ p ∈ S, f21_form a p = t)
    (hidx : ∀ p : ZMod 21 × ZMod 21, f21_form a p = t → p ∈ L.map (fun i => f21_point i.val)) :
    (f21_val S g).satisfies (L.map fun i => Sat.Literal.pos i.val) := by
  obtain ⟨p,hp,hpform⟩ := hcover
  obtain ⟨i,hi,hip⟩ := List.mem_map.mp (hidx p hpform)
  apply f21_sat_positive_mem (f21_val S g) (L.map fun i => Sat.Literal.pos i.val) i.val
  · exact List.mem_map.mpr ⟨i,hi,rfl⟩
  · simp only [f21_val, i.isLt, if_true, hip]
    exact hp

theorem good_slopes_fiber21_anchored_classification (S : Finset (ZMod 21 × ZMod 21)) (g : ZMod 21 → Prop)
  (h0 : (0,0) ∈ S) (h1 : (1,20) ∈ S)
  (hrow : ∀ a ∈ ({2,5,8,11,17,20} : Finset (ZMod 21)), Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + a*p.1) S)
  (hinj : ∀ a ∈ ({4,10,13,16,19} : Finset (ZMod 21)), g a → Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + a*p.1) S)
  (hcover : ∀ a ∈ ({4,10,13,16,19} : Finset (ZMod 21)), g a → ∀ t : ZMod 21, ∃ p ∈ S, p.2 + a*p.1 = t)
  (hthree : ∀ a b c, a ∈ ({4,10,13,16,19} : Finset (ZMod 21)) → b ∈ ({4,10,13,16,19} : Finset (ZMod 21)) → c ∈ ({4,10,13,16,19} : Finset (ZMod 21)) → a ≠ b → a ≠ c → b ≠ c → g a ∨ g b ∨ g c)
  (hnot : ¬ g 10 ∨ ¬ g 13 ∨ ¬ g 19 ∨ g 4 ∨ g 16) : False := by
  change ∀ a ∈ f21_row, Set.InjOn (f21_form a) S at hrow
  change ∀ a ∈ f21_opt, g a → Set.InjOn (f21_form a) S at hinj
  change ∀ a ∈ f21_opt, g a → ∀ t : ZMod 21, ∃ p ∈ S, f21_form a p = t at hcover
  change ∀ a b c, a ∈ f21_opt → b ∈ f21_opt → c ∈ f21_opt → a ≠ b → a ≠ c → b ≠ c → g a ∨ g b ∨ g c at hthree
  have hF : (f21_val S g).satisfies_fmla aftd_fiber21_formula := by
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change (¬ f21_point 0 ∈ S) → False
    intro h
    apply h
    simpa [f21_point] using h0
    apply f21_sat_and
    apply f21_sat_one
    change (¬ f21_point 41 ∈ S) → False
    intro h
    apply h
    simpa [f21_point] using h1
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 78 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 78) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 135 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 135) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 192 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 192) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 270 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 270) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 327 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 327) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 384 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 384) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 98 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 98) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 155 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 155) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 212 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 212) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 290 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 290) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 347 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 347) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 404 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 404) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 310) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 310) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 424 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 424) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 121 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 121) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 235 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 235) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 313 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 313) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 370 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 370) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 178 ∈ S → f21_point 235 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 178 ≠ f21_point 235) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 26 ∈ S → f21_point 104 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 26 ≠ f21_point 104) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 238 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 238) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 295 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 295) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 241) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 433) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 106 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 106 ≠ f21_point 241) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 298 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 298) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 433) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 32 ∈ S → f21_point 167 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 32 ≠ f21_point 167) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 52 ∈ S → f21_point 244 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 52 ≠ f21_point 244) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 244 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 244) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 436 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 436) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 244 ∈ S → f21_point 436 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 244 ≠ f21_point 436) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 15 ∈ S → f21_point 378 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 15 ≠ f21_point 378) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 55 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 55 ≠ f21_point 361) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 361) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 247 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 247 ≠ f21_point 361) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 304 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 304 ≠ f21_point 361) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 58 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 58 ≠ f21_point 307) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 172 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 172 ≠ f21_point 307) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 172 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 172 ≠ f21_point 421) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 250 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 250 ≠ f21_point 307) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 307 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 307 ≠ f21_point 364) (hrow 2 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 69 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 69) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 138 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 138) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 207 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 207) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 255 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 255) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 324 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 324) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 393 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 393) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 55 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 55 ≠ f21_point 241) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 172 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 172 ≠ f21_point 310) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 310) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 358 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 358) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 427 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 427) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 89 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 89) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 158 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 158) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 227 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 227) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 275 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 275) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 344 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 344) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 413 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 413) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 58 ∈ S → f21_point 175 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 58 ≠ f21_point 175) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 58 ∈ S → f21_point 313 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 58 ≠ f21_point 313) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 244 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 244) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 361) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 244 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 244 ≠ f21_point 361) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 313 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 313 ≠ f21_point 361) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 178 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 178) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 364) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 433) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 178 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 178 ≠ f21_point 364) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 12 ∈ S → f21_point 315 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 12 ≠ f21_point 315) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 29 ∈ S → f21_point 167 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 29 ≠ f21_point 167) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 32 ∈ S → f21_point 356 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 32 ≠ f21_point 356) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 187 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 187) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 421) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 35 ∈ S → f21_point 104 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 35 ≠ f21_point 104) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 52 ∈ S → f21_point 238 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 52 ≠ f21_point 238) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 169 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 169) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 307) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 376 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 376) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 307) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 307 ∈ S → f21_point 424 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 307 ≠ f21_point 424) (hrow 5 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 81 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 81) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 141 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 141) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 201 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 201) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 261 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 261) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 381 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 381) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 169 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 169) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 370 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 370) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 3 ∈ S → f21_point 63 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 3 ≠ f21_point 63) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 101 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 101) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 221 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 221) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 281 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 281) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 341 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 341) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 401 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 401) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 55 ∈ S → f21_point 376 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 55 ≠ f21_point 376) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 235 ∈ S → f21_point 376 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 235 ≠ f21_point 376) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 295 ∈ S → f21_point 436 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 295 ≠ f21_point 436) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 118 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 118 ≠ f21_point 439) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 121 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 121) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 241) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 421) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 241) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 361) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 361) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 421) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 361 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 361 ≠ f21_point 421) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 29 ∈ S → f21_point 230 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 29 ≠ f21_point 230) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 304 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 304 ≠ f21_point 364) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 187 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 187) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 247 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 247 ≠ f21_point 307) (hrow 8 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 72 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 72) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 144 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 144) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 195 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 195) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 267 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 267) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 318 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 318) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 390 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 390) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 32 ∈ S → f21_point 104 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 32 ≠ f21_point 104) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 310) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 433) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 238 ∈ S → f21_point 310 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 238 ≠ f21_point 310) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 310 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 310 ≠ f21_point 361) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 3 ∈ S → f21_point 126 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 3 ≠ f21_point 126) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 35 ∈ S → f21_point 230 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 35 ≠ f21_point 230) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 241) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 118 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 118 ≠ f21_point 241) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 241) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 313 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 313) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 6 ∈ S → f21_point 252 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 6 ≠ f21_point 252) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 38 ∈ S → f21_point 356 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 38 ≠ f21_point 356) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 172 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 172 ≠ f21_point 439) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 9 ∈ S → f21_point 378 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 9 ≠ f21_point 378) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 92 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 92) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 164 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 164) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 215 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 215) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 287 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 287) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 338 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 338) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 410 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 410) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 124 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 124 ≠ f21_point 421) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 298 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 298 ≠ f21_point 421) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 23 ∈ S → f21_point 167 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 23 ≠ f21_point 167) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 55 ∈ S → f21_point 106 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 55 ≠ f21_point 106) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 106 ∈ S → f21_point 178 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 106 ≠ f21_point 178) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 26 ∈ S → f21_point 293 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 26 ≠ f21_point 293) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 304 ∈ S → f21_point 376 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 304 ≠ f21_point 376) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 376 ∈ S → f21_point 427 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 376 ≠ f21_point 427) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 112 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 112) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 184 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 184) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 235 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 235) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 307) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 430 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 430) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 235 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 235 ≠ f21_point 307) (hrow 11 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 75 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 75) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 129 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 129) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 204 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 204) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 258 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 258) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 333 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 333) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 387 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 387) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 106 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 106 ≠ f21_point 364) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 235 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 235 ≠ f21_point 364) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 310 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 310 ≠ f21_point 439) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 364 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 364 ≠ f21_point 439) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 184 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 184 ≠ f21_point 421) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 238 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 238 ≠ f21_point 421) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 313 ∈ S → f21_point 367 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 313 ≠ f21_point 367) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 6 ∈ S → f21_point 189 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 6 ≠ f21_point 189) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 32 ∈ S → f21_point 419 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 32 ≠ f21_point 419) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 58 ∈ S → f21_point 424 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 58 ≠ f21_point 424) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 112 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 112 ≠ f21_point 241) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 241) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 187 ∈ S → f21_point 295 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 187 ≠ f21_point 295) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 424 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 424) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 9 ∈ S → f21_point 63 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 9 ≠ f21_point 63) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 244 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 244) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 298 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 298) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 61 ∈ S → f21_point 427 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 61 ≠ f21_point 427) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 115 ∈ S → f21_point 169 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 115 ≠ f21_point 169) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 118 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 118) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 172 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 172) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 95 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 95) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 149 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 149) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 224 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 224) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 278 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 278) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 353 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 353) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 407 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 407) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 121 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 121) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 250 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 250) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 358 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 358) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 358 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 358 ≠ f21_point 433) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 124 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 124) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 361) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 232 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 232 ≠ f21_point 307) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 361 ∈ S → f21_point 436 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 361 ≠ f21_point 436) (hrow 17 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 66 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 66) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 132 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 132) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 198 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 198) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 264 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 264) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 330 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 330) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 0 ∈ S → f21_point 396 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 0 ≠ f21_point 396) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 46 ∈ S → f21_point 244 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 46 ≠ f21_point 244) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 178 ∈ S → f21_point 421 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 178 ≠ f21_point 421) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 115 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 115) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 49 ∈ S → f21_point 247 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 49 ≠ f21_point 247) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 115 ∈ S → f21_point 313 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 115 ≠ f21_point 313) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 247 ∈ S → f21_point 313 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 247 ≠ f21_point 313) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 313 ∈ S → f21_point 424 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 313 ≠ f21_point 424) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 6 ∈ S → f21_point 315 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 6 ≠ f21_point 315) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 29 ∈ S → f21_point 293 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 29 ≠ f21_point 293) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 118 ∈ S → f21_point 361 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 118 ≠ f21_point 361) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 9 ∈ S → f21_point 252 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 9 ≠ f21_point 252) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 55 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 55 ≠ f21_point 364) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 187 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 187) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 121 ∈ S → f21_point 364 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 121 ≠ f21_point 364) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 12 ∈ S → f21_point 189 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 12 ≠ f21_point 189) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 35 ∈ S → f21_point 167 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 35 ≠ f21_point 167) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 235 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 235) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 367 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 367) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 169 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 169 ≠ f21_point 433) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 235 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 235 ≠ f21_point 433) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 367 ∈ S → f21_point 433 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 367 ≠ f21_point 433) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 106 ∈ S → f21_point 304 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 106 ≠ f21_point 304) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 238 ∈ S → f21_point 436 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 238 ≠ f21_point 436) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 86 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 86) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 152 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 152) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 218 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 218) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 284 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 284) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 350 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 350) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 41 ∈ S → f21_point 416 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 41 ≠ f21_point 416) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 175 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 175) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 43 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 43 ≠ f21_point 439) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 241 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 241) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 175 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 175 ≠ f21_point 307) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change f21_point 241 ∈ S → f21_point 307 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 241 ≠ f21_point 307) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_one
    change f21_point 307 ∈ S → f21_point 439 ∈ S → False
    intro hi hj
    exact (by decide : f21_point 307 ≠ f21_point 439) (hrow 20 (by decide) hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 38 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 38) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 55 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 55) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 106 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 106) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 178 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 178) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 250) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 356) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 373 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 373) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 0 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 424) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 3 ∈ S → f21_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 3 ≠ f21_point 41) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 58) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 109 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 109) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 126 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 126) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 232 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 232) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 304 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 304) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 376 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 376) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 41 ∈ S → f21_point 427 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 427) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → (f21_val S g).satisfies (([6, 23, 61, 78, 95, 112, 129, 167, 184, 201, 218, 235, 252, 290, 307, 324, 341, 358, 396, 413, 430] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 4 6 ([6, 23, 61, 78, 95, 112, 129, 167, 184, 201, 218, 235, 252, 290, 307, 324, 341, 358, 396, 413, 430] : List (Fin 441)) (hcover 4 (by decide) hg 6)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 6 ∈ S → f21_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 112) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 61 ∈ S → f21_point 252 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 61 ≠ f21_point 252) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 112 ∈ S → f21_point 167 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 112 ≠ f21_point 167) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 167 ∈ S → f21_point 235 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 235) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 167 ∈ S → f21_point 252 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 252) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → (f21_val S g).satisfies (([9, 26, 43, 81, 98, 115, 132, 149, 187, 204, 221, 238, 255, 293, 310, 327, 344, 361, 378, 416, 433] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 4 9 ([9, 26, 43, 81, 98, 115, 132, 149, 187, 204, 221, 238, 255, 293, 310, 327, 344, 361, 378, 416, 433] : List (Fin 441)) (hcover 4 (by decide) hg 9)
    decide
    apply f21_sat_one
    change g 4 → f21_point 9 ∈ S → f21_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 26) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 9 ∈ S → f21_point 187 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 187) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 9 ∈ S → f21_point 238 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 238) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 9 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 361) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 26 ∈ S → f21_point 433 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 433) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 187 ∈ S → f21_point 293 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 187 ≠ f21_point 293) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 310 ∈ S → f21_point 378 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 310 ≠ f21_point 378) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → (f21_val S g).satisfies (([12, 29, 46, 63, 101, 118, 135, 152, 169, 207, 224, 241, 258, 275, 313, 330, 347, 364, 381, 419, 436] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 4 12 ([12, 29, 46, 63, 101, 118, 135, 152, 169, 207, 224, 241, 258, 275, 313, 330, 347, 364, 381, 419, 436] : List (Fin 441)) (hcover 4 (by decide) hg 12)
    decide
    apply f21_sat_one
    change g 4 → f21_point 29 ∈ S → f21_point 63 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 63) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 29 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 241) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → (f21_val S g).satisfies (([15, 32, 49, 66, 104, 121, 138, 155, 172, 189, 227, 244, 261, 278, 295, 333, 350, 367, 384, 401, 439] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 4 15 ([15, 32, 49, 66, 104, 121, 138, 155, 172, 189, 227, 244, 261, 278, 295, 333, 350, 367, 384, 401, 439] : List (Fin 441)) (hcover 4 (by decide) hg 15)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 32 ∈ S → f21_point 439 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 32 ≠ f21_point 439) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 104 ∈ S → f21_point 172 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 104 ≠ f21_point 172) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → (f21_val S g).satisfies (([18, 35, 52, 69, 86, 124, 141, 158, 175, 192, 230, 247, 264, 281, 298, 315, 353, 370, 387, 404, 421] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 4 18 ([18, 35, 52, 69, 86, 124, 141, 158, 175, 192, 230, 247, 264, 281, 298, 315, 353, 370, 387, 404, 421] : List (Fin 441)) (hcover 4 (by decide) hg 18)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 35 ∈ S → f21_point 370 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 370) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 4 → f21_point 230 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 230 ≠ f21_point 315) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 4 → f21_point 315 ∈ S → f21_point 370 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 315 ≠ f21_point 370) (hinj 4 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 32 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 32) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 43 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 43) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 118 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 118) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 172 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 172) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 247 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 247) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 376 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 376) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 419 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 419) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 0 ∈ S → f21_point 430 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 430) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → (f21_val S g).satisfies (([3, 35, 46, 78, 89, 121, 132, 164, 175, 207, 218, 250, 261, 293, 304, 315, 347, 358, 390, 401, 433] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 10 3 ([3, 35, 46, 78, 89, 121, 132, 164, 175, 207, 218, 250, 261, 293, 304, 315, 347, 358, 390, 401, 433] : List (Fin 441)) (hcover 10 (by decide) hg 3)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 35 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 250) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 35 ∈ S → f21_point 358 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 358) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 250 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 250 ≠ f21_point 315) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 293 ∈ S → f21_point 358 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 293 ≠ f21_point 358) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 315 ∈ S → f21_point 358 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 315 ≠ f21_point 358) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → (f21_val S g).satisfies (([6, 38, 49, 81, 92, 124, 135, 167, 178, 189, 221, 232, 264, 275, 307, 318, 350, 361, 393, 404, 436] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 10 6 ([6, 38, 49, 81, 92, 124, 135, 167, 178, 189, 221, 232, 264, 275, 307, 318, 350, 361, 393, 404, 436] : List (Fin 441)) (hcover 10 (by decide) hg 6)
    decide
    apply f21_sat_one
    change g 10 → f21_point 6 ∈ S → f21_point 38 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 38) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 6 ∈ S → f21_point 178 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 178) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 6 ∈ S → f21_point 232 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 232) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 124 ∈ S → f21_point 189 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 124 ≠ f21_point 189) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 167 ∈ S → f21_point 189 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 189) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 167 ∈ S → f21_point 232 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 232) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 189 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 189 ≠ f21_point 361) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 9 ∈ S → f21_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 41) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 52 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 52) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 63 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 63) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 106 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 106) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 235 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 235) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 310 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 310) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 364 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 364) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 41 ∈ S → f21_point 439 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 439) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → (f21_val S g).satisfies (([12, 23, 55, 66, 98, 109, 141, 152, 184, 195, 227, 238, 270, 281, 313, 324, 356, 367, 378, 410, 421] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 10 12 ([12, 23, 55, 66, 98, 109, 141, 152, 184, 195, 227, 238, 270, 281, 313, 324, 356, 367, 378, 410, 421] : List (Fin 441)) (hcover 10 (by decide) hg 12)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 12 ∈ S → f21_point 367 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 367) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 12 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 421) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 23 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 23 ≠ f21_point 421) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 378 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 378 ≠ f21_point 421) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → (f21_val S g).satisfies (([15, 26, 58, 69, 101, 112, 144, 155, 187, 198, 230, 241, 252, 284, 295, 327, 338, 370, 381, 413, 424] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 10 15 ([15, 26, 58, 69, 101, 112, 144, 155, 187, 198, 230, 241, 252, 284, 295, 327, 338, 370, 381, 413, 424] : List (Fin 441)) (hcover 10 (by decide) hg 15)
    decide
    apply f21_sat_one
    change g 10 → f21_point 15 ∈ S → f21_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 15 ≠ f21_point 26) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 15 ∈ S → f21_point 187 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 15 ≠ f21_point 187) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 26 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 241) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 26 ∈ S → f21_point 295 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 295) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 241 ∈ S → f21_point 252 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 241 ≠ f21_point 252) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → (f21_val S g).satisfies (([18, 29, 61, 72, 104, 115, 126, 158, 169, 201, 212, 244, 255, 287, 298, 330, 341, 373, 384, 416, 427] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 10 18 ([18, 29, 61, 72, 104, 115, 126, 158, 169, 201, 212, 244, 255, 287, 298, 330, 341, 373, 384, 416, 427] : List (Fin 441)) (hcover 10 (by decide) hg 18)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 18 ∈ S → f21_point 61 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 18 ≠ f21_point 61) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 29 ∈ S → f21_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 115) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 10 → f21_point 61 ∈ S → f21_point 104 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 61 ≠ f21_point 104) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 10 → f21_point 61 ∈ S → f21_point 126 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 61 ≠ f21_point 126) (hinj 10 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 29 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 29) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 58) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 124 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 124) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 169 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 169) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 235 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 235) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 293 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 293) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 367 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 367) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 0 ∈ S → f21_point 433 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 433) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → (f21_val S g).satisfies (([3, 32, 61, 69, 98, 106, 135, 164, 172, 201, 230, 238, 267, 275, 304, 333, 341, 370, 378, 407, 436] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 13 3 ([3, 32, 61, 69, 98, 106, 135, 164, 172, 201, 230, 238, 267, 275, 304, 333, 341, 370, 378, 407, 436] : List (Fin 441)) (hcover 13 (by decide) hg 3)
    decide
    apply f21_sat_one
    change g 13 → f21_point 3 ∈ S → f21_point 106 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 3 ≠ f21_point 106) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 32 ∈ S → f21_point 378 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 32 ≠ f21_point 378) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 378 ∈ S → f21_point 436 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 378 ≠ f21_point 436) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → (f21_val S g).satisfies (([6, 35, 43, 72, 101, 109, 138, 167, 175, 204, 212, 241, 270, 278, 307, 315, 344, 373, 381, 410, 439] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 13 6 ([6, 35, 43, 72, 101, 109, 138, 167, 175, 204, 212, 241, 270, 278, 307, 315, 344, 373, 381, 410, 439] : List (Fin 441)) (hcover 13 (by decide) hg 6)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 6 ∈ S → f21_point 35 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 35) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 6 ∈ S → f21_point 175 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 175) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 6 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 241) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 6 ∈ S → f21_point 439 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 439) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 35 ∈ S → f21_point 43 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 43) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 35 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 241) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 35 ∈ S → f21_point 307 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 307) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 43 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 43 ≠ f21_point 315) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 167 ∈ S → f21_point 175 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 175) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 167 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 241) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 167 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 315) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 167 ∈ S → f21_point 439 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 439) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 241 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 241 ≠ f21_point 315) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 307 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 307 ≠ f21_point 315) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → (f21_val S g).satisfies (([9, 38, 46, 75, 104, 112, 141, 149, 178, 207, 215, 244, 252, 281, 310, 318, 347, 376, 384, 413, 421] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 13 9 ([9, 38, 46, 75, 104, 112, 141, 149, 178, 207, 215, 244, 252, 281, 310, 318, 347, 376, 384, 413, 421] : List (Fin 441)) (hcover 13 (by decide) hg 9)
    decide
    apply f21_sat_one
    change g 13 → f21_point 9 ∈ S → f21_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 112) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 9 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 421) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 38 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 38 ≠ f21_point 421) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 46 ∈ S → f21_point 104 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 46 ≠ f21_point 104) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 12 ∈ S → f21_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 41) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 49 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 49) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 115) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 189 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 189) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 247 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 247) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 313 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 313) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 358 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 358) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 41 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 424) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 15 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 15 ≠ f21_point 361) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 126 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 126 ≠ f21_point 250) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 361 ∈ S → f21_point 419 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 361 ≠ f21_point 419) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → (f21_val S g).satisfies (([18, 26, 55, 63, 92, 121, 129, 158, 187, 195, 224, 232, 261, 290, 298, 327, 356, 364, 393, 401, 430] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 13 18 ([18, 26, 55, 63, 92, 121, 129, 158, 187, 195, 224, 232, 261, 290, 298, 327, 356, 364, 393, 401, 430] : List (Fin 441)) (hcover 13 (by decide) hg 18)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 18 ∈ S → f21_point 232 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 18 ≠ f21_point 232) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 13 → f21_point 26 ∈ S → f21_point 121 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 121) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 13 → f21_point 121 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 121 ≠ f21_point 356) (hinj 13 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 26 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 26) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 52 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 52) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 104 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 104) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 109 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 109) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 187 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 187) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 244 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 244) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 358 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 358) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 0 ∈ S → f21_point 436 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 436) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → (f21_val S g).satisfies (([3, 29, 55, 81, 86, 112, 138, 164, 169, 195, 221, 247, 252, 278, 304, 330, 356, 361, 387, 413, 439] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 16 3 ([3, 29, 55, 81, 86, 112, 138, 164, 169, 195, 221, 247, 252, 278, 304, 330, 356, 361, 387, 413, 439] : List (Fin 441)) (hcover 16 (by decide) hg 3)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 3 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 3 ≠ f21_point 356) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 3 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 3 ≠ f21_point 361) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 29 ∈ S → f21_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 112) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 29 ∈ S → f21_point 247 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 247) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 29 ∈ S → f21_point 252 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 252) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 29 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 361) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 304 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 304 ≠ f21_point 356) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 356 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 356 ≠ f21_point 361) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → (f21_val S g).satisfies (([6, 32, 58, 63, 89, 115, 141, 167, 172, 198, 224, 250, 255, 281, 307, 333, 338, 364, 390, 416, 421] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 16 6 ([6, 32, 58, 63, 89, 115, 141, 167, 172, 198, 224, 250, 255, 281, 307, 333, 338, 364, 390, 416, 421] : List (Fin 441)) (hcover 16 (by decide) hg 6)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 6 ∈ S → f21_point 32 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 32) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 6 ∈ S → f21_point 172 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 172) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 6 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 250) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 6 ∈ S → f21_point 364 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 364) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 6 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 421) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 32 ∈ S → f21_point 307 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 32 ≠ f21_point 307) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 167 ∈ S → f21_point 172 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 172) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 167 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 250) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 167 ∈ S → f21_point 364 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 364) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → (f21_val S g).satisfies (([9, 35, 61, 66, 92, 118, 144, 149, 175, 201, 227, 232, 258, 284, 310, 315, 341, 367, 393, 419, 424] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 16 9 ([9, 35, 61, 66, 92, 118, 144, 149, 175, 201, 227, 232, 258, 284, 310, 315, 341, 367, 393, 419, 424] : List (Fin 441)) (hcover 16 (by decide) hg 9)
    decide
    apply f21_sat_one
    change g 16 → f21_point 9 ∈ S → f21_point 61 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 61) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 35 ∈ S → f21_point 310 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 310) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 35 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 424) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 310 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 310 ≠ f21_point 315) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 315 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 315 ≠ f21_point 424) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → (f21_val S g).satisfies (([12, 38, 43, 69, 95, 121, 126, 152, 178, 204, 230, 235, 261, 287, 313, 318, 344, 370, 396, 401, 427] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 16 12 ([12, 38, 43, 69, 95, 121, 126, 152, 178, 204, 230, 235, 261, 287, 313, 318, 344, 370, 396, 401, 427] : List (Fin 441)) (hcover 16 (by decide) hg 12)
    decide
    apply f21_sat_one
    change g 16 → f21_point 12 ∈ S → f21_point 121 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 121) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 38 ∈ S → f21_point 235 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 38 ≠ f21_point 235) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 15 ∈ S → f21_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 15 ≠ f21_point 41) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 46 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 46) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 124 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 124) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 238 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 238) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 295 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 295) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 373 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 373) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 378 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 378) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 41 ∈ S → f21_point 430 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 430) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → (f21_val S g).satisfies (([18, 23, 49, 75, 101, 106, 132, 158, 184, 189, 215, 241, 267, 293, 298, 324, 350, 376, 381, 407, 433] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 16 18 ([18, 23, 49, 75, 101, 106, 132, 158, 184, 189, 215, 241, 267, 293, 298, 324, 350, 376, 381, 407, 433] : List (Fin 441)) (hcover 16 (by decide) hg 18)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 18 ∈ S → f21_point 241 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 18 ≠ f21_point 241) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 49 ∈ S → f21_point 293 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 49 ≠ f21_point 293) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 16 → f21_point 189 ∈ S → f21_point 293 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 189 ≠ f21_point 293) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 16 → f21_point 189 ∈ S → f21_point 433 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 189 ≠ f21_point 433) (hinj 16 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 23 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 23) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 46 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 46) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 115 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 115) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 184 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 184) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 230 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 230) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 232 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 232) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 370 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 370) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 0 ∈ S → f21_point 439 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 0 ≠ f21_point 439) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → (f21_val S g).satisfies (([3, 26, 49, 72, 95, 118, 141, 164, 187, 189, 212, 235, 258, 281, 304, 327, 350, 373, 396, 419, 421] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 19 3 ([3, 26, 49, 72, 95, 118, 141, 164, 187, 189, 212, 235, 258, 281, 304, 327, 350, 373, 396, 419, 421] : List (Fin 441)) (hcover 19 (by decide) hg 3)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 26 ∈ S → f21_point 49 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 49) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 26 ∈ S → f21_point 189 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 189) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 26 ∈ S → f21_point 421 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 26 ≠ f21_point 421) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 187 ∈ S → f21_point 189 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 187 ≠ f21_point 189) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → (f21_val S g).satisfies (([6, 29, 52, 75, 98, 121, 144, 167, 169, 192, 215, 238, 261, 284, 307, 330, 353, 376, 378, 401, 424] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 19 6 ([6, 29, 52, 75, 98, 121, 144, 167, 169, 192, 215, 238, 261, 284, 307, 330, 353, 376, 378, 401, 424] : List (Fin 441)) (hcover 19 (by decide) hg 6)
    decide
    apply f21_sat_one
    change g 19 → f21_point 6 ∈ S → f21_point 29 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 29) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 6 ∈ S → f21_point 121 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 121) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 6 ∈ S → f21_point 169 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 169) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 6 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 6 ≠ f21_point 424) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 29 ∈ S → f21_point 307 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 29 ≠ f21_point 307) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 52 ∈ S → f21_point 378 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 52 ≠ f21_point 378) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 121 ∈ S → f21_point 167 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 121 ≠ f21_point 167) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 167 ∈ S → f21_point 169 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 169) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 167 ∈ S → f21_point 424 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 167 ≠ f21_point 424) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → (f21_val S g).satisfies (([9, 32, 55, 78, 101, 124, 126, 149, 172, 195, 218, 241, 264, 287, 310, 333, 356, 358, 381, 404, 427] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 19 9 ([9, 32, 55, 78, 101, 124, 126, 149, 172, 195, 218, 241, 264, 287, 310, 333, 356, 358, 381, 404, 427] : List (Fin 441)) (hcover 19 (by decide) hg 9)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 9 ∈ S → f21_point 32 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 32) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 9 ∈ S → f21_point 172 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 9 ≠ f21_point 172) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 32 ∈ S → f21_point 310 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 32 ≠ f21_point 310) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 126 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 126 ≠ f21_point 356) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 172 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 172 ≠ f21_point 356) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 241 ∈ S → f21_point 356 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 241 ≠ f21_point 356) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 356 ∈ S → f21_point 427 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 356 ≠ f21_point 427) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → (f21_val S g).satisfies (([12, 35, 58, 81, 104, 106, 129, 152, 175, 198, 221, 244, 267, 290, 313, 315, 338, 361, 384, 407, 430] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 19 12 ([12, 35, 58, 81, 104, 106, 129, 152, 175, 198, 221, 244, 267, 290, 313, 315, 338, 361, 384, 407, 430] : List (Fin 441)) (hcover 19 (by decide) hg 12)
    decide
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 12 ∈ S → f21_point 35 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 35) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 12 ∈ S → f21_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 58) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 12 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 12 ≠ f21_point 361) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 35 ∈ S → f21_point 58 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 58) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 35 ∈ S → f21_point 244 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 244) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 35 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 35 ≠ f21_point 361) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 58 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 58 ≠ f21_point 315) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 104 ∈ S → f21_point 175 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 104 ≠ f21_point 175) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 104 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 104 ≠ f21_point 315) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 104 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 104 ≠ f21_point 361) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 244 ∈ S → f21_point 315 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 244 ≠ f21_point 315) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 315 ∈ S → f21_point 361 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 315 ≠ f21_point 361) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → (f21_val S g).satisfies (([15, 38, 61, 63, 86, 109, 132, 155, 178, 201, 224, 247, 270, 293, 295, 318, 341, 364, 387, 410, 433] : List (Fin 441)).map fun i => Sat.Literal.pos i.val)
    intro hg
    apply f21_sat_line S g 19 15 ([15, 38, 61, 63, 86, 109, 132, 155, 178, 201, 224, 247, 270, 293, 295, 318, 341, 364, 387, 410, 433] : List (Fin 441)) (hcover 19 (by decide) hg 15)
    decide
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 38 ∈ S → f21_point 61 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 38 ≠ f21_point 61) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 38 ∈ S → f21_point 364 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 38 ≠ f21_point 364) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 61 ∈ S → f21_point 293 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 61 ≠ f21_point 293) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 18 ∈ S → f21_point 41 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 18 ≠ f21_point 41) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 43 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 43) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 112 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 112) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 250 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 250) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 252 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 252) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 298 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 298) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 367 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 367) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change g 19 → f21_point 41 ∈ S → f21_point 436 ∈ S → False
    intro hg hi hj
    exact (by decide : f21_point 41 ≠ f21_point 436) (hinj 19 (by decide) hg hi hj (by decide))
    apply f21_sat_one
    change (¬ g 4) → (¬ g 10) → (¬ g 13) → False
    intro ha hb hc
    have hh := hthree 4 10 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_and
    apply f21_sat_one
    change (¬ g 4) → (¬ g 10) → (¬ g 16) → False
    intro ha hb hc
    have hh := hthree 4 10 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_one
    change (¬ g 4) → (¬ g 10) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 4 10 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change (¬ g 4) → (¬ g 13) → (¬ g 16) → False
    intro ha hb hc
    have hh := hthree 4 13 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_one
    change (¬ g 4) → (¬ g 13) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 4 13 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_and
    apply f21_sat_one
    change (¬ g 4) → (¬ g 16) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 4 16 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_one
    change (¬ g 10) → (¬ g 13) → (¬ g 16) → False
    intro ha hb hc
    have hh := hthree 10 13 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_and
    apply f21_sat_and
    apply f21_sat_one
    change (¬ g 10) → (¬ g 13) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 10 13 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_one
    change (¬ g 10) → (¬ g 16) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 10 16 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_and
    apply f21_sat_one
    change (¬ g 13) → (¬ g 16) → (¬ g 19) → False
    intro ha hb hc
    have hh := hthree 13 16 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rcases hh with hh | hh | hh <;> contradiction
    apply f21_sat_one
    change g 10 → g 13 → g 19 → (¬ g 4) → (¬ g 16) → False
    intro h10 h13 h19 h4 h16
    rcases hnot with h | h | h | h | h <;> contradiction
  exact aftd_fiber21_sat_proof (f21_val S g) hF
