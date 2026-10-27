import AFTD.Prelude
import AFTD.Kb.Tcs.Threshold101Edges

/-!
# threshold101_no_four_coloring

Topic: combinatorics   Node: 3e2c63e35cf3

Provenance: helper lemma. Helper for arXiv:2610.28828 Theorem 2. Exact 101-point coordinates and a trimmed witness subgraph from https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_101p_088928. points.csv SHA256 362e063b96d5075c6904446d3e9164879b47233de32158e46ff6703c96704093. Independent integer geometry and SAT check: experiment 6995; the LRAT proof is independently generated and kernel checked.

No assignment of four colors to the 101 vertices separates every trimmed witness edge.
-/

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lrat_proof threshold101_colour_core_fixed "p cnf 404 400\n1 2 3 4 0\n9 10 11 12 0\n13 14 15 16 0\n17 18 19 20 0\n21 22 23 24 0\n25 26 27 28 0\n29 30 31 32 0\n33 34 35 36 0\n37 38 39 40 0\n41 42 43 44 0\n45 46 47 48 0\n49 50 51 52 0\n53 54 55 56 0\n57 58 59 60 0\n61 62 63 64 0\n65 66 67 68 0\n69 70 71 72 0\n77 78 79 80 0\n81 82 83 84 0\n85 86 87 88 0\n89 90 91 92 0\n93 94 95 96 0\n97 98 99 100 0\n101 102 103 104 0\n105 106 107 108 0\n109 110 111 112 0\n113 114 115 116 0\n117 118 119 120 0\n121 122 123 124 0\n125 126 127 128 0\n129 130 131 132 0\n137 138 139 140 0\n141 142 143 144 0\n145 146 147 148 0\n149 150 151 152 0\n153 154 155 156 0\n157 158 159 160 0\n161 162 163 164 0\n165 166 167 168 0\n169 170 171 172 0\n173 174 175 176 0\n177 178 179 180 0\n181 182 183 184 0\n185 186 187 188 0\n189 190 191 192 0\n193 194 195 196 0\n197 198 199 200 0\n201 202 203 204 0\n205 206 207 208 0\n209 210 211 212 0\n213 214 215 216 0\n217 218 219 220 0\n221 222 223 224 0\n225 226 227 228 0\n229 230 231 232 0\n233 234 235 236 0\n237 238 239 240 0\n241 242 243 244 0\n245 246 247 248 0\n249 250 251 252 0\n253 254 255 256 0\n257 258 259 260 0\n261 262 263 264 0\n265 266 267 268 0\n269 270 271 272 0\n273 274 275 276 0\n277 278 279 280 0\n281 282 283 284 0\n285 286 287 288 0\n289 290 291 292 0\n293 294 295 296 0\n297 298 299 300 0\n301 302 303 304 0\n305 306 307 308 0\n309 310 311 312 0\n313 314 315 316 0\n317 318 319 320 0\n321 322 323 324 0\n325 326 327 328 0\n329 330 331 332 0\n333 334 335 336 0\n337 338 339 340 0\n341 342 343 344 0\n345 346 347 348 0\n349 350 351 352 0\n353 354 355 356 0\n357 358 359 360 0\n361 362 363 364 0\n365 366 367 368 0\n369 370 371 372 0\n373 374 375 376 0\n377 378 379 380 0\n381 382 383 384 0\n385 386 387 388 0\n389 390 391 392 0\n393 394 395 396 0\n397 398 399 400 0\n401 402 403 404 0\n-1 -5 0\n-4 -164 0\n-3 -243 0\n-2 -382 0\n-5 -21 0\n-5 -25 0\n-5 -29 0\n-5 -53 0\n-5 -77 0\n-5 -85 0\n-5 -93 0\n-5 -125 0\n-5 -129 0\n-5 -137 0\n-5 -149 0\n-5 -185 0\n-5 -209 0\n-5 -213 0\n-5 -221 0\n-5 -237 0\n-5 -253 0\n-5 -261 0\n-5 -265 0\n-5 -269 0\n-5 -277 0\n-5 -285 0\n-5 -289 0\n-5 -293 0\n-5 -321 0\n-5 -325 0\n-5 -333 0\n-5 -337 0\n-5 -341 0\n-5 -345 0\n-5 -349 0\n-5 -353 0\n-5 -389 0\n-5 -393 0\n-5 -397 0\n-5 -401 0\n-9 -69 0\n-10 -254 0\n-12 -288 0\n-11 -355 0\n-13 -101 0\n-16 -128 0\n-15 -135 0\n-14 -398 0\n-17 -113 0\n-19 -135 0\n-18 -270 0\n-20 -288 0\n-18 -338 0\n-18 -350 0\n-18 -390 0\n-22 -174 0\n-24 -364 0\n-23 -367 0\n-28 -72 0\n-27 -179 0\n-26 -318 0\n-32 -156 0\n-31 -199 0\n-30 -226 0\n-35 -135 0\n-34 -138 0\n-33 -193 0\n-33 -201 0\n-36 -288 0\n-39 -135 0\n-38 -150 0\n-37 -153 0\n-40 -288 0\n-42 -74 0\n-43 -135 0\n-44 -212 0\n-44 -264 0\n-41 -281 0\n-44 -348 0\n-44 -392 0\n-47 -135 0\n-45 -165 0\n-46 -210 0\n-46 -214 0\n-48 -288 0\n-46 -326 0\n-46 -394 0\n-50 -74 0\n-49 -81 0\n-52 -88 0\n-51 -135 0\n-54 -58 0\n-55 -251 0\n-56 -376 0\n-54 -386 0\n-59 -135 0\n-60 -288 0\n-57 -361 0\n-57 -365 0\n-62 -74 0\n-61 -141 0\n-63 -215 0\n-63 -263 0\n-64 -288 0\n-63 -339 0\n-63 -343 0\n-66 -74 0\n-67 -151 0\n-65 -153 0\n-68 -288 0\n-70 -74 0\n-71 -135 0\n-72 -152 0\n-72 -400 0\n-74 -82 0\n-74 -114 0\n-74 -146 0\n-74 -166 0\n-74 -170 0\n-74 -178 0\n-74 -194 0\n-74 -202 0\n-74 -206 0\n-74 -250 0\n-74 -282 0\n-74 -286 0\n-74 -302 0\n-74 -310 0\n-74 -330 0\n-74 -362 0\n-74 -366 0\n-74 -374 0\n-78 -106 0\n-79 -195 0\n-80 -204 0\n-83 -131 0\n-81 -189 0\n-84 -288 0\n-87 -103 0\n-86 -190 0\n-91 -223 0\n-90 -266 0\n-92 -288 0\n-89 -357 0\n-89 -377 0\n-94 -110 0\n-95 -147 0\n-96 -248 0\n-96 -376 0\n-99 -135 0\n-100 -240 0\n-97 -241 0\n-98 -266 0\n-97 -381 0\n-97 -385 0\n-102 -266 0\n-104 -288 0\n-103 -335 0\n-107 -135 0\n-105 -177 0\n-108 -288 0\n-111 -135 0\n-109 -249 0\n-112 -288 0\n-109 -373 0\n-116 -280 0\n-115 -403 0\n-119 -135 0\n-117 -157 0\n-120 -216 0\n-118 -342 0\n-123 -135 0\n-121 -181 0\n-122 -266 0\n-124 -292 0\n-124 -324 0\n-124 -344 0\n-124 -396 0\n-127 -159 0\n-126 -318 0\n-132 -360 0\n-130 -378 0\n-135 -143 0\n-135 -155 0\n-135 -163 0\n-135 -175 0\n-135 -191 0\n-135 -203 0\n-135 -207 0\n-135 -227 0\n-135 -231 0\n-135 -235 0\n-135 -247 0\n-135 -259 0\n-135 -267 0\n-135 -275 0\n-135 -279 0\n-135 -287 0\n-135 -299 0\n-135 -307 0\n-135 -311 0\n-135 -319 0\n-135 -347 0\n-135 -351 0\n-135 -359 0\n-135 -363 0\n-135 -375 0\n-135 -379 0\n-135 -383 0\n-135 -387 0\n-139 -171 0\n-140 -312 0\n-142 -346 0\n-144 -352 0\n-145 -233 0\n-148 -288 0\n-145 -373 0\n-145 -385 0\n-154 -266 0\n-159 -255 0\n-158 -266 0\n-160 -288 0\n-159 -323 0\n-159 -327 0\n-159 -399 0\n-161 -197 0\n-161 -225 0\n-162 -266 0\n-168 -340 0\n-167 -391 0\n-172 -288 0\n-169 -297 0\n-173 -205 0\n-176 -288 0\n-173 -329 0\n-180 -336 0\n-183 -211 0\n-182 -262 0\n-184 -288 0\n-187 -219 0\n-188 -236 0\n-186 -386 0\n-192 -288 0\n-196 -288 0\n-198 -266 0\n-200 -288 0\n-208 -296 0\n-217 -229 0\n-218 -266 0\n-217 -273 0\n-220 -288 0\n-224 -232 0\n-222 -274 0\n-228 -288 0\n-230 -266 0\n-234 -266 0\n-238 -258 0\n-239 -371 0\n-242 -266 0\n-244 -288 0\n-245 -257 0\n-246 -266 0\n-245 -369 0\n-252 -288 0\n-256 -308 0\n-260 -288 0\n-266 -278 0\n-268 -288 0\n-266 -306 0\n-266 -358 0\n-266 -370 0\n-266 -402 0\n-271 -283 0\n-272 -288 0\n-276 -288 0\n-284 -288 0\n-288 -300 0\n-288 -316 0\n-288 -320 0\n-288 -332 0\n-288 -368 0\n-288 -372 0\n-288 -380 0\n-288 -384 0\n-288 -388 0\n-288 -404 0\n-291 -315 0\n-290 -318 0\n-294 -298 0\n-295 -331 0\n-297 -309 0\n-301 -317 0\n-304 -328 0\n-303 -395 0\n-305 -313 0\n-308 -356 0\n-314 -322 0\n-318 -334 0\n-318 -354 0\n5 0\n74 0\n135 0\n" "401 -1 0 398 99 0\n402 -21 0 398 103 0\n403 -25 0 398 104 0\n404 -29 0 398 105 0\n405 -53 0 398 106 0\n406 -77 0 398 107 0\n407 -85 0 398 108 0\n408 -93 0 398 109 0\n409 -125 0 398 110 0\n410 -129 0 398 111 0\n411 -137 0 398 112 0\n412 -149 0 398 113 0\n413 -185 0 398 114 0\n414 -209 0 398 115 0\n415 -213 0 398 116 0\n416 -221 0 398 117 0\n417 -237 0 398 118 0\n418 -253 0 398 119 0\n419 -261 0 398 120 0\n420 -265 0 398 121 0\n421 -269 0 398 122 0\n422 -277 0 398 123 0\n423 -285 0 398 124 0\n424 -289 0 398 125 0\n425 -293 0 398 126 0\n426 -321 0 398 127 0\n427 -325 0 398 128 0\n428 -333 0 398 129 0\n429 -337 0 398 130 0\n430 -341 0 398 131 0\n431 -345 0 398 132 0\n432 -349 0 398 133 0\n433 -353 0 398 134 0\n434 -389 0 398 135 0\n435 -393 0 398 136 0\n436 -397 0 398 137 0\n437 -401 0 398 138 0\n438 -42 0 399 172 0\n439 -50 0 399 186 0\n440 -62 0 399 198 0\n441 -66 0 399 205 0\n442 -70 0 399 209 0\n443 -82 0 399 213 0\n444 -114 0 399 214 0\n445 -146 0 399 215 0\n446 -166 0 399 216 0\n447 -170 0 399 217 0\n448 -178 0 399 218 0\n449 -194 0 399 219 0\n450 -202 0 399 220 0\n451 -206 0 399 221 0\n452 -250 0 399 222 0\n453 -282 0 399 223 0\n454 -286 0 399 224 0\n455 -302 0 399 225 0\n456 -310 0 399 226 0\n457 -330 0 399 227 0\n458 -362 0 399 228 0\n459 -366 0 399 229 0\n460 -374 0 399 230 0\n461 -15 0 400 145 0\n462 -19 0 400 148 0\n463 -35 0 400 163 0\n464 -39 0 400 168 0\n465 -43 0 400 173 0\n466 -47 0 400 179 0\n467 -51 0 400 189 0\n468 -59 0 400 194 0\n469 -71 0 400 210 0\n470 -99 0 400 248 0\n471 -107 0 400 257 0\n472 -111 0 400 260 0\n473 -119 0 400 266 0\n474 -123 0 400 270 0\n475 -143 0 400 281 0\n476 -155 0 400 282 0\n477 -163 0 400 283 0\n478 -175 0 400 284 0\n479 -191 0 400 285 0\n480 -203 0 400 286 0\n481 -207 0 400 287 0\n482 -227 0 400 288 0\n483 -231 0 400 289 0\n484 -235 0 400 290 0\n485 -247 0 400 291 0\n486 -259 0 400 292 0\n487 -267 0 400 293 0\n488 -275 0 400 294 0\n489 -279 0 400 295 0\n490 -287 0 400 296 0\n491 -299 0 400 297 0\n492 -307 0 400 298 0\n493 -311 0 400 299 0\n494 -319 0 400 300 0\n495 -347 0 400 301 0\n496 -351 0 400 302 0\n497 -359 0 400 303 0\n498 -363 0 400 304 0\n499 -375 0 400 305 0\n500 -379 0 400 306 0\n501 -383 0 400 307 0\n502 -387 0 400 308 0\n503 288 0 490 423 454 69 0\n504 -12 0 503 141 0\n505 -20 0 503 150 0\n506 -36 0 503 167 0\n507 -40 0 503 171 0\n508 -48 0 503 183 0\n509 -60 0 503 195 0\n510 -64 0 503 202 0\n511 -68 0 503 208 0\n512 -84 0 503 236 0\n513 -92 0 503 241 0\n514 -104 0 503 255 0\n515 -108 0 503 259 0\n516 -112 0 503 262 0\n517 -148 0 503 314 0\n518 -160 0 503 320 0\n519 -172 0 503 329 0\n520 -176 0 503 332 0\n521 -184 0 503 337 0\n522 -192 0 503 341 0\n523 -196 0 503 342 0\n524 -200 0 503 344 0\n525 -220 0 503 349 0\n526 -228 0 503 352 0\n527 -244 0 503 358 0\n528 -252 0 503 362 0\n529 -260 0 503 364 0\n530 -268 0 503 366 0\n531 -272 0 503 372 0\n532 -276 0 503 373 0\n533 -284 0 503 374 0\n534 -300 0 503 375 0\n535 -316 0 503 376 0\n536 -320 0 503 377 0\n537 -332 0 503 378 0\n538 -368 0 503 379 0\n539 -372 0 503 380 0\n540 -380 0 503 381 0\n541 -384 0 503 382 0\n542 -388 0 503 383 0\n543 -404 0 503 384 0\n544 266 0 530 420 487 64 0\n545 -90 0 544 240 0\n546 -98 0 544 251 0\n547 -102 0 544 254 0\n548 -122 0 544 272 0\n549 -154 0 544 317 0\n550 -158 0 544 319 0\n551 -162 0 544 326 0\n552 -198 0 544 343 0\n553 -218 0 544 347 0\n554 -230 0 544 353 0\n555 -234 0 544 354 0\n556 -242 0 544 357 0\n557 -246 0 544 360 0\n558 -278 0 544 365 0\n559 -306 0 544 367 0\n560 -358 0 544 368 0\n561 -370 0 544 369 0\n562 -402 0 544 370 0\n563 280 0 558 422 489 67 0\n564 403 0 562 437 543 98 0\n565 -116 0 563 264 0\n566 -115 0 564 265 0\n567 113 0 566 444 565 27 0\n568 -17 0 567 147 0\n569 18 0 568 462 505 4 0\n570 -270 0 569 149 0\n571 -338 0 569 151 0\n572 -350 0 569 152 0\n573 -390 0 569 153 0\n574 271 0 570 421 531 65 0\n575 352 0 572 432 496 85 0\n576 -283 0 574 371 0\n577 -144 0 575 312 0\n578 281 0 576 453 533 68 0\n579 -41 0 578 176 0\n580 44 0 579 438 465 10 0\n581 -212 0 580 174 0\n582 -264 0 580 175 0\n583 -348 0 580 177 0\n584 -392 0 580 178 0\n585 346 0 583 431 495 84 0\n586 391 0 584 434 573 95 0\n587 -142 0 585 311 0\n588 -167 0 586 328 0\n589 141 0 587 475 577 33 0\n590 -61 0 589 199 0\n591 63 0 590 440 510 15 0\n592 -215 0 591 200 0\n593 -263 0 591 201 0\n594 -339 0 591 203 0\n595 -343 0 591 204 0\n596 262 0 593 419 582 63 0\n597 340 0 594 429 571 82 0\n598 -182 0 596 336 0\n599 -168 0 597 327 0\n600 165 0 599 446 588 39 0\n601 -45 0 600 180 0\n602 46 0 601 466 508 11 0\n603 -210 0 602 181 0\n604 -214 0 602 182 0\n605 -326 0 602 184 0\n606 -394 0 602 185 0\n607 211 0 603 414 581 50 0\n608 216 0 604 415 592 51 0\n609 -183 0 607 335 0\n610 -120 0 608 268 0\n611 181 0 609 598 521 43 0\n612 -121 0 611 271 0\n613 124 0 612 474 548 29 0\n614 -292 0 613 273 0\n615 -324 0 613 274 0\n616 -344 0 613 275 0\n617 -396 0 613 276 0\n618 342 0 616 430 595 83 0\n619 395 0 617 435 606 96 0\n620 -118 0 618 269 0\n621 -303 0 619 392 0\n622 117 0 620 473 610 28 0\n623 -157 0 622 267 0\n624 159 0 623 550 518 37 0\n625 -127 0 624 277 0\n626 -255 0 624 318 0\n627 -323 0 624 321 0\n628 -327 0 624 322 0\n629 -399 0 624 323 0\n630 322 0 627 426 615 78 0\n631 328 0 628 427 605 79 0\n632 -314 0 630 395 0\n633 -304 0 631 391 0\n634 301 0 633 455 621 73 0\n635 -317 0 634 390 0\n636 318 0 635 494 536 77 0\n637 -26 0 636 159 0\n638 -126 0 636 278 0\n639 -290 0 636 386 0\n640 -334 0 636 396 0\n641 -354 0 636 397 0\n642 128 0 638 409 625 30 0\n643 291 0 639 424 614 70 0\n644 -16 0 642 144 0\n645 -315 0 643 385 0\n646 313 0 645 632 535 76 0\n647 -305 0 646 393 0\n648 308 0 647 492 559 74 0\n649 -256 0 648 363 0\n650 -356 0 648 394 0\n651 254 0 649 418 626 61 0\n652 355 0 650 433 641 86 0\n653 -10 0 651 140 0\n654 -11 0 652 142 0\n655 9 0 653 654 504 2 0\n656 -69 0 655 139 0\n657 72 0 656 442 469 17 0\n658 -28 0 657 157 0\n659 -152 0 657 211 0\n660 -400 0 657 212 0\n661 27 0 658 403 637 6 0\n662 398 0 660 436 629 97 0\n663 -179 0 661 158 0\n664 -14 0 662 146 0\n665 13 0 664 461 644 3 0\n666 -101 0 665 143 0\n667 103 0 666 547 514 24 0\n668 -87 0 667 237 0\n669 -335 0 667 256 0\n670 336 0 669 428 640 81 0\n671 -180 0 670 334 0\n672 177 0 671 448 663 42 0\n673 -105 0 672 258 0\n674 106 0 673 471 515 25 0\n675 -78 0 674 231 0\n676 -376 95 54 0 405 408 528 452 516 472 192 247 13 22 191 244 60 26 261 0\n677 -385 54 0 546 470 517 445 499 460 516 472 408 557 485 529 486 539 561 417 253 316 23 34 249 245 676 91 263 26 244 22 246 59 359 361 62 90 355 356 57 0\n678 -153 0 507 464 511 441 659 412 170 207 9 16 169 206 35 0\n679 156 0 678 476 549 36 0\n680 -32 0 679 160 0\n681 -161 0 524 552 526 482 680 404 324 325 47 54 161 162 7 0\n682 164 0 681 477 551 38 0\n683 -4 0 682 100 0\n684 -97 0 527 556 541 501 683 401 250 252 58 93 101 102 1 0\n685 100 0 684 470 546 23 0\n686 -240 0 685 249 0\n687 -245 0 529 486 539 561 686 417 359 361 62 90 355 356 57 0\n688 248 0 687 485 557 59 0\n689 -96 0 688 246 0\n690 -373 0 516 472 517 445 689 408 263 315 26 34 244 245 22 0\n691 376 0 690 460 499 91 0\n692 -81 0 467 439 522 479 668 407 187 235 12 45 188 238 20 0\n693 83 0 692 443 512 19 0\n694 -131 0 693 234 0\n695 -89 0 560 497 540 500 694 410 242 243 87 92 279 280 31 0\n696 91 0 695 545 513 21 0\n697 -223 0 696 239 0\n698 -217 0 554 483 532 488 697 416 346 348 55 66 350 351 53 0\n699 219 0 698 553 525 52 0\n700 -187 0 699 338 0\n701 -386 0 691 700 413 517 445 555 484 193 340 676 44 245 339 34 56 313 0\n702 385 0 701 502 542 94 0\n703 54 0 702 677 0\n704 -58 0 703 190 0\n705 57 0 704 468 509 14 0\n706 -361 0 705 196 0\n707 -365 0 705 197 0\n708 364 0 706 458 498 88 0\n709 367 0 707 459 538 89 0\n710 -24 0 708 155 0\n711 -23 0 709 156 0\n712 22 0 711 402 710 5 0\n713 -174 0 712 154 0\n714 173 0 713 478 520 41 0\n715 -205 0 714 331 0\n716 -329 0 714 333 0\n717 208 0 715 451 481 49 0\n718 331 0 716 457 537 80 0\n719 -296 0 717 345 0\n720 -295 0 718 388 0\n721 294 0 720 425 719 71 0\n722 -298 0 721 387 0\n723 297 0 722 491 534 72 0\n724 -169 0 723 330 0\n725 -309 0 723 389 0\n726 171 0 724 447 519 40 0\n727 312 0 725 456 493 75 0\n728 -139 0 726 309 0\n729 -140 0 727 310 0\n730 138 0 729 411 728 32 0\n731 -34 0 730 164 0\n732 33 0 731 463 506 8 0\n733 -193 0 732 165 0\n734 -201 0 732 166 0\n735 195 0 733 449 523 46 0\n736 204 0 734 450 480 48 0\n737 -79 0 735 232 0\n738 -80 0 736 233 0\n739 0 737 738 406 675 18 0\n"

theorem threshold101_no_four_coloring (c : Fin 101 → Fin 4)
    (hne : ∀ e ∈ threshold101_edges, c e.1 ≠ c e.2) : False := by
  classical
  let a : Fin 4 → Fin 101 := ![1, 18, 33, 71]
  have hclique : ∀ i j : Fin 4, i ≠ j →
      (a i, a j) ∈ threshold101_edges ∨ (a j, a i) ∈ threshold101_edges := by
    dsimp [a]
    decide
  have hci : Function.Injective (fun k : Fin 4 => c (a k)) := by
    intro i j hij
    by_contra h
    rcases hclique i j h with he | he
    · exact hne (a i, a j) he hij
    · exact hne (a j, a i) he hij.symm
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective (fun k : Fin 4 => c (a k))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hci, rfl⟩)
  let d : Fin 101 → Fin 4 := fun i => e.symm (c i)
  have hd (i : Fin 4) : d (a i) = i := by
    change e.symm (e i) = i
    exact e.symm_apply_apply i
  have hd0 : d 1 = 0 := by simpa [a] using hd 0
  have hd1 : d 18 = 1 := by simpa [a] using hd 1
  have hd2 : d 33 = 2 := by simpa [a] using hd 2
  have hd3 : d 71 = 3 := by simpa [a] using hd 3
  have hnd (x : Fin 101 × Fin 101) (hx : x ∈ threshold101_edges) : d x.1 ≠ d x.2 := by
    intro hh
    exact hne x hx (e.symm.injective hh)
  have hcover (i : Fin 101) : ¬ (d i ≠ 0 ∧ d i ≠ 1 ∧ d i ≠ 2 ∧ d i ≠ 3) := by
    intro hh
    have hi := (d i).isLt
    omega
  have h0 (a : Fin 4) : ¬ (d 0 = a ∧ d 1 = a) := by
    intro hh
    exact hnd (0, 1) (by decide) (hh.1.trans hh.2.symm)
  have h1 (a : Fin 4) : ¬ (d 0 = a ∧ d 40 = a) := by
    intro hh
    exact hnd (0, 40) (by decide) (hh.1.trans hh.2.symm)
  have h2 (a : Fin 4) : ¬ (d 0 = a ∧ d 60 = a) := by
    intro hh
    exact hnd (0, 60) (by decide) (hh.1.trans hh.2.symm)
  have h3 (a : Fin 4) : ¬ (d 0 = a ∧ d 95 = a) := by
    intro hh
    exact hnd (0, 95) (by decide) (hh.1.trans hh.2.symm)
  have h4 (a : Fin 4) : ¬ (d 1 = a ∧ d 5 = a) := by
    intro hh
    exact hnd (1, 5) (by decide) (hh.1.trans hh.2.symm)
  have h5 (a : Fin 4) : ¬ (d 1 = a ∧ d 6 = a) := by
    intro hh
    exact hnd (1, 6) (by decide) (hh.1.trans hh.2.symm)
  have h6 (a : Fin 4) : ¬ (d 1 = a ∧ d 7 = a) := by
    intro hh
    exact hnd (1, 7) (by decide) (hh.1.trans hh.2.symm)
  have h7 (a : Fin 4) : ¬ (d 1 = a ∧ d 13 = a) := by
    intro hh
    exact hnd (1, 13) (by decide) (hh.1.trans hh.2.symm)
  have h8 (a : Fin 4) : ¬ (d 1 = a ∧ d 19 = a) := by
    intro hh
    exact hnd (1, 19) (by decide) (hh.1.trans hh.2.symm)
  have h9 (a : Fin 4) : ¬ (d 1 = a ∧ d 21 = a) := by
    intro hh
    exact hnd (1, 21) (by decide) (hh.1.trans hh.2.symm)
  have h10 (a : Fin 4) : ¬ (d 1 = a ∧ d 23 = a) := by
    intro hh
    exact hnd (1, 23) (by decide) (hh.1.trans hh.2.symm)
  have h11 (a : Fin 4) : ¬ (d 1 = a ∧ d 31 = a) := by
    intro hh
    exact hnd (1, 31) (by decide) (hh.1.trans hh.2.symm)
  have h12 (a : Fin 4) : ¬ (d 1 = a ∧ d 32 = a) := by
    intro hh
    exact hnd (1, 32) (by decide) (hh.1.trans hh.2.symm)
  have h13 (a : Fin 4) : ¬ (d 1 = a ∧ d 34 = a) := by
    intro hh
    exact hnd (1, 34) (by decide) (hh.1.trans hh.2.symm)
  have h14 (a : Fin 4) : ¬ (d 1 = a ∧ d 37 = a) := by
    intro hh
    exact hnd (1, 37) (by decide) (hh.1.trans hh.2.symm)
  have h15 (a : Fin 4) : ¬ (d 1 = a ∧ d 46 = a) := by
    intro hh
    exact hnd (1, 46) (by decide) (hh.1.trans hh.2.symm)
  have h16 (a : Fin 4) : ¬ (d 1 = a ∧ d 52 = a) := by
    intro hh
    exact hnd (1, 52) (by decide) (hh.1.trans hh.2.symm)
  have h17 (a : Fin 4) : ¬ (d 1 = a ∧ d 53 = a) := by
    intro hh
    exact hnd (1, 53) (by decide) (hh.1.trans hh.2.symm)
  have h18 (a : Fin 4) : ¬ (d 1 = a ∧ d 55 = a) := by
    intro hh
    exact hnd (1, 55) (by decide) (hh.1.trans hh.2.symm)
  have h19 (a : Fin 4) : ¬ (d 1 = a ∧ d 59 = a) := by
    intro hh
    exact hnd (1, 59) (by decide) (hh.1.trans hh.2.symm)
  have h20 (a : Fin 4) : ¬ (d 1 = a ∧ d 63 = a) := by
    intro hh
    exact hnd (1, 63) (by decide) (hh.1.trans hh.2.symm)
  have h21 (a : Fin 4) : ¬ (d 1 = a ∧ d 65 = a) := by
    intro hh
    exact hnd (1, 65) (by decide) (hh.1.trans hh.2.symm)
  have h22 (a : Fin 4) : ¬ (d 1 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (1, 66) (by decide) (hh.1.trans hh.2.symm)
  have h23 (a : Fin 4) : ¬ (d 1 = a ∧ d 67 = a) := by
    intro hh
    exact hnd (1, 67) (by decide) (hh.1.trans hh.2.symm)
  have h24 (a : Fin 4) : ¬ (d 1 = a ∧ d 69 = a) := by
    intro hh
    exact hnd (1, 69) (by decide) (hh.1.trans hh.2.symm)
  have h25 (a : Fin 4) : ¬ (d 1 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (1, 71) (by decide) (hh.1.trans hh.2.symm)
  have h26 (a : Fin 4) : ¬ (d 1 = a ∧ d 72 = a) := by
    intro hh
    exact hnd (1, 72) (by decide) (hh.1.trans hh.2.symm)
  have h27 (a : Fin 4) : ¬ (d 1 = a ∧ d 73 = a) := by
    intro hh
    exact hnd (1, 73) (by decide) (hh.1.trans hh.2.symm)
  have h28 (a : Fin 4) : ¬ (d 1 = a ∧ d 80 = a) := by
    intro hh
    exact hnd (1, 80) (by decide) (hh.1.trans hh.2.symm)
  have h29 (a : Fin 4) : ¬ (d 1 = a ∧ d 81 = a) := by
    intro hh
    exact hnd (1, 81) (by decide) (hh.1.trans hh.2.symm)
  have h30 (a : Fin 4) : ¬ (d 1 = a ∧ d 83 = a) := by
    intro hh
    exact hnd (1, 83) (by decide) (hh.1.trans hh.2.symm)
  have h31 (a : Fin 4) : ¬ (d 1 = a ∧ d 84 = a) := by
    intro hh
    exact hnd (1, 84) (by decide) (hh.1.trans hh.2.symm)
  have h32 (a : Fin 4) : ¬ (d 1 = a ∧ d 85 = a) := by
    intro hh
    exact hnd (1, 85) (by decide) (hh.1.trans hh.2.symm)
  have h33 (a : Fin 4) : ¬ (d 1 = a ∧ d 86 = a) := by
    intro hh
    exact hnd (1, 86) (by decide) (hh.1.trans hh.2.symm)
  have h34 (a : Fin 4) : ¬ (d 1 = a ∧ d 87 = a) := by
    intro hh
    exact hnd (1, 87) (by decide) (hh.1.trans hh.2.symm)
  have h35 (a : Fin 4) : ¬ (d 1 = a ∧ d 88 = a) := by
    intro hh
    exact hnd (1, 88) (by decide) (hh.1.trans hh.2.symm)
  have h36 (a : Fin 4) : ¬ (d 1 = a ∧ d 97 = a) := by
    intro hh
    exact hnd (1, 97) (by decide) (hh.1.trans hh.2.symm)
  have h37 (a : Fin 4) : ¬ (d 1 = a ∧ d 98 = a) := by
    intro hh
    exact hnd (1, 98) (by decide) (hh.1.trans hh.2.symm)
  have h38 (a : Fin 4) : ¬ (d 1 = a ∧ d 99 = a) := by
    intro hh
    exact hnd (1, 99) (by decide) (hh.1.trans hh.2.symm)
  have h39 (a : Fin 4) : ¬ (d 1 = a ∧ d 100 = a) := by
    intro hh
    exact hnd (1, 100) (by decide) (hh.1.trans hh.2.symm)
  have h40 (a : Fin 4) : ¬ (d 2 = a ∧ d 17 = a) := by
    intro hh
    exact hnd (2, 17) (by decide) (hh.1.trans hh.2.symm)
  have h41 (a : Fin 4) : ¬ (d 2 = a ∧ d 63 = a) := by
    intro hh
    exact hnd (2, 63) (by decide) (hh.1.trans hh.2.symm)
  have h42 (a : Fin 4) : ¬ (d 2 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (2, 71) (by decide) (hh.1.trans hh.2.symm)
  have h43 (a : Fin 4) : ¬ (d 2 = a ∧ d 88 = a) := by
    intro hh
    exact hnd (2, 88) (by decide) (hh.1.trans hh.2.symm)
  have h44 (a : Fin 4) : ¬ (d 3 = a ∧ d 25 = a) := by
    intro hh
    exact hnd (3, 25) (by decide) (hh.1.trans hh.2.symm)
  have h45 (a : Fin 4) : ¬ (d 3 = a ∧ d 31 = a) := by
    intro hh
    exact hnd (3, 31) (by decide) (hh.1.trans hh.2.symm)
  have h46 (a : Fin 4) : ¬ (d 3 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (3, 33) (by decide) (hh.1.trans hh.2.symm)
  have h47 (a : Fin 4) : ¬ (d 3 = a ∧ d 99 = a) := by
    intro hh
    exact hnd (3, 99) (by decide) (hh.1.trans hh.2.symm)
  have h48 (a : Fin 4) : ¬ (d 4 = a ∧ d 28 = a) := by
    intro hh
    exact hnd (4, 28) (by decide) (hh.1.trans hh.2.symm)
  have h49 (a : Fin 4) : ¬ (d 4 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (4, 33) (by decide) (hh.1.trans hh.2.symm)
  have h50 (a : Fin 4) : ¬ (d 4 = a ∧ d 67 = a) := by
    intro hh
    exact hnd (4, 67) (by decide) (hh.1.trans hh.2.symm)
  have h51 (a : Fin 4) : ¬ (d 4 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (4, 71) (by decide) (hh.1.trans hh.2.symm)
  have h52 (a : Fin 4) : ¬ (d 4 = a ∧ d 84 = a) := by
    intro hh
    exact hnd (4, 84) (by decide) (hh.1.trans hh.2.symm)
  have h53 (a : Fin 4) : ¬ (d 4 = a ∧ d 87 = a) := by
    intro hh
    exact hnd (4, 87) (by decide) (hh.1.trans hh.2.symm)
  have h54 (a : Fin 4) : ¬ (d 4 = a ∧ d 97 = a) := by
    intro hh
    exact hnd (4, 97) (by decide) (hh.1.trans hh.2.symm)
  have h55 (a : Fin 4) : ¬ (d 5 = a ∧ d 43 = a) := by
    intro hh
    exact hnd (5, 43) (by decide) (hh.1.trans hh.2.symm)
  have h56 (a : Fin 4) : ¬ (d 5 = a ∧ d 90 = a) := by
    intro hh
    exact hnd (5, 90) (by decide) (hh.1.trans hh.2.symm)
  have h57 (a : Fin 4) : ¬ (d 5 = a ∧ d 91 = a) := by
    intro hh
    exact hnd (5, 91) (by decide) (hh.1.trans hh.2.symm)
  have h58 (a : Fin 4) : ¬ (d 6 = a ∧ d 17 = a) := by
    intro hh
    exact hnd (6, 17) (by decide) (hh.1.trans hh.2.symm)
  have h59 (a : Fin 4) : ¬ (d 6 = a ∧ d 44 = a) := by
    intro hh
    exact hnd (6, 44) (by decide) (hh.1.trans hh.2.symm)
  have h60 (a : Fin 4) : ¬ (d 6 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (6, 79) (by decide) (hh.1.trans hh.2.symm)
  have h61 (a : Fin 4) : ¬ (d 7 = a ∧ d 38 = a) := by
    intro hh
    exact hnd (7, 38) (by decide) (hh.1.trans hh.2.symm)
  have h62 (a : Fin 4) : ¬ (d 7 = a ∧ d 49 = a) := by
    intro hh
    exact hnd (7, 49) (by decide) (hh.1.trans hh.2.symm)
  have h63 (a : Fin 4) : ¬ (d 7 = a ∧ d 56 = a) := by
    intro hh
    exact hnd (7, 56) (by decide) (hh.1.trans hh.2.symm)
  have h64 (a : Fin 4) : ¬ (d 8 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (8, 33) (by decide) (hh.1.trans hh.2.symm)
  have h65 (a : Fin 4) : ¬ (d 8 = a ∧ d 34 = a) := by
    intro hh
    exact hnd (8, 34) (by decide) (hh.1.trans hh.2.symm)
  have h66 (a : Fin 4) : ¬ (d 8 = a ∧ d 48 = a) := by
    intro hh
    exact hnd (8, 48) (by decide) (hh.1.trans hh.2.symm)
  have h67 (a : Fin 4) : ¬ (d 8 = a ∧ d 50 = a) := by
    intro hh
    exact hnd (8, 50) (by decide) (hh.1.trans hh.2.symm)
  have h68 (a : Fin 4) : ¬ (d 8 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (8, 71) (by decide) (hh.1.trans hh.2.symm)
  have h69 (a : Fin 4) : ¬ (d 9 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (9, 33) (by decide) (hh.1.trans hh.2.symm)
  have h70 (a : Fin 4) : ¬ (d 9 = a ∧ d 37 = a) := by
    intro hh
    exact hnd (9, 37) (by decide) (hh.1.trans hh.2.symm)
  have h71 (a : Fin 4) : ¬ (d 9 = a ∧ d 38 = a) := by
    intro hh
    exact hnd (9, 38) (by decide) (hh.1.trans hh.2.symm)
  have h72 (a : Fin 4) : ¬ (d 9 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (9, 71) (by decide) (hh.1.trans hh.2.symm)
  have h73 (a : Fin 4) : ¬ (d 10 = a ∧ d 18 = a) := by
    intro hh
    exact hnd (10, 18) (by decide) (hh.1.trans hh.2.symm)
  have h74 (a : Fin 4) : ¬ (d 10 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (10, 33) (by decide) (hh.1.trans hh.2.symm)
  have h75 (a : Fin 4) : ¬ (d 10 = a ∧ d 52 = a) := by
    intro hh
    exact hnd (10, 52) (by decide) (hh.1.trans hh.2.symm)
  have h76 (a : Fin 4) : ¬ (d 10 = a ∧ d 65 = a) := by
    intro hh
    exact hnd (10, 65) (by decide) (hh.1.trans hh.2.symm)
  have h77 (a : Fin 4) : ¬ (d 10 = a ∧ d 70 = a) := by
    intro hh
    exact hnd (10, 70) (by decide) (hh.1.trans hh.2.symm)
  have h78 (a : Fin 4) : ¬ (d 10 = a ∧ d 86 = a) := by
    intro hh
    exact hnd (10, 86) (by decide) (hh.1.trans hh.2.symm)
  have h79 (a : Fin 4) : ¬ (d 10 = a ∧ d 97 = a) := by
    intro hh
    exact hnd (10, 97) (by decide) (hh.1.trans hh.2.symm)
  have h80 (a : Fin 4) : ¬ (d 11 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (11, 33) (by decide) (hh.1.trans hh.2.symm)
  have h81 (a : Fin 4) : ¬ (d 11 = a ∧ d 41 = a) := by
    intro hh
    exact hnd (11, 41) (by decide) (hh.1.trans hh.2.symm)
  have h82 (a : Fin 4) : ¬ (d 11 = a ∧ d 52 = a) := by
    intro hh
    exact hnd (11, 52) (by decide) (hh.1.trans hh.2.symm)
  have h83 (a : Fin 4) : ¬ (d 11 = a ∧ d 53 = a) := by
    intro hh
    exact hnd (11, 53) (by decide) (hh.1.trans hh.2.symm)
  have h84 (a : Fin 4) : ¬ (d 11 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (11, 71) (by decide) (hh.1.trans hh.2.symm)
  have h85 (a : Fin 4) : ¬ (d 11 = a ∧ d 81 = a) := by
    intro hh
    exact hnd (11, 81) (by decide) (hh.1.trans hh.2.symm)
  have h86 (a : Fin 4) : ¬ (d 11 = a ∧ d 98 = a) := by
    intro hh
    exact hnd (11, 98) (by decide) (hh.1.trans hh.2.symm)
  have h87 (a : Fin 4) : ¬ (d 12 = a ∧ d 18 = a) := by
    intro hh
    exact hnd (12, 18) (by decide) (hh.1.trans hh.2.symm)
  have h88 (a : Fin 4) : ¬ (d 12 = a ∧ d 20 = a) := by
    intro hh
    exact hnd (12, 20) (by decide) (hh.1.trans hh.2.symm)
  have h89 (a : Fin 4) : ¬ (d 12 = a ∧ d 21 = a) := by
    intro hh
    exact hnd (12, 21) (by decide) (hh.1.trans hh.2.symm)
  have h90 (a : Fin 4) : ¬ (d 12 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (12, 33) (by decide) (hh.1.trans hh.2.symm)
  have h91 (a : Fin 4) : ¬ (d 13 = a ∧ d 14 = a) := by
    intro hh
    exact hnd (13, 14) (by decide) (hh.1.trans hh.2.symm)
  have h92 (a : Fin 4) : ¬ (d 13 = a ∧ d 62 = a) := by
    intro hh
    exact hnd (13, 62) (by decide) (hh.1.trans hh.2.symm)
  have h93 (a : Fin 4) : ¬ (d 13 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (13, 93) (by decide) (hh.1.trans hh.2.symm)
  have h94 (a : Fin 4) : ¬ (d 13 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (13, 96) (by decide) (hh.1.trans hh.2.symm)
  have h95 (a : Fin 4) : ¬ (d 14 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (14, 33) (by decide) (hh.1.trans hh.2.symm)
  have h96 (a : Fin 4) : ¬ (d 14 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (14, 71) (by decide) (hh.1.trans hh.2.symm)
  have h97 (a : Fin 4) : ¬ (d 14 = a ∧ d 90 = a) := by
    intro hh
    exact hnd (14, 90) (by decide) (hh.1.trans hh.2.symm)
  have h98 (a : Fin 4) : ¬ (d 14 = a ∧ d 91 = a) := by
    intro hh
    exact hnd (14, 91) (by decide) (hh.1.trans hh.2.symm)
  have h99 (a : Fin 4) : ¬ (d 15 = a ∧ d 18 = a) := by
    intro hh
    exact hnd (15, 18) (by decide) (hh.1.trans hh.2.symm)
  have h100 (a : Fin 4) : ¬ (d 15 = a ∧ d 35 = a) := by
    intro hh
    exact hnd (15, 35) (by decide) (hh.1.trans hh.2.symm)
  have h101 (a : Fin 4) : ¬ (d 15 = a ∧ d 53 = a) := by
    intro hh
    exact hnd (15, 53) (by decide) (hh.1.trans hh.2.symm)
  have h102 (a : Fin 4) : ¬ (d 15 = a ∧ d 65 = a) := by
    intro hh
    exact hnd (15, 65) (by decide) (hh.1.trans hh.2.symm)
  have h103 (a : Fin 4) : ¬ (d 15 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (15, 71) (by decide) (hh.1.trans hh.2.symm)
  have h104 (a : Fin 4) : ¬ (d 15 = a ∧ d 84 = a) := by
    intro hh
    exact hnd (15, 84) (by decide) (hh.1.trans hh.2.symm)
  have h105 (a : Fin 4) : ¬ (d 15 = a ∧ d 85 = a) := by
    intro hh
    exact hnd (15, 85) (by decide) (hh.1.trans hh.2.symm)
  have h106 (a : Fin 4) : ¬ (d 16 = a ∧ d 18 = a) := by
    intro hh
    exact hnd (16, 18) (by decide) (hh.1.trans hh.2.symm)
  have h107 (a : Fin 4) : ¬ (d 16 = a ∧ d 37 = a) := by
    intro hh
    exact hnd (16, 37) (by decide) (hh.1.trans hh.2.symm)
  have h108 (a : Fin 4) : ¬ (d 16 = a ∧ d 38 = a) := by
    intro hh
    exact hnd (16, 38) (by decide) (hh.1.trans hh.2.symm)
  have h109 (a : Fin 4) : ¬ (d 16 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (16, 71) (by decide) (hh.1.trans hh.2.symm)
  have h110 (a : Fin 4) : ¬ (d 17 = a ∧ d 18 = a) := by
    intro hh
    exact hnd (17, 18) (by decide) (hh.1.trans hh.2.symm)
  have h111 (a : Fin 4) : ¬ (d 17 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (17, 33) (by decide) (hh.1.trans hh.2.symm)
  have h112 (a : Fin 4) : ¬ (d 17 = a ∧ d 37 = a) := by
    intro hh
    exact hnd (17, 37) (by decide) (hh.1.trans hh.2.symm)
  have h113 (a : Fin 4) : ¬ (d 17 = a ∧ d 99 = a) := by
    intro hh
    exact hnd (17, 99) (by decide) (hh.1.trans hh.2.symm)
  have h114 (a : Fin 4) : ¬ (d 18 = a ∧ d 20 = a) := by
    intro hh
    exact hnd (18, 20) (by decide) (hh.1.trans hh.2.symm)
  have h115 (a : Fin 4) : ¬ (d 18 = a ∧ d 28 = a) := by
    intro hh
    exact hnd (18, 28) (by decide) (hh.1.trans hh.2.symm)
  have h116 (a : Fin 4) : ¬ (d 18 = a ∧ d 36 = a) := by
    intro hh
    exact hnd (18, 36) (by decide) (hh.1.trans hh.2.symm)
  have h117 (a : Fin 4) : ¬ (d 18 = a ∧ d 41 = a) := by
    intro hh
    exact hnd (18, 41) (by decide) (hh.1.trans hh.2.symm)
  have h118 (a : Fin 4) : ¬ (d 18 = a ∧ d 42 = a) := by
    intro hh
    exact hnd (18, 42) (by decide) (hh.1.trans hh.2.symm)
  have h119 (a : Fin 4) : ¬ (d 18 = a ∧ d 44 = a) := by
    intro hh
    exact hnd (18, 44) (by decide) (hh.1.trans hh.2.symm)
  have h120 (a : Fin 4) : ¬ (d 18 = a ∧ d 48 = a) := by
    intro hh
    exact hnd (18, 48) (by decide) (hh.1.trans hh.2.symm)
  have h121 (a : Fin 4) : ¬ (d 18 = a ∧ d 50 = a) := by
    intro hh
    exact hnd (18, 50) (by decide) (hh.1.trans hh.2.symm)
  have h122 (a : Fin 4) : ¬ (d 18 = a ∧ d 51 = a) := by
    intro hh
    exact hnd (18, 51) (by decide) (hh.1.trans hh.2.symm)
  have h123 (a : Fin 4) : ¬ (d 18 = a ∧ d 62 = a) := by
    intro hh
    exact hnd (18, 62) (by decide) (hh.1.trans hh.2.symm)
  have h124 (a : Fin 4) : ¬ (d 18 = a ∧ d 70 = a) := by
    intro hh
    exact hnd (18, 70) (by decide) (hh.1.trans hh.2.symm)
  have h125 (a : Fin 4) : ¬ (d 18 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (18, 71) (by decide) (hh.1.trans hh.2.symm)
  have h126 (a : Fin 4) : ¬ (d 18 = a ∧ d 75 = a) := by
    intro hh
    exact hnd (18, 75) (by decide) (hh.1.trans hh.2.symm)
  have h127 (a : Fin 4) : ¬ (d 18 = a ∧ d 77 = a) := by
    intro hh
    exact hnd (18, 77) (by decide) (hh.1.trans hh.2.symm)
  have h128 (a : Fin 4) : ¬ (d 18 = a ∧ d 82 = a) := by
    intro hh
    exact hnd (18, 82) (by decide) (hh.1.trans hh.2.symm)
  have h129 (a : Fin 4) : ¬ (d 18 = a ∧ d 90 = a) := by
    intro hh
    exact hnd (18, 90) (by decide) (hh.1.trans hh.2.symm)
  have h130 (a : Fin 4) : ¬ (d 18 = a ∧ d 91 = a) := by
    intro hh
    exact hnd (18, 91) (by decide) (hh.1.trans hh.2.symm)
  have h131 (a : Fin 4) : ¬ (d 18 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (18, 93) (by decide) (hh.1.trans hh.2.symm)
  have h132 (a : Fin 4) : ¬ (d 19 = a ∧ d 26 = a) := by
    intro hh
    exact hnd (19, 26) (by decide) (hh.1.trans hh.2.symm)
  have h133 (a : Fin 4) : ¬ (d 19 = a ∧ d 48 = a) := by
    intro hh
    exact hnd (19, 48) (by decide) (hh.1.trans hh.2.symm)
  have h134 (a : Fin 4) : ¬ (d 19 = a ∧ d 50 = a) := by
    intro hh
    exact hnd (19, 50) (by decide) (hh.1.trans hh.2.symm)
  have h135 (a : Fin 4) : ¬ (d 20 = a ∧ d 32 = a) := by
    intro hh
    exact hnd (20, 32) (by decide) (hh.1.trans hh.2.symm)
  have h136 (a : Fin 4) : ¬ (d 20 = a ∧ d 47 = a) := by
    intro hh
    exact hnd (20, 47) (by decide) (hh.1.trans hh.2.symm)
  have h137 (a : Fin 4) : ¬ (d 20 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (20, 71) (by decide) (hh.1.trans hh.2.symm)
  have h138 (a : Fin 4) : ¬ (d 21 = a ∧ d 25 = a) := by
    intro hh
    exact hnd (21, 25) (by decide) (hh.1.trans hh.2.symm)
  have h139 (a : Fin 4) : ¬ (d 21 = a ∧ d 47 = a) := by
    intro hh
    exact hnd (21, 47) (by decide) (hh.1.trans hh.2.symm)
  have h140 (a : Fin 4) : ¬ (d 22 = a ∧ d 55 = a) := by
    intro hh
    exact hnd (22, 55) (by decide) (hh.1.trans hh.2.symm)
  have h141 (a : Fin 4) : ¬ (d 22 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (22, 66) (by decide) (hh.1.trans hh.2.symm)
  have h142 (a : Fin 4) : ¬ (d 22 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (22, 71) (by decide) (hh.1.trans hh.2.symm)
  have h143 (a : Fin 4) : ¬ (d 22 = a ∧ d 89 = a) := by
    intro hh
    exact hnd (22, 89) (by decide) (hh.1.trans hh.2.symm)
  have h144 (a : Fin 4) : ¬ (d 22 = a ∧ d 94 = a) := by
    intro hh
    exact hnd (22, 94) (by decide) (hh.1.trans hh.2.symm)
  have h145 (a : Fin 4) : ¬ (d 23 = a ∧ d 27 = a) := by
    intro hh
    exact hnd (23, 27) (by decide) (hh.1.trans hh.2.symm)
  have h146 (a : Fin 4) : ¬ (d 23 = a ∧ d 36 = a) := by
    intro hh
    exact hnd (23, 36) (by decide) (hh.1.trans hh.2.symm)
  have h147 (a : Fin 4) : ¬ (d 23 = a ∧ d 61 = a) := by
    intro hh
    exact hnd (23, 61) (by decide) (hh.1.trans hh.2.symm)
  have h148 (a : Fin 4) : ¬ (d 23 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (23, 93) (by decide) (hh.1.trans hh.2.symm)
  have h149 (a : Fin 4) : ¬ (d 24 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (24, 33) (by decide) (hh.1.trans hh.2.symm)
  have h150 (a : Fin 4) : ¬ (d 24 = a ∧ d 59 = a) := by
    intro hh
    exact hnd (24, 59) (by decide) (hh.1.trans hh.2.symm)
  have h151 (a : Fin 4) : ¬ (d 24 = a ∧ d 60 = a) := by
    intro hh
    exact hnd (24, 60) (by decide) (hh.1.trans hh.2.symm)
  have h152 (a : Fin 4) : ¬ (d 24 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (24, 66) (by decide) (hh.1.trans hh.2.symm)
  have h153 (a : Fin 4) : ¬ (d 24 = a ∧ d 95 = a) := by
    intro hh
    exact hnd (24, 95) (by decide) (hh.1.trans hh.2.symm)
  have h154 (a : Fin 4) : ¬ (d 24 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (24, 96) (by decide) (hh.1.trans hh.2.symm)
  have h155 (a : Fin 4) : ¬ (d 25 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (25, 66) (by decide) (hh.1.trans hh.2.symm)
  have h156 (a : Fin 4) : ¬ (d 25 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (25, 71) (by decide) (hh.1.trans hh.2.symm)
  have h157 (a : Fin 4) : ¬ (d 25 = a ∧ d 83 = a) := by
    intro hh
    exact hnd (25, 83) (by decide) (hh.1.trans hh.2.symm)
  have h158 (a : Fin 4) : ¬ (d 26 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (26, 33) (by decide) (hh.1.trans hh.2.symm)
  have h159 (a : Fin 4) : ¬ (d 26 = a ∧ d 44 = a) := by
    intro hh
    exact hnd (26, 44) (by decide) (hh.1.trans hh.2.symm)
  have h160 (a : Fin 4) : ¬ (d 26 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (26, 71) (by decide) (hh.1.trans hh.2.symm)
  have h161 (a : Fin 4) : ¬ (d 27 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (27, 33) (by decide) (hh.1.trans hh.2.symm)
  have h162 (a : Fin 4) : ¬ (d 27 = a ∧ d 62 = a) := by
    intro hh
    exact hnd (27, 62) (by decide) (hh.1.trans hh.2.symm)
  have h163 (a : Fin 4) : ¬ (d 27 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (27, 71) (by decide) (hh.1.trans hh.2.symm)
  have h164 (a : Fin 4) : ¬ (d 27 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (27, 93) (by decide) (hh.1.trans hh.2.symm)
  have h165 (a : Fin 4) : ¬ (d 28 = a ∧ d 69 = a) := by
    intro hh
    exact hnd (28, 69) (by decide) (hh.1.trans hh.2.symm)
  have h166 (a : Fin 4) : ¬ (d 28 = a ∧ d 100 = a) := by
    intro hh
    exact hnd (28, 100) (by decide) (hh.1.trans hh.2.symm)
  have h167 (a : Fin 4) : ¬ (d 29 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (29, 33) (by decide) (hh.1.trans hh.2.symm)
  have h168 (a : Fin 4) : ¬ (d 29 = a ∧ d 39 = a) := by
    intro hh
    exact hnd (29, 39) (by decide) (hh.1.trans hh.2.symm)
  have h169 (a : Fin 4) : ¬ (d 29 = a ∧ d 53 = a) := by
    intro hh
    exact hnd (29, 53) (by decide) (hh.1.trans hh.2.symm)
  have h170 (a : Fin 4) : ¬ (d 29 = a ∧ d 85 = a) := by
    intro hh
    exact hnd (29, 85) (by decide) (hh.1.trans hh.2.symm)
  have h171 (a : Fin 4) : ¬ (d 30 = a ∧ d 33 = a) := by
    intro hh
    exact hnd (30, 33) (by decide) (hh.1.trans hh.2.symm)
  have h172 (a : Fin 4) : ¬ (d 30 = a ∧ d 45 = a) := by
    intro hh
    exact hnd (30, 45) (by decide) (hh.1.trans hh.2.symm)
  have h173 (a : Fin 4) : ¬ (d 30 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (30, 66) (by decide) (hh.1.trans hh.2.symm)
  have h174 (a : Fin 4) : ¬ (d 30 = a ∧ d 72 = a) := by
    intro hh
    exact hnd (30, 72) (by decide) (hh.1.trans hh.2.symm)
  have h175 (a : Fin 4) : ¬ (d 30 = a ∧ d 80 = a) := by
    intro hh
    exact hnd (30, 80) (by decide) (hh.1.trans hh.2.symm)
  have h176 (a : Fin 4) : ¬ (d 30 = a ∧ d 85 = a) := by
    intro hh
    exact hnd (30, 85) (by decide) (hh.1.trans hh.2.symm)
  have h177 (a : Fin 4) : ¬ (d 30 = a ∧ d 98 = a) := by
    intro hh
    exact hnd (30, 98) (by decide) (hh.1.trans hh.2.symm)
  have h178 (a : Fin 4) : ¬ (d 31 = a ∧ d 39 = a) := by
    intro hh
    exact hnd (31, 39) (by decide) (hh.1.trans hh.2.symm)
  have h179 (a : Fin 4) : ¬ (d 31 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (31, 79) (by decide) (hh.1.trans hh.2.symm)
  have h180 (a : Fin 4) : ¬ (d 32 = a ∧ d 89 = a) := by
    intro hh
    exact hnd (32, 89) (by decide) (hh.1.trans hh.2.symm)
  have h181 (a : Fin 4) : ¬ (d 32 = a ∧ d 94 = a) := by
    intro hh
    exact hnd (32, 94) (by decide) (hh.1.trans hh.2.symm)
  have h182 (a : Fin 4) : ¬ (d 33 = a ∧ d 35 = a) := by
    intro hh
    exact hnd (33, 35) (by decide) (hh.1.trans hh.2.symm)
  have h183 (a : Fin 4) : ¬ (d 33 = a ∧ d 38 = a) := by
    intro hh
    exact hnd (33, 38) (by decide) (hh.1.trans hh.2.symm)
  have h184 (a : Fin 4) : ¬ (d 33 = a ∧ d 40 = a) := by
    intro hh
    exact hnd (33, 40) (by decide) (hh.1.trans hh.2.symm)
  have h185 (a : Fin 4) : ¬ (d 33 = a ∧ d 43 = a) := by
    intro hh
    exact hnd (33, 43) (by decide) (hh.1.trans hh.2.symm)
  have h186 (a : Fin 4) : ¬ (d 33 = a ∧ d 47 = a) := by
    intro hh
    exact hnd (33, 47) (by decide) (hh.1.trans hh.2.symm)
  have h187 (a : Fin 4) : ¬ (d 33 = a ∧ d 50 = a) := by
    intro hh
    exact hnd (33, 50) (by decide) (hh.1.trans hh.2.symm)
  have h188 (a : Fin 4) : ¬ (d 33 = a ∧ d 51 = a) := by
    intro hh
    exact hnd (33, 51) (by decide) (hh.1.trans hh.2.symm)
  have h189 (a : Fin 4) : ¬ (d 33 = a ∧ d 56 = a) := by
    intro hh
    exact hnd (33, 56) (by decide) (hh.1.trans hh.2.symm)
  have h190 (a : Fin 4) : ¬ (d 33 = a ∧ d 57 = a) := by
    intro hh
    exact hnd (33, 57) (by decide) (hh.1.trans hh.2.symm)
  have h191 (a : Fin 4) : ¬ (d 33 = a ∧ d 58 = a) := by
    intro hh
    exact hnd (33, 58) (by decide) (hh.1.trans hh.2.symm)
  have h192 (a : Fin 4) : ¬ (d 33 = a ∧ d 61 = a) := by
    intro hh
    exact hnd (33, 61) (by decide) (hh.1.trans hh.2.symm)
  have h193 (a : Fin 4) : ¬ (d 33 = a ∧ d 64 = a) := by
    intro hh
    exact hnd (33, 64) (by decide) (hh.1.trans hh.2.symm)
  have h194 (a : Fin 4) : ¬ (d 33 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (33, 66) (by decide) (hh.1.trans hh.2.symm)
  have h195 (a : Fin 4) : ¬ (d 33 = a ∧ d 68 = a) := by
    intro hh
    exact hnd (33, 68) (by decide) (hh.1.trans hh.2.symm)
  have h196 (a : Fin 4) : ¬ (d 33 = a ∧ d 69 = a) := by
    intro hh
    exact hnd (33, 69) (by decide) (hh.1.trans hh.2.symm)
  have h197 (a : Fin 4) : ¬ (d 33 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (33, 71) (by decide) (hh.1.trans hh.2.symm)
  have h198 (a : Fin 4) : ¬ (d 33 = a ∧ d 74 = a) := by
    intro hh
    exact hnd (33, 74) (by decide) (hh.1.trans hh.2.symm)
  have h199 (a : Fin 4) : ¬ (d 33 = a ∧ d 76 = a) := by
    intro hh
    exact hnd (33, 76) (by decide) (hh.1.trans hh.2.symm)
  have h200 (a : Fin 4) : ¬ (d 33 = a ∧ d 77 = a) := by
    intro hh
    exact hnd (33, 77) (by decide) (hh.1.trans hh.2.symm)
  have h201 (a : Fin 4) : ¬ (d 33 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (33, 79) (by decide) (hh.1.trans hh.2.symm)
  have h202 (a : Fin 4) : ¬ (d 33 = a ∧ d 86 = a) := by
    intro hh
    exact hnd (33, 86) (by decide) (hh.1.trans hh.2.symm)
  have h203 (a : Fin 4) : ¬ (d 33 = a ∧ d 87 = a) := by
    intro hh
    exact hnd (33, 87) (by decide) (hh.1.trans hh.2.symm)
  have h204 (a : Fin 4) : ¬ (d 33 = a ∧ d 89 = a) := by
    intro hh
    exact hnd (33, 89) (by decide) (hh.1.trans hh.2.symm)
  have h205 (a : Fin 4) : ¬ (d 33 = a ∧ d 90 = a) := by
    intro hh
    exact hnd (33, 90) (by decide) (hh.1.trans hh.2.symm)
  have h206 (a : Fin 4) : ¬ (d 33 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (33, 93) (by decide) (hh.1.trans hh.2.symm)
  have h207 (a : Fin 4) : ¬ (d 33 = a ∧ d 94 = a) := by
    intro hh
    exact hnd (33, 94) (by decide) (hh.1.trans hh.2.symm)
  have h208 (a : Fin 4) : ¬ (d 33 = a ∧ d 95 = a) := by
    intro hh
    exact hnd (33, 95) (by decide) (hh.1.trans hh.2.symm)
  have h209 (a : Fin 4) : ¬ (d 33 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (33, 96) (by decide) (hh.1.trans hh.2.symm)
  have h210 (a : Fin 4) : ¬ (d 34 = a ∧ d 42 = a) := by
    intro hh
    exact hnd (34, 42) (by decide) (hh.1.trans hh.2.symm)
  have h211 (a : Fin 4) : ¬ (d 34 = a ∧ d 77 = a) := by
    intro hh
    exact hnd (34, 77) (by decide) (hh.1.trans hh.2.symm)
  have h212 (a : Fin 4) : ¬ (d 35 = a ∧ d 86 = a) := by
    intro hh
    exact hnd (35, 86) (by decide) (hh.1.trans hh.2.symm)
  have h213 (a : Fin 4) : ¬ (d 35 = a ∧ d 87 = a) := by
    intro hh
    exact hnd (35, 87) (by decide) (hh.1.trans hh.2.symm)
  have h214 (a : Fin 4) : ¬ (d 36 = a ∧ d 58 = a) := by
    intro hh
    exact hnd (36, 58) (by decide) (hh.1.trans hh.2.symm)
  have h215 (a : Fin 4) : ¬ (d 36 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (36, 71) (by decide) (hh.1.trans hh.2.symm)
  have h216 (a : Fin 4) : ¬ (d 36 = a ∧ d 93 = a) := by
    intro hh
    exact hnd (36, 93) (by decide) (hh.1.trans hh.2.symm)
  have h217 (a : Fin 4) : ¬ (d 36 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (36, 96) (by decide) (hh.1.trans hh.2.symm)
  have h218 (a : Fin 4) : ¬ (d 38 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (38, 66) (by decide) (hh.1.trans hh.2.symm)
  have h219 (a : Fin 4) : ¬ (d 39 = a ∧ d 63 = a) := by
    intro hh
    exact hnd (39, 63) (by decide) (hh.1.trans hh.2.symm)
  have h220 (a : Fin 4) : ¬ (d 39 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (39, 66) (by decide) (hh.1.trans hh.2.symm)
  have h221 (a : Fin 4) : ¬ (d 39 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (39, 71) (by decide) (hh.1.trans hh.2.symm)
  have h222 (a : Fin 4) : ¬ (d 39 = a ∧ d 80 = a) := by
    intro hh
    exact hnd (39, 80) (by decide) (hh.1.trans hh.2.symm)
  have h223 (a : Fin 4) : ¬ (d 39 = a ∧ d 81 = a) := by
    intro hh
    exact hnd (39, 81) (by decide) (hh.1.trans hh.2.symm)
  have h224 (a : Fin 4) : ¬ (d 39 = a ∧ d 99 = a) := by
    intro hh
    exact hnd (39, 99) (by decide) (hh.1.trans hh.2.symm)
  have h225 (a : Fin 4) : ¬ (d 40 = a ∧ d 49 = a) := by
    intro hh
    exact hnd (40, 49) (by decide) (hh.1.trans hh.2.symm)
  have h226 (a : Fin 4) : ¬ (d 40 = a ∧ d 56 = a) := by
    intro hh
    exact hnd (40, 56) (by decide) (hh.1.trans hh.2.symm)
  have h227 (a : Fin 4) : ¬ (d 40 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (40, 66) (by decide) (hh.1.trans hh.2.symm)
  have h228 (a : Fin 4) : ¬ (d 41 = a ∧ d 84 = a) := by
    intro hh
    exact hnd (41, 84) (by decide) (hh.1.trans hh.2.symm)
  have h229 (a : Fin 4) : ¬ (d 41 = a ∧ d 97 = a) := by
    intro hh
    exact hnd (41, 97) (by decide) (hh.1.trans hh.2.symm)
  have h230 (a : Fin 4) : ¬ (d 42 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (42, 71) (by decide) (hh.1.trans hh.2.symm)
  have h231 (a : Fin 4) : ¬ (d 42 = a ∧ d 74 = a) := by
    intro hh
    exact hnd (42, 74) (by decide) (hh.1.trans hh.2.symm)
  have h232 (a : Fin 4) : ¬ (d 43 = a ∧ d 51 = a) := by
    intro hh
    exact hnd (43, 51) (by decide) (hh.1.trans hh.2.symm)
  have h233 (a : Fin 4) : ¬ (d 43 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (43, 71) (by decide) (hh.1.trans hh.2.symm)
  have h234 (a : Fin 4) : ¬ (d 43 = a ∧ d 82 = a) := by
    intro hh
    exact hnd (43, 82) (by decide) (hh.1.trans hh.2.symm)
  have h235 (a : Fin 4) : ¬ (d 44 = a ∧ d 83 = a) := by
    intro hh
    exact hnd (44, 83) (by decide) (hh.1.trans hh.2.symm)
  have h236 (a : Fin 4) : ¬ (d 45 = a ∧ d 52 = a) := by
    intro hh
    exact hnd (45, 52) (by decide) (hh.1.trans hh.2.symm)
  have h237 (a : Fin 4) : ¬ (d 45 = a ∧ d 65 = a) := by
    intro hh
    exact hnd (45, 65) (by decide) (hh.1.trans hh.2.symm)
  have h238 (a : Fin 4) : ¬ (d 45 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (45, 71) (by decide) (hh.1.trans hh.2.symm)
  have h239 (a : Fin 4) : ¬ (d 46 = a ∧ d 54 = a) := by
    intro hh
    exact hnd (46, 54) (by decide) (hh.1.trans hh.2.symm)
  have h240 (a : Fin 4) : ¬ (d 46 = a ∧ d 58 = a) := by
    intro hh
    exact hnd (46, 58) (by decide) (hh.1.trans hh.2.symm)
  have h241 (a : Fin 4) : ¬ (d 46 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (46, 96) (by decide) (hh.1.trans hh.2.symm)
  have h242 (a : Fin 4) : ¬ (d 47 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (47, 71) (by decide) (hh.1.trans hh.2.symm)
  have h243 (a : Fin 4) : ¬ (d 48 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (48, 71) (by decide) (hh.1.trans hh.2.symm)
  have h244 (a : Fin 4) : ¬ (d 49 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (49, 66) (by decide) (hh.1.trans hh.2.symm)
  have h245 (a : Fin 4) : ¬ (d 49 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (49, 71) (by decide) (hh.1.trans hh.2.symm)
  have h246 (a : Fin 4) : ¬ (d 51 = a ∧ d 73 = a) := by
    intro hh
    exact hnd (51, 73) (by decide) (hh.1.trans hh.2.symm)
  have h247 (a : Fin 4) : ¬ (d 54 = a ∧ d 57 = a) := by
    intro hh
    exact hnd (54, 57) (by decide) (hh.1.trans hh.2.symm)
  have h248 (a : Fin 4) : ¬ (d 54 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (54, 66) (by decide) (hh.1.trans hh.2.symm)
  have h249 (a : Fin 4) : ¬ (d 54 = a ∧ d 68 = a) := by
    intro hh
    exact hnd (54, 68) (by decide) (hh.1.trans hh.2.symm)
  have h250 (a : Fin 4) : ¬ (d 54 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (54, 71) (by decide) (hh.1.trans hh.2.symm)
  have h251 (a : Fin 4) : ¬ (d 55 = a ∧ d 57 = a) := by
    intro hh
    exact hnd (55, 57) (by decide) (hh.1.trans hh.2.symm)
  have h252 (a : Fin 4) : ¬ (d 55 = a ∧ d 68 = a) := by
    intro hh
    exact hnd (55, 68) (by decide) (hh.1.trans hh.2.symm)
  have h253 (a : Fin 4) : ¬ (d 56 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (56, 71) (by decide) (hh.1.trans hh.2.symm)
  have h254 (a : Fin 4) : ¬ (d 57 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (57, 66) (by decide) (hh.1.trans hh.2.symm)
  have h255 (a : Fin 4) : ¬ (d 58 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (58, 66) (by decide) (hh.1.trans hh.2.symm)
  have h256 (a : Fin 4) : ¬ (d 59 = a ∧ d 64 = a) := by
    intro hh
    exact hnd (59, 64) (by decide) (hh.1.trans hh.2.symm)
  have h257 (a : Fin 4) : ¬ (d 59 = a ∧ d 92 = a) := by
    intro hh
    exact hnd (59, 92) (by decide) (hh.1.trans hh.2.symm)
  have h258 (a : Fin 4) : ¬ (d 60 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (60, 66) (by decide) (hh.1.trans hh.2.symm)
  have h259 (a : Fin 4) : ¬ (d 60 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (60, 71) (by decide) (hh.1.trans hh.2.symm)
  have h260 (a : Fin 4) : ¬ (d 61 = a ∧ d 64 = a) := by
    intro hh
    exact hnd (61, 64) (by decide) (hh.1.trans hh.2.symm)
  have h261 (a : Fin 4) : ¬ (d 61 = a ∧ d 66 = a) := by
    intro hh
    exact hnd (61, 66) (by decide) (hh.1.trans hh.2.symm)
  have h262 (a : Fin 4) : ¬ (d 61 = a ∧ d 92 = a) := by
    intro hh
    exact hnd (61, 92) (by decide) (hh.1.trans hh.2.symm)
  have h263 (a : Fin 4) : ¬ (d 62 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (62, 71) (by decide) (hh.1.trans hh.2.symm)
  have h264 (a : Fin 4) : ¬ (d 63 = a ∧ d 76 = a) := by
    intro hh
    exact hnd (63, 76) (by decide) (hh.1.trans hh.2.symm)
  have h265 (a : Fin 4) : ¬ (d 64 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (64, 71) (by decide) (hh.1.trans hh.2.symm)
  have h266 (a : Fin 4) : ¬ (d 66 = a ∧ d 69 = a) := by
    intro hh
    exact hnd (66, 69) (by decide) (hh.1.trans hh.2.symm)
  have h267 (a : Fin 4) : ¬ (d 66 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (66, 71) (by decide) (hh.1.trans hh.2.symm)
  have h268 (a : Fin 4) : ¬ (d 66 = a ∧ d 76 = a) := by
    intro hh
    exact hnd (66, 76) (by decide) (hh.1.trans hh.2.symm)
  have h269 (a : Fin 4) : ¬ (d 66 = a ∧ d 89 = a) := by
    intro hh
    exact hnd (66, 89) (by decide) (hh.1.trans hh.2.symm)
  have h270 (a : Fin 4) : ¬ (d 66 = a ∧ d 92 = a) := by
    intro hh
    exact hnd (66, 92) (by decide) (hh.1.trans hh.2.symm)
  have h271 (a : Fin 4) : ¬ (d 66 = a ∧ d 100 = a) := by
    intro hh
    exact hnd (66, 100) (by decide) (hh.1.trans hh.2.symm)
  have h272 (a : Fin 4) : ¬ (d 67 = a ∧ d 70 = a) := by
    intro hh
    exact hnd (67, 70) (by decide) (hh.1.trans hh.2.symm)
  have h273 (a : Fin 4) : ¬ (d 67 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (67, 71) (by decide) (hh.1.trans hh.2.symm)
  have h274 (a : Fin 4) : ¬ (d 68 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (68, 71) (by decide) (hh.1.trans hh.2.symm)
  have h275 (a : Fin 4) : ¬ (d 70 = a ∧ d 71 = a) := by
    intro hh
    exact hnd (70, 71) (by decide) (hh.1.trans hh.2.symm)
  have h276 (a : Fin 4) : ¬ (d 71 = a ∧ d 74 = a) := by
    intro hh
    exact hnd (71, 74) (by decide) (hh.1.trans hh.2.symm)
  have h277 (a : Fin 4) : ¬ (d 71 = a ∧ d 78 = a) := by
    intro hh
    exact hnd (71, 78) (by decide) (hh.1.trans hh.2.symm)
  have h278 (a : Fin 4) : ¬ (d 71 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (71, 79) (by decide) (hh.1.trans hh.2.symm)
  have h279 (a : Fin 4) : ¬ (d 71 = a ∧ d 82 = a) := by
    intro hh
    exact hnd (71, 82) (by decide) (hh.1.trans hh.2.symm)
  have h280 (a : Fin 4) : ¬ (d 71 = a ∧ d 91 = a) := by
    intro hh
    exact hnd (71, 91) (by decide) (hh.1.trans hh.2.symm)
  have h281 (a : Fin 4) : ¬ (d 71 = a ∧ d 92 = a) := by
    intro hh
    exact hnd (71, 92) (by decide) (hh.1.trans hh.2.symm)
  have h282 (a : Fin 4) : ¬ (d 71 = a ∧ d 94 = a) := by
    intro hh
    exact hnd (71, 94) (by decide) (hh.1.trans hh.2.symm)
  have h283 (a : Fin 4) : ¬ (d 71 = a ∧ d 95 = a) := by
    intro hh
    exact hnd (71, 95) (by decide) (hh.1.trans hh.2.symm)
  have h284 (a : Fin 4) : ¬ (d 71 = a ∧ d 96 = a) := by
    intro hh
    exact hnd (71, 96) (by decide) (hh.1.trans hh.2.symm)
  have h285 (a : Fin 4) : ¬ (d 71 = a ∧ d 100 = a) := by
    intro hh
    exact hnd (71, 100) (by decide) (hh.1.trans hh.2.symm)
  have h286 (a : Fin 4) : ¬ (d 72 = a ∧ d 78 = a) := by
    intro hh
    exact hnd (72, 78) (by decide) (hh.1.trans hh.2.symm)
  have h287 (a : Fin 4) : ¬ (d 72 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (72, 79) (by decide) (hh.1.trans hh.2.symm)
  have h288 (a : Fin 4) : ¬ (d 73 = a ∧ d 74 = a) := by
    intro hh
    exact hnd (73, 74) (by decide) (hh.1.trans hh.2.symm)
  have h289 (a : Fin 4) : ¬ (d 73 = a ∧ d 82 = a) := by
    intro hh
    exact hnd (73, 82) (by decide) (hh.1.trans hh.2.symm)
  have h290 (a : Fin 4) : ¬ (d 74 = a ∧ d 77 = a) := by
    intro hh
    exact hnd (74, 77) (by decide) (hh.1.trans hh.2.symm)
  have h291 (a : Fin 4) : ¬ (d 75 = a ∧ d 79 = a) := by
    intro hh
    exact hnd (75, 79) (by decide) (hh.1.trans hh.2.symm)
  have h292 (a : Fin 4) : ¬ (d 75 = a ∧ d 81 = a) := by
    intro hh
    exact hnd (75, 81) (by decide) (hh.1.trans hh.2.symm)
  have h293 (a : Fin 4) : ¬ (d 75 = a ∧ d 98 = a) := by
    intro hh
    exact hnd (75, 98) (by decide) (hh.1.trans hh.2.symm)
  have h294 (a : Fin 4) : ¬ (d 76 = a ∧ d 78 = a) := by
    intro hh
    exact hnd (76, 78) (by decide) (hh.1.trans hh.2.symm)
  have h295 (a : Fin 4) : ¬ (d 76 = a ∧ d 88 = a) := by
    intro hh
    exact hnd (76, 88) (by decide) (hh.1.trans hh.2.symm)
  have h296 (a : Fin 4) : ¬ (d 78 = a ∧ d 80 = a) := by
    intro hh
    exact hnd (78, 80) (by decide) (hh.1.trans hh.2.symm)
  have h297 (a : Fin 4) : ¬ (d 79 = a ∧ d 83 = a) := by
    intro hh
    exact hnd (79, 83) (by decide) (hh.1.trans hh.2.symm)
  have h298 (a : Fin 4) : ¬ (d 79 = a ∧ d 88 = a) := by
    intro hh
    exact hnd (79, 88) (by decide) (hh.1.trans hh.2.symm)
  have hu0 : ¬ (d 1 ≠ 0) := not_not_intro hd0
  have hu1 : ¬ (d 18 ≠ 1) := not_not_intro hd1
  have hu2 : ¬ (d 33 ≠ 2) := not_not_intro hd2
  have hu3 : ¬ (d 71 ≠ 3) := not_not_intro hd3
  have H := threshold101_colour_core_fixed
    (d 0 = 0) (d 0 = 1) (d 0 = 2) (d 0 = 3) (d 1 = 0) (d 1 = 1) (d 1 = 2) (d 1 = 3)
    (d 2 = 0) (d 2 = 1) (d 2 = 2) (d 2 = 3) (d 3 = 0) (d 3 = 1) (d 3 = 2) (d 3 = 3)
    (d 4 = 0) (d 4 = 1) (d 4 = 2) (d 4 = 3) (d 5 = 0) (d 5 = 1) (d 5 = 2) (d 5 = 3)
    (d 6 = 0) (d 6 = 1) (d 6 = 2) (d 6 = 3) (d 7 = 0) (d 7 = 1) (d 7 = 2) (d 7 = 3)
    (d 8 = 0) (d 8 = 1) (d 8 = 2) (d 8 = 3) (d 9 = 0) (d 9 = 1) (d 9 = 2) (d 9 = 3)
    (d 10 = 0) (d 10 = 1) (d 10 = 2) (d 10 = 3) (d 11 = 0) (d 11 = 1) (d 11 = 2) (d 11 = 3)
    (d 12 = 0) (d 12 = 1) (d 12 = 2) (d 12 = 3) (d 13 = 0) (d 13 = 1) (d 13 = 2) (d 13 = 3)
    (d 14 = 0) (d 14 = 1) (d 14 = 2) (d 14 = 3) (d 15 = 0) (d 15 = 1) (d 15 = 2) (d 15 = 3)
    (d 16 = 0) (d 16 = 1) (d 16 = 2) (d 16 = 3) (d 17 = 0) (d 17 = 1) (d 17 = 2) (d 17 = 3)
    (d 18 = 0) (d 18 = 1) (d 18 = 2) (d 18 = 3) (d 19 = 0) (d 19 = 1) (d 19 = 2) (d 19 = 3)
    (d 20 = 0) (d 20 = 1) (d 20 = 2) (d 20 = 3) (d 21 = 0) (d 21 = 1) (d 21 = 2) (d 21 = 3)
    (d 22 = 0) (d 22 = 1) (d 22 = 2) (d 22 = 3) (d 23 = 0) (d 23 = 1) (d 23 = 2) (d 23 = 3)
    (d 24 = 0) (d 24 = 1) (d 24 = 2) (d 24 = 3) (d 25 = 0) (d 25 = 1) (d 25 = 2) (d 25 = 3)
    (d 26 = 0) (d 26 = 1) (d 26 = 2) (d 26 = 3) (d 27 = 0) (d 27 = 1) (d 27 = 2) (d 27 = 3)
    (d 28 = 0) (d 28 = 1) (d 28 = 2) (d 28 = 3) (d 29 = 0) (d 29 = 1) (d 29 = 2) (d 29 = 3)
    (d 30 = 0) (d 30 = 1) (d 30 = 2) (d 30 = 3) (d 31 = 0) (d 31 = 1) (d 31 = 2) (d 31 = 3)
    (d 32 = 0) (d 32 = 1) (d 32 = 2) (d 32 = 3) (d 33 = 0) (d 33 = 1) (d 33 = 2) (d 33 = 3)
    (d 34 = 0) (d 34 = 1) (d 34 = 2) (d 34 = 3) (d 35 = 0) (d 35 = 1) (d 35 = 2) (d 35 = 3)
    (d 36 = 0) (d 36 = 1) (d 36 = 2) (d 36 = 3) (d 37 = 0) (d 37 = 1) (d 37 = 2) (d 37 = 3)
    (d 38 = 0) (d 38 = 1) (d 38 = 2) (d 38 = 3) (d 39 = 0) (d 39 = 1) (d 39 = 2) (d 39 = 3)
    (d 40 = 0) (d 40 = 1) (d 40 = 2) (d 40 = 3) (d 41 = 0) (d 41 = 1) (d 41 = 2) (d 41 = 3)
    (d 42 = 0) (d 42 = 1) (d 42 = 2) (d 42 = 3) (d 43 = 0) (d 43 = 1) (d 43 = 2) (d 43 = 3)
    (d 44 = 0) (d 44 = 1) (d 44 = 2) (d 44 = 3) (d 45 = 0) (d 45 = 1) (d 45 = 2) (d 45 = 3)
    (d 46 = 0) (d 46 = 1) (d 46 = 2) (d 46 = 3) (d 47 = 0) (d 47 = 1) (d 47 = 2) (d 47 = 3)
    (d 48 = 0) (d 48 = 1) (d 48 = 2) (d 48 = 3) (d 49 = 0) (d 49 = 1) (d 49 = 2) (d 49 = 3)
    (d 50 = 0) (d 50 = 1) (d 50 = 2) (d 50 = 3) (d 51 = 0) (d 51 = 1) (d 51 = 2) (d 51 = 3)
    (d 52 = 0) (d 52 = 1) (d 52 = 2) (d 52 = 3) (d 53 = 0) (d 53 = 1) (d 53 = 2) (d 53 = 3)
    (d 54 = 0) (d 54 = 1) (d 54 = 2) (d 54 = 3) (d 55 = 0) (d 55 = 1) (d 55 = 2) (d 55 = 3)
    (d 56 = 0) (d 56 = 1) (d 56 = 2) (d 56 = 3) (d 57 = 0) (d 57 = 1) (d 57 = 2) (d 57 = 3)
    (d 58 = 0) (d 58 = 1) (d 58 = 2) (d 58 = 3) (d 59 = 0) (d 59 = 1) (d 59 = 2) (d 59 = 3)
    (d 60 = 0) (d 60 = 1) (d 60 = 2) (d 60 = 3) (d 61 = 0) (d 61 = 1) (d 61 = 2) (d 61 = 3)
    (d 62 = 0) (d 62 = 1) (d 62 = 2) (d 62 = 3) (d 63 = 0) (d 63 = 1) (d 63 = 2) (d 63 = 3)
    (d 64 = 0) (d 64 = 1) (d 64 = 2) (d 64 = 3) (d 65 = 0) (d 65 = 1) (d 65 = 2) (d 65 = 3)
    (d 66 = 0) (d 66 = 1) (d 66 = 2) (d 66 = 3) (d 67 = 0) (d 67 = 1) (d 67 = 2) (d 67 = 3)
    (d 68 = 0) (d 68 = 1) (d 68 = 2) (d 68 = 3) (d 69 = 0) (d 69 = 1) (d 69 = 2) (d 69 = 3)
    (d 70 = 0) (d 70 = 1) (d 70 = 2) (d 70 = 3) (d 71 = 0) (d 71 = 1) (d 71 = 2) (d 71 = 3)
    (d 72 = 0) (d 72 = 1) (d 72 = 2) (d 72 = 3) (d 73 = 0) (d 73 = 1) (d 73 = 2) (d 73 = 3)
    (d 74 = 0) (d 74 = 1) (d 74 = 2) (d 74 = 3) (d 75 = 0) (d 75 = 1) (d 75 = 2) (d 75 = 3)
    (d 76 = 0) (d 76 = 1) (d 76 = 2) (d 76 = 3) (d 77 = 0) (d 77 = 1) (d 77 = 2) (d 77 = 3)
    (d 78 = 0) (d 78 = 1) (d 78 = 2) (d 78 = 3) (d 79 = 0) (d 79 = 1) (d 79 = 2) (d 79 = 3)
    (d 80 = 0) (d 80 = 1) (d 80 = 2) (d 80 = 3) (d 81 = 0) (d 81 = 1) (d 81 = 2) (d 81 = 3)
    (d 82 = 0) (d 82 = 1) (d 82 = 2) (d 82 = 3) (d 83 = 0) (d 83 = 1) (d 83 = 2) (d 83 = 3)
    (d 84 = 0) (d 84 = 1) (d 84 = 2) (d 84 = 3) (d 85 = 0) (d 85 = 1) (d 85 = 2) (d 85 = 3)
    (d 86 = 0) (d 86 = 1) (d 86 = 2) (d 86 = 3) (d 87 = 0) (d 87 = 1) (d 87 = 2) (d 87 = 3)
    (d 88 = 0) (d 88 = 1) (d 88 = 2) (d 88 = 3) (d 89 = 0) (d 89 = 1) (d 89 = 2) (d 89 = 3)
    (d 90 = 0) (d 90 = 1) (d 90 = 2) (d 90 = 3) (d 91 = 0) (d 91 = 1) (d 91 = 2) (d 91 = 3)
    (d 92 = 0) (d 92 = 1) (d 92 = 2) (d 92 = 3) (d 93 = 0) (d 93 = 1) (d 93 = 2) (d 93 = 3)
    (d 94 = 0) (d 94 = 1) (d 94 = 2) (d 94 = 3) (d 95 = 0) (d 95 = 1) (d 95 = 2) (d 95 = 3)
    (d 96 = 0) (d 96 = 1) (d 96 = 2) (d 96 = 3) (d 97 = 0) (d 97 = 1) (d 97 = 2) (d 97 = 3)
    (d 98 = 0) (d 98 = 1) (d 98 = 2) (d 98 = 3) (d 99 = 0) (d 99 = 1) (d 99 = 2) (d 99 = 3)
    (d 100 = 0) (d 100 = 1) (d 100 = 2) (d 100 = 3)
  simp only [hu0, hu1, hu2, hu3, hcover, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196, h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242, h243, h244, h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279, h280, h281, h282, h283, h284, h285, h286, h287, h288, h289, h290, h291, h292, h293, h294, h295, h296, h297, h298, false_or, or_false, and_false, false_and] at H
