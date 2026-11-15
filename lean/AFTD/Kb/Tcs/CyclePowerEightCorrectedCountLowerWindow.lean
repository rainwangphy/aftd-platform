import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.G

/-!
# cycle_power_eight_corrected_count_lower_window

Topic: combinatorics   Node: 76d984b338ac

Provenance: helper lemma. Finite-window ladder for thread RT-1 and arXiv:2610.15635; the compressed, externally verified CNF/LRAT and semantic variable mapping are recorded in the evidence experiments.

In every zero-phase defective half model of exponent three, the corrected lower count at v is at most its value at v+4.
-/

namespace RT1Lower895
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem rt1_bridge_base895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) :
    (∀ p, y p 0 = true ∧ y p 7 = true) ∧
    (∀ p, (y p 1 = true → y p 7 = true) ∧ (y p 2 = true → y p 6 = true) ∧
          (y p 3 = true → y p 7 = true) ∧ (y p 4 = true → y p 0 = true) ∧
          (y p 5 = true → y p 1 = true) ∧ (y p 6 = true → y p 0 = true)) := by
  constructor
  · intro p
    have hex := h.2.1 0 (by omega) p
    simp only [pow_zero, Finset.sum_range_one, Nat.cast_zero, sub_zero, zero_add] at hex
    cases h0 : y p 0 <;> cases h7 : y p 7 <;> simp_all
  · intro p
    have h1 := cycle_power_dyadic_tight_class_parent 3 1 (by omega) (by omega) (y p) (h.1 p)
    have h2 := cycle_power_dyadic_tight_class_parent 3 2 (by omega) (by omega) (y p) (h.1 p)
    have a := (h1 1 (by norm_num)).2 (by norm_num)
    have b := (h2 2 (by norm_num)).2 (by norm_num)
    have c := (h2 3 (by norm_num)).2 (by norm_num)
    have d := (h2 0 (by norm_num)).1 (by norm_num)
    have f := (h2 1 (by norm_num)).1 (by norm_num)
    have g := (h1 0 (by norm_num)).1 (by norm_num)
    norm_num at a b c d f g
    exact ⟨a,b,c,d,f,g⟩

lrat_proof rt1_upper_cert895
  "p cnf 195 300\n1 0\n2 0\n4 -3 0\n7 0\n10 0\n12 -11 0\n15 0\n18 -17 0\n-20 16 0\n21 0\n22 0\n25 -24 0\n-28 23 0\n29 0\n30 0\n-32 33 0\n-36 31 0\n37 0\n38 0\n-40 41 0\n39 -44 0\n45 0\n46 0\n49 -48 0\n-52 47 0\n53 0\n54 0\n57 -56 0\n-60 55 0\n61 0\n62 0\n-64 65 0\n-68 63 0\n69 0\n70 0\n-72 73 0\n71 -76 0\n77 0\n78 -81 0\n82 0\n-84 83 0\n85 0\n-87 86 0\n88 0\n19 24 31 105 -69 0\n19 -63 24 31 -69 0\n19 -56 24 31 -69 0\n-50 19 24 31 -69 0\n-111 19 24 31 -69 0\n-63 105 31 24 -69 0\n-56 105 31 24 -69 0\n-50 105 31 24 -69 0\n-111 105 31 24 -69 0\n19 -63 31 105 -69 0\n-56 105 31 19 -69 0\n-50 105 31 19 -69 0\n-111 19 31 105 -69 0\n-56 -50 31 105 -69 0\n-56 -111 31 105 -69 0\n19 -63 24 105 -69 0\n19 -56 24 105 -69 0\n-50 105 19 24 -69 0\n-63 -56 24 19 -69 0\n-50 -63 19 24 -69 0\n19 -111 -63 24 -69 0\n-111 -50 19 24 -69 0\n-63 -56 24 105 -69 0\n-50 24 -63 105 -69 0\n-63 -111 24 105 -69 0\n-50 -56 24 105 -69 0\n-111 -56 105 24 -69 0\n-50 105 24 -111 -69 0\n-23 -17 -4 -29 -1 0\n-23 -13 -4 -29 -1 0\n-8 -23 -4 -29 -1 0\n-6 -23 -4 -29 -1 0\n-13 -17 -4 -29 -1 0\n-8 -17 -4 -29 -1 0\n-14 -24 -31 -37 -2 0\n-31 -9 -24 -37 -2 0\n-5 -31 -24 -37 -2 0\n-9 -31 -19 -37 -2 0\n-5 -31 -19 -37 -2 0\n-9 -14 -31 -37 -2 0\n-5 -14 -31 -37 -2 0\n-105 -14 -31 -37 -2 0\n-105 -9 -31 -37 -2 0\n-105 -5 -31 -37 -2 0\n-47 -34 -12 -53 -7 0\n-27 -47 -12 -53 -7 0\n-55 -48 -42 -61 -10 0\n-55 -42 -18 -61 -10 0\n-35 -55 -18 -61 -10 0\n-28 -48 -42 -61 -10 0\n-42 -48 -18 -61 -10 0\n-28 -48 -35 -61 -10 0\n-35 -48 -18 -61 -10 0\n-25 -56 -63 -69 -15 0\n-50 -63 -25 -69 -15 0\n111 56 43 63 36 50 0\n25 111 63 56 43 36 0\n111 25 63 43 36 50 0\n111 25 56 50 43 36 0\n-64 -44 -71 -77 -22 0\n-58 -44 -71 -77 -22 0\n-58 -33 -71 -77 -22 0\n-51 -44 -71 -77 -22 0\n-51 -33 -71 -77 -22 0\n-44 -33 -71 -77 -22 0\n-51 -64 -44 -77 -22 0\n44 33 58 51 64 115 0\n-66 -78 -52 -82 -30 0\n-41 -66 -78 -82 -30 0\n66 59 41 52 72 119 0\n-83 -74 -60 -85 -38 0\n-83 -74 -49 -85 -38 0\n-67 -83 -49 -85 -38 0\n-79 -60 -74 -85 -38 0\n-86 -80 -57 -88 -46 0\n-75 -86 -57 -88 -46 0\n-68 -86 -57 -88 -46 0\n121 122 124 123 125 120 0\n-120 32 0\n-121 26 0\n-122 17 0\n-123 13 0\n-124 8 0\n-125 6 0\n128 126 127 129 130 131 0\n-126 64 0\n126 -64 -61 0\n-127 55 0\n-127 58 0\n-128 51 0\n-129 42 0\n-129 44 0\n-130 35 0\n-130 33 0\n-131 28 0\n132 135 133 137 134 136 0\n-132 72 0\n-133 63 0\n-133 66 0\n-134 56 0\n-135 50 0\n-136 43 0\n-136 41 0\n-137 36 0\n137 -36 -30 0\n138 140 139 142 141 0\n-138 34 0\n-139 23 0\n-140 20 0\n-141 13 0\n-142 8 0\n143 144 146 145 147 0\n-143 42 0\n-144 35 0\n-145 24 0\n-145 28 0\n-146 19 0\n-147 14 0\n149 152 151 150 148 0\n-148 58 0\n-149 51 0\n-150 40 0\n-150 44 0\n-151 34 0\n-151 33 0\n-152 27 0\n153 156 154 155 157 0\n-153 74 0\n-154 63 0\n-154 67 0\n-155 56 0\n-155 60 0\n-156 50 0\n-157 43 0\n159 158 161 162 160 0\n-158 80 0\n-159 75 0\n-160 64 0\n-160 68 0\n-161 58 0\n-162 51 0\n165 163 164 0\n-163 9 0\n-164 5 0\n3 -165 0\n168 167 166 0\n-166 28 0\n-167 16 0\n-167 18 0\n11 -168 0\n170 171 169 0\n-169 36 0\n-170 23 0\n-171 17 0\n172 173 174 0\n-172 44 0\n-173 31 0\n-173 33 0\n-174 24 0\n174 -24 -22 0\n175 177 176 0\n-175 52 0\n-176 41 0\n-177 32 0\n179 178 180 0\n-178 60 0\n-179 47 0\n-179 49 0\n-180 40 0\n183 182 181 0\n-181 68 0\n-182 57 0\n-183 48 0\n184 185 186 0\n76 -184 0\n-185 63 0\n-186 56 0\n186 -56 -54 0\n187 188 189 0\n-187 81 0\n-188 71 0\n-188 73 0\n188 -73 -71 0\n-189 64 0\n189 -64 -62 0\n191 190 192 0\n-190 84 0\n-191 78 0\n-192 72 0\n192 -72 -70 0\n193 194 195 0\n-193 87 0\n-194 83 0\n-195 79 0\n-90 -89 0\n89 -25 -21 0\n-16 90 -15 0\n-91 -92 0\n91 92 0\n33 -91 0\n-33 91 -29 0\n-92 23 0\n92 -23 -22 0\n-93 -94 0\n-41 93 -37 0\n94 -31 -30 0\n-95 -96 0\n96 95 0\n57 -95 0\n-57 95 -53 0\n-96 47 0\n96 -47 -46 0\n-97 -98 0\n-65 97 -61 0\n98 -55 -54 0\n-99 -100 0\n99 100 0\n73 -99 0\n-73 99 -69 0\n-100 63 0\n100 -63 -62 0\n-102 -101 0\n-101 -103 0\n-101 -104 0\n-101 -105 0\n-102 -103 0\n-102 -104 0\n-102 -105 0\n-103 -104 0\n-103 -105 0\n-104 -105 0\n-43 101 -37 0\n-36 102 -31 0\n103 -24 -25 0\n104 -19 -15 0\n-108 -106 0\n-108 -107 0\n106 -51 -45 0\n107 -39 -44 0\n-26 108 -22 0\n-109 -110 0\n-59 109 -53 0\n110 -34 -30 0\n-113 -112 0\n-114 -112 0\n-115 -112 0\n-114 -113 0\n112 -76 -71 0\n-65 -64 113 0\n-58 114 -54 0\n-117 -116 0\n-116 -118 0\n-119 -116 0\n-81 116 -78 0\n117 -72 -73 0\n118 -66 -62 0\n"
  "300 d 58 59 0\n301 19 24 31 105 0 34 45 0\n301 d 45 0\n302 19 24 31 -63 0 34 46 0\n302 d 46 0\n303 19 24 31 -56 0 34 47 0\n303 d 47 0\n304 19 24 31 -50 0 34 48 0\n304 d 48 0\n305 19 24 31 -111 0 34 49 0\n305 d 49 0\n306 24 31 -63 105 0 34 50 0\n306 d 50 0\n307 24 31 -56 105 0 34 51 0\n307 d 51 0\n308 24 31 -50 105 0 34 52 0\n308 d 52 0\n309 24 31 105 -111 0 34 53 0\n309 d 53 0\n310 19 31 -63 105 0 34 54 0\n310 d 54 0\n311 19 31 -56 105 0 34 55 0\n311 d 55 0\n312 19 31 -50 105 0 34 56 0\n312 d 56 0\n313 19 31 105 -111 0 34 57 0\n313 d 57 0\n316 19 24 -63 105 0 34 60 0\n316 d 60 0\n317 19 24 -56 105 0 34 61 0\n317 d 61 0\n318 19 24 -50 105 0 34 62 0\n318 d 62 0\n319 19 24 -56 -63 0 34 63 0\n319 d 63 0\n320 19 24 -50 -63 0 34 64 0\n320 d 64 0\n321 19 24 -63 -111 0 34 65 0\n321 d 65 0\n322 19 24 -50 -111 0 34 66 0\n322 d 66 0\n323 24 -56 -63 105 0 34 67 0\n323 d 67 0\n324 24 -50 -63 105 0 34 68 0\n324 d 68 0\n325 24 -63 105 -111 0 34 69 0\n325 d 69 0\n326 24 -50 -56 105 0 34 70 0\n326 d 70 0\n327 24 -56 105 -111 0 34 71 0\n327 d 71 0\n328 24 -50 105 -111 0 34 72 0\n328 d 72 0\n329 -4 -17 -23 0 1 14 73 0\n329 d 73 0\n330 -4 -13 -23 0 1 14 74 0\n330 d 74 0\n331 -4 -8 -23 0 1 14 75 0\n331 d 75 0\n332 -4 -6 -23 0 1 14 76 0\n332 d 76 0\n333 -4 -13 -17 0 1 14 77 0\n333 d 77 0\n334 -4 -8 -17 0 1 14 78 0\n334 d 78 0\n335 -19 -24 0 7 279 12 278 273 0\n336 -14 -24 -31 0 2 18 79 0\n336 d 79 0\n337 -9 -24 -31 0 2 18 80 0\n337 d 80 0\n338 -5 -24 -31 0 2 18 81 0\n338 d 81 0\n339 -9 -19 -31 0 2 18 82 0\n339 d 82 0\n340 -5 -19 -31 0 2 18 83 0\n340 d 83 0\n341 -19 -105 0 7 279 275 0\n342 -9 -14 -31 0 2 18 84 0\n342 d 84 0\n343 -5 -14 -31 0 2 18 85 0\n343 d 85 0\n344 -14 -31 -105 0 2 18 86 0\n344 d 86 0\n345 -9 -31 -105 0 2 18 87 0\n345 d 87 0\n346 -5 -31 -105 0 2 18 88 0\n346 d 88 0\n347 -12 -34 -47 0 4 26 89 0\n347 d 89 0\n348 -12 -27 -47 0 4 26 90 0\n348 d 90 0\n349 -42 -48 -55 0 5 30 91 0\n349 d 91 0\n350 -18 -42 -55 0 5 30 92 0\n350 d 92 0\n351 -18 -35 -55 0 5 30 93 0\n351 d 93 0\n352 -28 -42 -48 0 5 30 94 0\n352 d 94 0\n353 -18 -42 -48 0 5 30 95 0\n353 d 95 0\n354 -28 -35 -48 0 5 30 96 0\n354 d 96 0\n355 -18 -35 -48 0 5 30 97 0\n355 d 97 0\n356 -25 -56 -63 0 7 34 98 0\n356 d 98 0\n357 -25 -50 -63 0 7 34 99 0\n357 d 99 0\n358 -25 -43 -63 0 7 18 276 268 267 269 279 278 316 0\n359 -44 -64 -71 0 11 38 104 0\n359 d 104 0\n360 -44 -58 -71 0 11 38 105 0\n360 d 105 0\n361 -33 -58 -71 0 11 38 106 0\n361 d 106 0\n362 -44 -51 -71 0 11 38 107 0\n362 d 107 0\n363 -33 -51 -71 0 11 38 108 0\n363 d 108 0\n364 -33 -44 -71 0 11 38 109 0\n364 d 109 0\n365 -44 -51 -64 0 11 38 110 0\n365 d 110 0\n366 -52 -66 -78 0 15 40 112 0\n366 d 112 0\n367 -41 -66 -78 0 15 40 113 0\n367 d 113 0\n368 -60 -74 -83 0 19 42 115 0\n368 d 115 0\n369 -49 -74 -83 0 19 42 116 0\n369 d 116 0\n370 -49 -67 -83 0 19 42 117 0\n370 d 117 0\n371 -60 -74 -79 0 19 42 118 0\n371 d 118 0\n372 -57 -80 -86 0 23 44 119 0\n372 d 119 0\n373 -57 -75 -86 0 23 44 120 0\n373 d 120 0\n374 -57 -68 -86 0 23 44 121 0\n374 d 121 0\n375 -64 126 0 30 131 0\n375 d 131 0\n376 -36 137 0 15 149 0\n376 d 149 0\n377 -24 174 0 11 204 0\n377 d 204 0\n378 -56 186 0 27 222 0\n378 d 222 0\n379 -64 189 0 31 229 0\n379 d 229 0\n380 -72 192 0 35 234 0\n380 d 234 0\n381 -25 89 0 10 240 0\n381 d 240 0\n382 -16 90 0 7 241 0\n382 d 241 0\n383 -33 91 0 14 245 0\n383 d 245 0\n384 -23 92 0 11 247 0\n384 d 247 0\n385 -41 93 0 18 249 0\n385 d 249 0\n386 -31 94 0 15 250 0\n386 d 250 0\n387 -57 95 0 26 254 0\n387 d 254 0\n388 -47 96 0 23 256 0\n388 d 256 0\n389 -65 97 0 30 258 0\n389 d 258 0\n390 -55 98 0 27 259 0\n390 d 259 0\n391 -73 99 0 34 263 0\n391 d 263 0\n392 -63 100 0 31 265 0\n392 d 265 0\n393 -43 101 0 18 276 0\n393 d 276 0\n394 -19 104 0 7 279 0\n394 d 279 0\n395 -51 106 0 22 282 0\n395 d 282 0\n396 -26 108 0 11 284 0\n396 d 284 0\n397 -59 109 0 26 286 0\n397 d 286 0\n398 -34 110 0 15 287 0\n398 d 287 0\n399 -58 114 0 27 294 0\n399 d 294 0\n400 -66 118 0 31 300 0\n400 d 300 0\n401 -25 -63 132 133 134 0 357 145 358 146 140 148 17 277 271 272 270 394 278 316 0\n401 d 358 146 0\n402 -102 24 -63 0 271 272 394 316 0\n403 19 25 56 -63 0 12 402 302 316 277 269 393 320 103 321 0\n403 d 320 321 0\n404 -63 56 132 133 0 144 401 12 403 402 394 341 268 306 325 324 393 277 103 0\n404 d 401 0\n405 186 132 133 188 0 378 404 220 218 219 37 264 227 261 262 0\n405 d 378 264 227 261 262 0\n406 24 -19 -56 63 66 72 102 119 0 28 394 341 307 387 268 326 327 386 277 340 339 251 393 102 248 196 188 187 388 381 385 186 25 239 207 189 206 114 382 205 3 397 9 208 285 153 16 398 383 151 242 384 152 197 195 198 334 333 155 154 150 0\n406 d 326 327 102 114 397 285 398 0\n407 -19 -56 63 66 72 102 119 0 335 406 0\n407 d 406 0\n408 -24 19 -56 0 12 161 28 278 387 270 274 251 311 388 386 277 211 25 248 196 206 385 20 207 213 205 209 208 210 16 29 383 242 384 13 197 195 198 8 351 350 158 157 336 162 156 160 0\n408 d 336 160 0\n409 102 -56 63 66 72 -78 119 0 28 387 251 388 211 25 206 407 161 408 303 159 317 386 277 248 196 385 20 207 213 205 209 208 210 16 29 383 242 384 197 195 198 8 351 158 344 162 156 157 350 0\n409 d 407 344 350 0\n410 -102 -56 -78 132 133 0 271 272 394 317 408 0\n411 188 72 189 0 223 141 224 39 298 297 296 400 143 405 221 410 409 356 12 319 341 323 0\n411 d 297 296 400 405 410 409 356 319 323 0\n412 -33 -71 158 159 160 0 363 361 185 184 179 0\n413 -56 43 63 -71 -86 103 105 160 0 28 387 373 372 251 181 180 388 412 25 16 206 208 205 207 385 248 386 311 307 335 0\n413 d 412 311 0\n414 -24 103 0 12 278 0\n414 d 278 0\n415 31 24 43 56 63 105 0 17 308 100 309 0\n415 d 308 309 0\n416 33 -4 174 0 16 202 244 123 199 243 200 246 21 329 332 330 331 283 125 128 126 127 281 122 396 124 0\n417 -19 63 -71 -86 132 160 0 394 335 341 220 142 268 271 273 203 393 413 221 144 415 218 386 339 340 277 219 248 187 188 196 148 292 385 186 289 147 189 399 140 3 184 145 416 383 363 242 185 384 13 152 197 191 195 198 334 333 155 154 328 101 381 239 382 9 192 153 190 150 194 151 6 347 255 252 253 373 372 181 180 179 0\n417 d 413 328 0\n418 -74 -83 180 0 369 212 209 210 368 0\n418 d 368 0\n419 50 -31 132 133 134 153 154 155 0 177 386 171 248 178 385 393 266 277 148 145 140 147 0\n419 d 145 140 147 0\n420 56 19 24 -31 63 132 139 153 170 0 221 175 144 386 203 220 173 142 218 419 248 219 318 385 37 292 269 272 345 346 20 289 393 277 187 188 213 399 196 186 133 195 189 198 3 8 334 333 416 329 155 154 364 363 13 136 134 191 139 322 101 381 239 382 9 192 153 190 150 194 151 6 347 211 209 210 29 390 351 257 137 389 129 32 130 0\n420 d 322 101 0\n421 -33 24 63 -71 -83 -86 132 160 0 383 364 363 361 203 417 242 200 185 184 384 199 152 197 201 386 248 385 20 213 418 172 420 28 373 372 181 180 179 0\n421 d 420 0\n422 -57 -86 160 161 162 0 373 372 181 180 179 0\n422 d 373 372 181 180 179 0\n423 -31 19 24 132 133 134 153 154 155 165 0 419 318 345 346 187 188 186 0\n423 d 419 0\n424 24 63 -71 -83 -86 132 160 0 203 417 173 33 142 215 421 202 416 199 3 200 189 362 360 185 184 422 28 216 175 214 217 144 24 369 172 423 17 304 305 301 100 269 393 0\n424 d 421 144 24 369 423 0\n425 31 19 43 63 105 0 17 312 313 301 100 408 0\n426 33 -4 58 64 115 0 16 244 123 243 246 329 331 330 332 125 127 126 128 122 124 396 281 280 395 111 283 21 0\n426 d 244 123 243 246 329 331 330 332 125 127 126 128 122 124 396 281 280 395 111 283 21 0\n427 56 -4 64 -71 132 133 137 185 0 130 404 221 33 218 215 219 292 290 289 399 133 426 383 364 363 242 136 200 134 384 13 197 139 129 137 376 196 195 198 8 355 351 217 29 214 210 216 387 251 388 211 209 213 20 385 248 386 201 199 203 414 335 267 274 425 393 0\n427 d 376 0\n428 189 72 -83 -86 0 141 411 225 226 391 260 392 220 33 142 183 417 379 424 414 408 267 270 274 393 425 277 338 337 148 188 187 427 186 3 189 0\n428 d 379 424 425 0\n429 -56 -64 -86 0 28 32 387 389 293 251 257 388 390 211 29 210 209 213 20 385 248 386 201 374 291 399 184 183 422 185 365 200 199 203 335 408 0\n429 d 374 291 183 365 0\n430 -103 31 0 267 17 393 273 394 274 301 408 313 312 100 310 0\n430 d 273 274 313 312 310 0\n431 31 -64 186 0 430 414 203 201 199 200 359 37 219 218 220 302 306 341 0\n431 d 201 0\n432 -19 24 -64 153 154 186 0 394 341 32 268 389 293 393 257 288 178 390 29 176 171 177 324 220 218 219 37 292 0\n433 -63 19 24 56 153 154 155 0 403 316 357 269 177 393 171 178 0\n434 24 -64 -83 -86 132 0 32 429 389 293 221 175 257 288 431 390 386 29 248 210 385 20 213 418 209 172 212 370 174 432 433 220 218 219 37 292 0\n434 d 432 433 0\n435 -83 72 -86 0 141 428 228 32 429 389 293 221 175 257 288 431 390 386 29 248 210 385 20 213 418 209 172 212 370 174 434 12 414 267 393 178 171 177 357 220 218 219 37 292 0\n435 d 428 434 0\n436 63 -24 -78 132 0 220 414 430 270 337 338 277 187 188 186 189 3 142 335 148 408 221 218 219 37 292 288 427 32 293 0\n436 d 142 335 148 408 427 0\n437 -24 72 -78 0 12 414 141 381 430 270 239 386 337 338 277 382 248 187 188 196 9 192 385 186 153 20 207 189 213 3 436 392 260 391 226 411 228 32 389 257 390 29 210 209 211 388 251 387 28 404 143 366 206 205 208 16 383 242 384 13 152 197 191 195 190 198 194 334 333 6 155 154 347 150 151 0\n437 d 436 0\n438 19 -17 24 -31 -47 56 -63 139 166 0 316 403 346 345 381 188 187 239 186 382 189 9 192 3 153 190 333 334 194 154 155 6 150 347 151 0\n439 -63 72 -78 -86 0 392 437 141 260 402 391 226 411 228 32 429 389 221 404 257 431 143 390 277 366 367 29 196 206 20 207 210 205 213 208 209 16 211 383 242 384 13 152 197 191 195 198 438 394 340 339 341 268 188 187 325 324 393 186 103 189 381 3 239 333 334 382 154 155 9 192 153 190 150 194 151 6 347 0\n439 d 404 431 143 366 367 438 341 0\n440 -64 113 0 32 293 0\n440 d 293 0\n441 -33 -47 -48 -71 126 127 148 150 0 383 364 363 242 136 134 165 384 13 191 139 129 137 355 193 190 194 6 347 348 170 163 168 0\n441 d 355 168 0\n442 -14 -31 165 0 343 188 186 187 342 0\n442 d 343 342 0\n443 -28 -48 145 146 147 0 354 352 158 157 156 0\n443 d 354 352 158 157 156 0\n444 55 -31 -71 126 145 146 148 174 181 0 29 386 210 248 385 20 213 166 209 211 388 251 387 216 214 217 132 441 202 138 416 199 3 200 189 362 442 134 162 443 191 139 129 135 169 165 353 163 193 190 194 6 170 348 0\n444 d 132 169 165 353 163 193 170 348 0\n445 33 -55 -71 -86 126 127 131 160 161 174 181 0 202 138 199 200 362 134 185 129 422 135 216 349 214 217 0\n446 131 -55 -71 -86 126 127 160 161 174 181 0 445 364 361 363 167 164 185 422 253 216 252 214 255 217 441 0\n446 d 445 0\n447 -31 -71 -86 126 127 145 146 148 160 161 174 181 0 444 446 139 13 384 242 383 202 416 199 3 200 189 362 442 185 162 422 443 216 217 214 0\n447 d 446 0\n448 56 24 63 -86 132 0 221 203 159 220 33 218 215 219 37 292 288 289 440 399 130 182 133 164 184 417 161 447 17 304 305 301 100 269 393 0\n449 192 -86 0 380 435 41 231 230 232 437 203 159 141 439 33 215 448 429 228 130 182 411 225 417 161 303 317 345 346 187 188 186 189 3 416 361 133 164 184 447 0\n449 d 380 435 141 439 448 417 0\n450 -31 -71 -86 126 127 148 161 165 174 0 449 377 233 159 36 391 260 392 33 215 375 182 447 161 340 339 188 187 186 0\n450 d 375 447 0\n451 -104 24 31 56 63 0 268 275 393 415 0\n451 d 415 0\n452 174 33 -71 -86 0 416 449 202 3 233 199 189 36 200 391 362 260 185 392 377 360 133 164 184 359 130 182 422 28 450 17 451 394 301 305 304 269 100 393 0\n452 d 377 360 359 450 0\n453 -71 33 -86 0 16 449 452 208 233 203 36 414 391 430 260 386 337 338 392 248 187 188 220 385 186 207 189 205 3 206 25 388 251 387 28 221 218 219 292 288 290 289 440 399 426 0\n453 d 452 0\n454 -81 116 0 39 298 0\n454 d 39 298 0\n455 64 -86 150 0 228 130 449 233 36 299 391 295 260 454 392 224 33 223 215 225 453 361 363 133 164 182 184 185 422 253 216 252 214 255 217 441 0\n455 d 182 184 185 422 0\n456 -64 -86 0 440 449 288 233 36 391 260 392 220 429 221 218 219 37 292 0\n456 d 429 0\n457 -86 0 456 228 449 233 36 299 295 454 224 223 225 455 453 364 167 0\n457 d 456 449 455 453 167 0\n458 -24 -31 165 0 337 187 186 188 338 0\n458 d 337 338 0\n459 146 -31 -48 -71 126 127 128 130 145 147 148 174 181 0 444 443 139 129 349 135 0\n459 d 444 443 349 135 0\n460 63 -31 33 64 -71 182 186 0 220 33 130 218 215 219 214 292 217 202 138 290 289 399 133 164 426 3 189 442 458 203 162 159 199 200 362 134 459 161 340 339 188 187 186 0\n460 d 202 138 290 289 399 426 442 458 162 159 199 200 362 459 161 0\n461 73 189 0 36 411 226 0\n461 d 226 0\n462 33 -31 64 -71 0 386 228 248 461 385 391 260 392 16 207 208 205 206 25 388 251 387 28 216 221 460 0\n462 d 16 207 208 205 206 25 460 0\n463 57 -33 -71 126 150 181 0 361 133 253 216 164 252 214 255 217 441 0\n463 d 253 216 164 252 214 255 217 441 0\n464 -31 64 -71 0 457 43 236 386 228 248 461 385 391 20 260 213 392 462 383 242 384 13 197 130 166 173 33 364 361 363 139 215 136 133 134 463 387 251 388 211 209 210 29 129 137 351 8 198 195 196 277 271 394 272 270 414 266 393 178 317 318 177 175 171 172 418 371 237 238 235 0\n464 d 43 236 462 130 166 173 33 364 361 363 139 215 136 133 134 463 129 137 351 8 272 270 266 317 318 175 371 237 238 235 0\n465 56 31 63 0 430 414 17 451 394 304 301 305 100 393 269 0\n465 d 17 451 304 301 305 100 269 0\n466 31 63 0 430 414 465 307 275 394 303 0\n466 d 465 307 303 0\n467 64 0 228 461 391 260 392 466 464 225 411 223 299 224 295 454 0\n467 d 228 461 464 225 411 223 299 224 295 454 0\n468 -76 0 467 440 288 292 37 0\n468 d 440 288 292 37 0\n469 -24 0 467 32 389 257 390 29 176 210 468 219 12 414 430 386 248 385 20 213 209 211 388 251 387 28 221 218 220 267 393 212 357 392 178 177 260 391 36 233 437 232 230 231 41 370 418 174 172 171 0\n469 d 176 12 414 430 267 212 357 392 178 177 260 391 36 233 437 232 230 231 41 370 418 174 172 171 0\n470 19 -31 0 467 32 389 257 390 29 210 468 219 469 203 386 248 385 20 213 209 211 388 251 387 28 221 218 220 403 381 239 382 9 192 153 402 277 196 316 346 188 345 187 186 189 3 416 383 242 384 13 152 197 191 195 190 198 194 334 333 6 155 154 347 150 151 0\n470 d 403 402 316 346 345 0\n471 -31 0 467 32 389 257 390 29 210 468 219 469 203 470 394 275 386 340 339 268 271 248 188 187 393 277 385 186 196 20 189 213 3 209 416 211 383 388 242 251 384 387 13 152 197 28 191 195 221 198 218 334 333 220 155 154 325 324 103 381 239 382 9 192 153 190 150 194 151 6 347 0\n471 d 32 389 257 390 29 210 219 203 470 386 340 339 268 271 248 188 187 393 277 385 186 196 20 189 213 3 209 416 211 383 388 242 251 384 387 13 152 197 28 191 195 221 198 218 334 333 220 155 154 325 324 103 381 239 382 9 192 153 190 150 194 151 6 347 0\n473 0 469 471 466 302 306 394 275 0\n"

theorem rt1_upper_clause895_0 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-8 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-8 : ℤ)
  have hp := hpar (-8 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_1 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-7 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-7 : ℤ)
  have hp := hpar (-7 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_2 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-7 : ℤ) 6 = true) ∧ (y (-7 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-7 : ℤ)
  have hp := hpar (-7 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_3 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-5 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-5 : ℤ)
  have hp := hpar (-5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_4 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-4 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-4 : ℤ)
  have hp := hpar (-4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_5 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-4 : ℤ) 6 = true) ∧ (y (-4 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-4 : ℤ)
  have hp := hpar (-4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_6 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-3 : ℤ)
  have hp := hpar (-3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_7 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 6 = true) ∧ (y (-3 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-3 : ℤ)
  have hp := hpar (-3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_8 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 5 = true) ∧ ¬ (y (-3 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-3 : ℤ)
  have hp := hpar (-3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_9 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_10 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_11 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 6 = true) ∧ (y (-2 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_12 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 5 = true) ∧ ¬ (y (-2 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_13 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-1 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_14 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-1 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_15 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_16 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ ¬ (y (-1 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_17 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_18 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_19 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 2 = true) ∧ ¬ (y (0 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_20 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 1 = true) ∧ (y (0 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_21 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_22 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_23 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 6 = true) ∧ (y (1 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_24 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 5 = true) ∧ ¬ (y (1 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_25 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_26 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_27 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 6 = true) ∧ (y (2 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_28 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 5 = true) ∧ ¬ (y (2 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_29 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_30 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_31 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 2 = true) ∧ ¬ (y (3 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_32 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 5 = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_33 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_34 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_35 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (4 : ℤ) 2 = true) ∧ ¬ (y (4 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_36 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 1 = true) ∧ (y (4 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_37 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_38 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 1 = true) ∧ (y (5 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_39 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (6 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (6 : ℤ)
  have hp := hpar (6 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_40 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (6 : ℤ) 5 = true) ∧ ¬ (y (6 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (6 : ℤ)
  have hp := hpar (6 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_41 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (7 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (7 : ℤ)
  have hp := hpar (7 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_42 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (7 : ℤ) 5 = true) ∧ ¬ (y (7 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (7 : ℤ)
  have hp := hpar (7 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_43 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (8 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (8 : ℤ)
  have hp := hpar (8 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_upper_clause895_44 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_45 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_46 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_47 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_48 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_49 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_50 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_51 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_52 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_53 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_54 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_55 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_56 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_57 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ (y (1 : ℤ) 3 = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_58 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ (e (4 : ℤ) = true) ∧ ¬ (y (-1 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_59 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_60 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_61 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_62 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 1 = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_63 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_64 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 3 = true) ∧ (e (4 : ℤ) = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_65 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (1 : ℤ) 3 = true) ∧ ¬ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_66 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 1 = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_67 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (3 : ℤ) 1 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_68 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 1 = true) ∧ (e (4 : ℤ) = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_69 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_70 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (2 : ℤ) 2 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_71 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ (y (-2 : ℤ) 2 = true) ∧ (e (4 : ℤ) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hn
  norm_num at hn
  have hh := hn
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  have hb5 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb6 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb7 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb8 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb9 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_72 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 2 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_73 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 1 = true) ∧ (y (-4 : ℤ) 3 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_74 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-5 : ℤ) 4 = true) ∧ (y (-2 : ℤ) 1 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_75 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-6 : ℤ) 5 = true) ∧ (y (-2 : ℤ) 1 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_76 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-4 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 2 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_77 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-5 : ℤ) 4 = true) ∧ (y (-3 : ℤ) 2 = true) ∧ (y (-7 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 0 = true) ∧ (y (-8 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_m1 := h.2.2.2.2 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_m1
  have hh := g_cnt_0_m1
  have hb0 : (y (-1 : ℤ) 0).toNat ≤ 1 := by cases y (-1 : ℤ) 0 <;> decide
  have hb1 : (y (-2 : ℤ) 1).toNat ≤ 1 := by cases y (-2 : ℤ) 1 <;> decide
  have hb2 : (y (-3 : ℤ) 2).toNat ≤ 1 := by cases y (-3 : ℤ) 2 <;> decide
  have hb3 : (y (-4 : ℤ) 3).toNat ≤ 1 := by cases y (-4 : ℤ) 3 <;> decide
  have hb4 : (y (-5 : ℤ) 4).toNat ≤ 1 := by cases y (-5 : ℤ) 4 <;> decide
  have hb5 : (y (-6 : ℤ) 5).toNat ≤ 1 := by cases y (-6 : ℤ) 5 <;> decide
  have hb6 : (y (-7 : ℤ) 6).toNat ≤ 1 := by cases y (-7 : ℤ) 6 <;> decide
  have hb7 : (y (-8 : ℤ) 7).toNat ≤ 1 := by cases y (-8 : ℤ) 7 <;> decide
  have hb8 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_78 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-4 : ℤ) 4 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_79 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (y (-5 : ℤ) 5 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_80 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-6 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_81 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-5 : ℤ) 5 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_82 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-6 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_83 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-5 : ℤ) 5 = true) ∧ (y (-4 : ℤ) 4 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_84 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-6 : ℤ) 6 = true) ∧ (y (-4 : ℤ) 4 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_85 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ (y (-4 : ℤ) 4 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_86 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ (y (-5 : ℤ) 5 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_87 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ (y (-6 : ℤ) 6 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true) ∧ (y (-7 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_0 := h.2.2.2.2 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_0
  have hh := g_cnt_0_0
  have hb0 : (y (0 : ℤ) 0).toNat ≤ 1 := by cases y (0 : ℤ) 0 <;> decide
  have hb1 : (y (-1 : ℤ) 1).toNat ≤ 1 := by cases y (-1 : ℤ) 1 <;> decide
  have hb2 : (y (-2 : ℤ) 2).toNat ≤ 1 := by cases y (-2 : ℤ) 2 <;> decide
  have hb3 : (y (-3 : ℤ) 3).toNat ≤ 1 := by cases y (-3 : ℤ) 3 <;> decide
  have hb4 : (y (-4 : ℤ) 4).toNat ≤ 1 := by cases y (-4 : ℤ) 4 <;> decide
  have hb5 : (y (-5 : ℤ) 5).toNat ≤ 1 := by cases y (-5 : ℤ) 5 <;> decide
  have hb6 : (y (-6 : ℤ) 6).toNat ≤ 1 := by cases y (-6 : ℤ) 6 <;> decide
  have hb7 : (y (-7 : ℤ) 7).toNat ≤ 1 := by cases y (-7 : ℤ) 7 <;> decide
  have hb8 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_88 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 1 = true) ∧ (y (-1 : ℤ) 3 = true) ∧ (y (-4 : ℤ) 6 = true) ∧ (y (2 : ℤ) 0 = true) ∧ (y (-5 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_2 := h.2.2.2.2 (2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_2
  have hh := g_cnt_0_2
  have hb0 : (y (2 : ℤ) 0).toNat ≤ 1 := by cases y (2 : ℤ) 0 <;> decide
  have hb1 : (y (1 : ℤ) 1).toNat ≤ 1 := by cases y (1 : ℤ) 1 <;> decide
  have hb2 : (y (0 : ℤ) 2).toNat ≤ 1 := by cases y (0 : ℤ) 2 <;> decide
  have hb3 : (y (-1 : ℤ) 3).toNat ≤ 1 := by cases y (-1 : ℤ) 3 <;> decide
  have hb4 : (y (-2 : ℤ) 4).toNat ≤ 1 := by cases y (-2 : ℤ) 4 <;> decide
  have hb5 : (y (-3 : ℤ) 5).toNat ≤ 1 := by cases y (-3 : ℤ) 5 <;> decide
  have hb6 : (y (-4 : ℤ) 6).toNat ≤ 1 := by cases y (-4 : ℤ) 6 <;> decide
  have hb7 : (y (-5 : ℤ) 7).toNat ≤ 1 := by cases y (-5 : ℤ) 7 <;> decide
  have hb8 : (e (2 : ℤ)).toNat ≤ 1 := by cases e (2 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_89 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 4 = true) ∧ (y (1 : ℤ) 1 = true) ∧ (y (-4 : ℤ) 6 = true) ∧ (y (2 : ℤ) 0 = true) ∧ (y (-5 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_2 := h.2.2.2.2 (2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_2
  have hh := g_cnt_0_2
  have hb0 : (y (2 : ℤ) 0).toNat ≤ 1 := by cases y (2 : ℤ) 0 <;> decide
  have hb1 : (y (1 : ℤ) 1).toNat ≤ 1 := by cases y (1 : ℤ) 1 <;> decide
  have hb2 : (y (0 : ℤ) 2).toNat ≤ 1 := by cases y (0 : ℤ) 2 <;> decide
  have hb3 : (y (-1 : ℤ) 3).toNat ≤ 1 := by cases y (-1 : ℤ) 3 <;> decide
  have hb4 : (y (-2 : ℤ) 4).toNat ≤ 1 := by cases y (-2 : ℤ) 4 <;> decide
  have hb5 : (y (-3 : ℤ) 5).toNat ≤ 1 := by cases y (-3 : ℤ) 5 <;> decide
  have hb6 : (y (-4 : ℤ) 6).toNat ≤ 1 := by cases y (-4 : ℤ) 6 <;> decide
  have hb7 : (y (-5 : ℤ) 7).toNat ≤ 1 := by cases y (-5 : ℤ) 7 <;> decide
  have hb8 : (e (2 : ℤ)).toNat ≤ 1 := by cases e (2 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_90 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 1 = true) ∧ (y (1 : ℤ) 2 = true) ∧ (y (0 : ℤ) 3 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_91 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 1 = true) ∧ (y (0 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_92 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 4 = true) ∧ (y (2 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_93 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 5 = true) ∧ (y (1 : ℤ) 2 = true) ∧ (y (0 : ℤ) 3 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_94 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 3 = true) ∧ (y (1 : ℤ) 2 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_95 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 5 = true) ∧ (y (1 : ℤ) 2 = true) ∧ (y (-1 : ℤ) 4 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_96 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 4 = true) ∧ (y (1 : ℤ) 2 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_3 := h.2.2.2.2 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_3
  have hh := g_cnt_0_3
  have hb0 : (y (3 : ℤ) 0).toNat ≤ 1 := by cases y (3 : ℤ) 0 <;> decide
  have hb1 : (y (2 : ℤ) 1).toNat ≤ 1 := by cases y (2 : ℤ) 1 <;> decide
  have hb2 : (y (1 : ℤ) 2).toNat ≤ 1 := by cases y (1 : ℤ) 2 <;> decide
  have hb3 : (y (0 : ℤ) 3).toNat ≤ 1 := by cases y (0 : ℤ) 3 <;> decide
  have hb4 : (y (-1 : ℤ) 4).toNat ≤ 1 := by cases y (-1 : ℤ) 4 <;> decide
  have hb5 : (y (-2 : ℤ) 5).toNat ≤ 1 := by cases y (-2 : ℤ) 5 <;> decide
  have hb6 : (y (-3 : ℤ) 6).toNat ≤ 1 := by cases y (-3 : ℤ) 6 <;> decide
  have hb7 : (y (-4 : ℤ) 7).toNat ≤ 1 := by cases y (-4 : ℤ) 7 <;> decide
  have hb8 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_97 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 6 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_98 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_99 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (0 : ℤ) 4 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (-1 : ℤ) 5 = true) ∧ ¬ (y (1 : ℤ) 3 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_100 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 6 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (0 : ℤ) 4 = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_101 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (-2 : ℤ) 6 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (0 : ℤ) 4 = true) ∧ ¬ (y (-1 : ℤ) 5 = true) ∧ ¬ (y (1 : ℤ) 3 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_102 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (-2 : ℤ) 6 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (0 : ℤ) 4 = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  have g_cnt_0_4 := h.2.2.2.2 (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_4
  have hh := g_cnt_0_4
  have hb0 : (y (4 : ℤ) 0).toNat ≤ 1 := by cases y (4 : ℤ) 0 <;> decide
  have hb1 : (y (3 : ℤ) 1).toNat ≤ 1 := by cases y (3 : ℤ) 1 <;> decide
  have hb2 : (y (2 : ℤ) 2).toNat ≤ 1 := by cases y (2 : ℤ) 2 <;> decide
  have hb3 : (y (1 : ℤ) 3).toNat ≤ 1 := by cases y (1 : ℤ) 3 <;> decide
  have hb4 : (y (0 : ℤ) 4).toNat ≤ 1 := by cases y (0 : ℤ) 4 <;> decide
  have hb5 : (y (-1 : ℤ) 5).toNat ≤ 1 := by cases y (-1 : ℤ) 5 <;> decide
  have hb6 : (y (-2 : ℤ) 6).toNat ≤ 1 := by cases y (-2 : ℤ) 6 <;> decide
  have hb7 : (y (-3 : ℤ) 7).toNat ≤ 1 := by cases y (-3 : ℤ) 7 <;> decide
  have hb8 : (e (4 : ℤ)).toNat ≤ 1 := by cases e (4 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_103 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 2 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_104 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 3 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_105 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 3 = true) ∧ (y (-1 : ℤ) 6 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_106 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 4 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_107 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 4 = true) ∧ (y (-1 : ℤ) 6 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_108 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 5 = true) ∧ (y (-1 : ℤ) 6 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_109 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 4 = true) ∧ (y (3 : ℤ) 2 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_110 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 5 = true) ∧ ¬ (y (-1 : ℤ) 6 = true) ∧ ¬ (y (2 : ℤ) 3 = true) ∧ ¬ (y (1 : ℤ) 4 = true) ∧ ¬ (y (3 : ℤ) 2 = true) ∧ ¬ (e (5 : ℤ) = true)) := by
  classical
  have g_cnt_0_5 := h.2.2.2.2 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_5
  have hh := g_cnt_0_5
  have hb0 : (y (5 : ℤ) 0).toNat ≤ 1 := by cases y (5 : ℤ) 0 <;> decide
  have hb1 : (y (4 : ℤ) 1).toNat ≤ 1 := by cases y (4 : ℤ) 1 <;> decide
  have hb2 : (y (3 : ℤ) 2).toNat ≤ 1 := by cases y (3 : ℤ) 2 <;> decide
  have hb3 : (y (2 : ℤ) 3).toNat ≤ 1 := by cases y (2 : ℤ) 3 <;> decide
  have hb4 : (y (1 : ℤ) 4).toNat ≤ 1 := by cases y (1 : ℤ) 4 <;> decide
  have hb5 : (y (0 : ℤ) 5).toNat ≤ 1 := by cases y (0 : ℤ) 5 <;> decide
  have hb6 : (y (-1 : ℤ) 6).toNat ≤ 1 := by cases y (-1 : ℤ) 6 <;> decide
  have hb7 : (y (-2 : ℤ) 7).toNat ≤ 1 := by cases y (-2 : ℤ) 7 <;> decide
  have hb8 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_111 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 3 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (1 : ℤ) 5 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_6 := h.2.2.2.2 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_6
  have hh := g_cnt_0_6
  have hb0 : (y (6 : ℤ) 0).toNat ≤ 1 := by cases y (6 : ℤ) 0 <;> decide
  have hb1 : (y (5 : ℤ) 1).toNat ≤ 1 := by cases y (5 : ℤ) 1 <;> decide
  have hb2 : (y (4 : ℤ) 2).toNat ≤ 1 := by cases y (4 : ℤ) 2 <;> decide
  have hb3 : (y (3 : ℤ) 3).toNat ≤ 1 := by cases y (3 : ℤ) 3 <;> decide
  have hb4 : (y (2 : ℤ) 4).toNat ≤ 1 := by cases y (2 : ℤ) 4 <;> decide
  have hb5 : (y (1 : ℤ) 5).toNat ≤ 1 := by cases y (1 : ℤ) 5 <;> decide
  have hb6 : (y (0 : ℤ) 6).toNat ≤ 1 := by cases y (0 : ℤ) 6 <;> decide
  have hb7 : (y (-1 : ℤ) 7).toNat ≤ 1 := by cases y (-1 : ℤ) 7 <;> decide
  have hb8 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_112 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 6 = true) ∧ (y (3 : ℤ) 3 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_6 := h.2.2.2.2 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_6
  have hh := g_cnt_0_6
  have hb0 : (y (6 : ℤ) 0).toNat ≤ 1 := by cases y (6 : ℤ) 0 <;> decide
  have hb1 : (y (5 : ℤ) 1).toNat ≤ 1 := by cases y (5 : ℤ) 1 <;> decide
  have hb2 : (y (4 : ℤ) 2).toNat ≤ 1 := by cases y (4 : ℤ) 2 <;> decide
  have hb3 : (y (3 : ℤ) 3).toNat ≤ 1 := by cases y (3 : ℤ) 3 <;> decide
  have hb4 : (y (2 : ℤ) 4).toNat ≤ 1 := by cases y (2 : ℤ) 4 <;> decide
  have hb5 : (y (1 : ℤ) 5).toNat ≤ 1 := by cases y (1 : ℤ) 5 <;> decide
  have hb6 : (y (0 : ℤ) 6).toNat ≤ 1 := by cases y (0 : ℤ) 6 <;> decide
  have hb7 : (y (-1 : ℤ) 7).toNat ≤ 1 := by cases y (-1 : ℤ) 7 <;> decide
  have hb8 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_113 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 4 = true) ∧ ¬ (y (0 : ℤ) 6 = true) ∧ ¬ (y (1 : ℤ) 5 = true) ∧ ¬ (y (4 : ℤ) 2 = true) ∧ ¬ (e (6 : ℤ) = true)) := by
  classical
  have g_cnt_0_6 := h.2.2.2.2 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_6
  have hh := g_cnt_0_6
  have hb0 : (y (6 : ℤ) 0).toNat ≤ 1 := by cases y (6 : ℤ) 0 <;> decide
  have hb1 : (y (5 : ℤ) 1).toNat ≤ 1 := by cases y (5 : ℤ) 1 <;> decide
  have hb2 : (y (4 : ℤ) 2).toNat ≤ 1 := by cases y (4 : ℤ) 2 <;> decide
  have hb3 : (y (3 : ℤ) 3).toNat ≤ 1 := by cases y (3 : ℤ) 3 <;> decide
  have hb4 : (y (2 : ℤ) 4).toNat ≤ 1 := by cases y (2 : ℤ) 4 <;> decide
  have hb5 : (y (1 : ℤ) 5).toNat ≤ 1 := by cases y (1 : ℤ) 5 <;> decide
  have hb6 : (y (0 : ℤ) 6).toNat ≤ 1 := by cases y (0 : ℤ) 6 <;> decide
  have hb7 : (y (-1 : ℤ) 7).toNat ≤ 1 := by cases y (-1 : ℤ) 7 <;> decide
  have hb8 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_114 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (6 : ℤ) 1 = true) ∧ (y (4 : ℤ) 3 = true) ∧ (y (2 : ℤ) 5 = true) ∧ (y (7 : ℤ) 0 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_7 := h.2.2.2.2 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_7
  have hh := g_cnt_0_7
  have hb0 : (y (7 : ℤ) 0).toNat ≤ 1 := by cases y (7 : ℤ) 0 <;> decide
  have hb1 : (y (6 : ℤ) 1).toNat ≤ 1 := by cases y (6 : ℤ) 1 <;> decide
  have hb2 : (y (5 : ℤ) 2).toNat ≤ 1 := by cases y (5 : ℤ) 2 <;> decide
  have hb3 : (y (4 : ℤ) 3).toNat ≤ 1 := by cases y (4 : ℤ) 3 <;> decide
  have hb4 : (y (3 : ℤ) 4).toNat ≤ 1 := by cases y (3 : ℤ) 4 <;> decide
  have hb5 : (y (2 : ℤ) 5).toNat ≤ 1 := by cases y (2 : ℤ) 5 <;> decide
  have hb6 : (y (1 : ℤ) 6).toNat ≤ 1 := by cases y (1 : ℤ) 6 <;> decide
  have hb7 : (y (0 : ℤ) 7).toNat ≤ 1 := by cases y (0 : ℤ) 7 <;> decide
  have hb8 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_115 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (6 : ℤ) 1 = true) ∧ (y (4 : ℤ) 3 = true) ∧ (y (1 : ℤ) 6 = true) ∧ (y (7 : ℤ) 0 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_7 := h.2.2.2.2 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_7
  have hh := g_cnt_0_7
  have hb0 : (y (7 : ℤ) 0).toNat ≤ 1 := by cases y (7 : ℤ) 0 <;> decide
  have hb1 : (y (6 : ℤ) 1).toNat ≤ 1 := by cases y (6 : ℤ) 1 <;> decide
  have hb2 : (y (5 : ℤ) 2).toNat ≤ 1 := by cases y (5 : ℤ) 2 <;> decide
  have hb3 : (y (4 : ℤ) 3).toNat ≤ 1 := by cases y (4 : ℤ) 3 <;> decide
  have hb4 : (y (3 : ℤ) 4).toNat ≤ 1 := by cases y (3 : ℤ) 4 <;> decide
  have hb5 : (y (2 : ℤ) 5).toNat ≤ 1 := by cases y (2 : ℤ) 5 <;> decide
  have hb6 : (y (1 : ℤ) 6).toNat ≤ 1 := by cases y (1 : ℤ) 6 <;> decide
  have hb7 : (y (0 : ℤ) 7).toNat ≤ 1 := by cases y (0 : ℤ) 7 <;> decide
  have hb8 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_116 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 4 = true) ∧ (y (6 : ℤ) 1 = true) ∧ (y (1 : ℤ) 6 = true) ∧ (y (7 : ℤ) 0 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_7 := h.2.2.2.2 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_7
  have hh := g_cnt_0_7
  have hb0 : (y (7 : ℤ) 0).toNat ≤ 1 := by cases y (7 : ℤ) 0 <;> decide
  have hb1 : (y (6 : ℤ) 1).toNat ≤ 1 := by cases y (6 : ℤ) 1 <;> decide
  have hb2 : (y (5 : ℤ) 2).toNat ≤ 1 := by cases y (5 : ℤ) 2 <;> decide
  have hb3 : (y (4 : ℤ) 3).toNat ≤ 1 := by cases y (4 : ℤ) 3 <;> decide
  have hb4 : (y (3 : ℤ) 4).toNat ≤ 1 := by cases y (3 : ℤ) 4 <;> decide
  have hb5 : (y (2 : ℤ) 5).toNat ≤ 1 := by cases y (2 : ℤ) 5 <;> decide
  have hb6 : (y (1 : ℤ) 6).toNat ≤ 1 := by cases y (1 : ℤ) 6 <;> decide
  have hb7 : (y (0 : ℤ) 7).toNat ≤ 1 := by cases y (0 : ℤ) 7 <;> decide
  have hb8 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_117 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (5 : ℤ) 2 = true) ∧ (y (2 : ℤ) 5 = true) ∧ (y (4 : ℤ) 3 = true) ∧ (y (7 : ℤ) 0 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_7 := h.2.2.2.2 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_7
  have hh := g_cnt_0_7
  have hb0 : (y (7 : ℤ) 0).toNat ≤ 1 := by cases y (7 : ℤ) 0 <;> decide
  have hb1 : (y (6 : ℤ) 1).toNat ≤ 1 := by cases y (6 : ℤ) 1 <;> decide
  have hb2 : (y (5 : ℤ) 2).toNat ≤ 1 := by cases y (5 : ℤ) 2 <;> decide
  have hb3 : (y (4 : ℤ) 3).toNat ≤ 1 := by cases y (4 : ℤ) 3 <;> decide
  have hb4 : (y (3 : ℤ) 4).toNat ≤ 1 := by cases y (3 : ℤ) 4 <;> decide
  have hb5 : (y (2 : ℤ) 5).toNat ≤ 1 := by cases y (2 : ℤ) 5 <;> decide
  have hb6 : (y (1 : ℤ) 6).toNat ≤ 1 := by cases y (1 : ℤ) 6 <;> decide
  have hb7 : (y (0 : ℤ) 7).toNat ≤ 1 := by cases y (0 : ℤ) 7 <;> decide
  have hb8 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_118 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (7 : ℤ) 1 = true) ∧ (y (5 : ℤ) 3 = true) ∧ (y (2 : ℤ) 6 = true) ∧ (y (8 : ℤ) 0 = true) ∧ (y (1 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_8 := h.2.2.2.2 (8 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_8
  have hh := g_cnt_0_8
  have hb0 : (y (8 : ℤ) 0).toNat ≤ 1 := by cases y (8 : ℤ) 0 <;> decide
  have hb1 : (y (7 : ℤ) 1).toNat ≤ 1 := by cases y (7 : ℤ) 1 <;> decide
  have hb2 : (y (6 : ℤ) 2).toNat ≤ 1 := by cases y (6 : ℤ) 2 <;> decide
  have hb3 : (y (5 : ℤ) 3).toNat ≤ 1 := by cases y (5 : ℤ) 3 <;> decide
  have hb4 : (y (4 : ℤ) 4).toNat ≤ 1 := by cases y (4 : ℤ) 4 <;> decide
  have hb5 : (y (3 : ℤ) 5).toNat ≤ 1 := by cases y (3 : ℤ) 5 <;> decide
  have hb6 : (y (2 : ℤ) 6).toNat ≤ 1 := by cases y (2 : ℤ) 6 <;> decide
  have hb7 : (y (1 : ℤ) 7).toNat ≤ 1 := by cases y (1 : ℤ) 7 <;> decide
  have hb8 : (e (8 : ℤ)).toNat ≤ 1 := by cases e (8 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_119 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (4 : ℤ) 4 = true) ∧ (y (7 : ℤ) 1 = true) ∧ (y (2 : ℤ) 6 = true) ∧ (y (8 : ℤ) 0 = true) ∧ (y (1 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_8 := h.2.2.2.2 (8 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_8
  have hh := g_cnt_0_8
  have hb0 : (y (8 : ℤ) 0).toNat ≤ 1 := by cases y (8 : ℤ) 0 <;> decide
  have hb1 : (y (7 : ℤ) 1).toNat ≤ 1 := by cases y (7 : ℤ) 1 <;> decide
  have hb2 : (y (6 : ℤ) 2).toNat ≤ 1 := by cases y (6 : ℤ) 2 <;> decide
  have hb3 : (y (5 : ℤ) 3).toNat ≤ 1 := by cases y (5 : ℤ) 3 <;> decide
  have hb4 : (y (4 : ℤ) 4).toNat ≤ 1 := by cases y (4 : ℤ) 4 <;> decide
  have hb5 : (y (3 : ℤ) 5).toNat ≤ 1 := by cases y (3 : ℤ) 5 <;> decide
  have hb6 : (y (2 : ℤ) 6).toNat ≤ 1 := by cases y (2 : ℤ) 6 <;> decide
  have hb7 : (y (1 : ℤ) 7).toNat ≤ 1 := by cases y (1 : ℤ) 7 <;> decide
  have hb8 : (e (8 : ℤ)).toNat ≤ 1 := by cases e (8 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_120 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 5 = true) ∧ (y (7 : ℤ) 1 = true) ∧ (y (2 : ℤ) 6 = true) ∧ (y (8 : ℤ) 0 = true) ∧ (y (1 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_8 := h.2.2.2.2 (8 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_8
  have hh := g_cnt_0_8
  have hb0 : (y (8 : ℤ) 0).toNat ≤ 1 := by cases y (8 : ℤ) 0 <;> decide
  have hb1 : (y (7 : ℤ) 1).toNat ≤ 1 := by cases y (7 : ℤ) 1 <;> decide
  have hb2 : (y (6 : ℤ) 2).toNat ≤ 1 := by cases y (6 : ℤ) 2 <;> decide
  have hb3 : (y (5 : ℤ) 3).toNat ≤ 1 := by cases y (5 : ℤ) 3 <;> decide
  have hb4 : (y (4 : ℤ) 4).toNat ≤ 1 := by cases y (4 : ℤ) 4 <;> decide
  have hb5 : (y (3 : ℤ) 5).toNat ≤ 1 := by cases y (3 : ℤ) 5 <;> decide
  have hb6 : (y (2 : ℤ) 6).toNat ≤ 1 := by cases y (2 : ℤ) 6 <;> decide
  have hb7 : (y (1 : ℤ) 7).toNat ≤ 1 := by cases y (1 : ℤ) 7 <;> decide
  have hb8 : (e (8 : ℤ)).toNat ≤ 1 := by cases e (8 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_121 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 3) = true) ∧ ¬ ((y (-3 : ℤ) 2 && y (-3 : ℤ) 4) = true) ∧ ¬ ((y (-5 : ℤ) 4 && y (-5 : ℤ) 6) = true) ∧ ¬ ((y (-4 : ℤ) 3 && y (-4 : ℤ) 5) = true) ∧ ¬ ((y (-6 : ℤ) 5 && y (-6 : ℤ) 7) = true) ∧ ¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 2) = true)) := by
  classical
  have g_cov_2_m1 := h.2.2.2.1 2 (by omega) (by omega) (by omega) (-1 : ℤ)
  norm_num at g_cov_2_m1
  have hh := g_cov_2_m1
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_122 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 2) = true) ∧ ¬ (y (-1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_123 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 1 && y (-2 : ℤ) 3) = true) ∧ ¬ (y (-2 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_124 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 2 && y (-3 : ℤ) 4) = true) ∧ ¬ (y (-3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_125 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-4 : ℤ) 3 && y (-4 : ℤ) 5) = true) ∧ ¬ (y (-4 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_126 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-5 : ℤ) 4 && y (-5 : ℤ) 6) = true) ∧ ¬ (y (-5 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_127 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-6 : ℤ) 5 && y (-6 : ℤ) 7) = true) ∧ ¬ (y (-6 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_128 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ∧ ¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ∧ ¬ ((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ∧ ¬ ((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ∧ ¬ ((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true)) := by
  classical
  have g_cov_2_3 := h.2.2.2.1 2 (by omega) (by omega) (by omega) (3 : ℤ)
  norm_num at g_cov_2_3
  have hh := g_cov_2_3
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_129 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ∧ ¬ (y (3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_130 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ∧ (y (3 : ℤ) 2 = true) ∧ (y (3 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_131 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ∧ ¬ (y (2 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_132 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ∧ ¬ (y (2 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_133 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ∧ ¬ (y (1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_134 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_135 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_136 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_137 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_138 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_139 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 2) = true) ∧ ¬ ((y (1 : ℤ) 3 && y (1 : ℤ) 5) = true) ∧ ¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 3) = true) ∧ ¬ ((y (-1 : ℤ) 5 && y (-1 : ℤ) 7) = true) ∧ ¬ ((y (2 : ℤ) 2 && y (2 : ℤ) 4) = true) ∧ ¬ ((y (0 : ℤ) 4 && y (0 : ℤ) 6) = true)) := by
  classical
  have g_cov_2_4 := h.2.2.2.1 2 (by omega) (by omega) (by omega) (4 : ℤ)
  norm_num at g_cov_2_4
  have hh := g_cov_2_4
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_140 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 0 && y (4 : ℤ) 2) = true) ∧ ¬ (y (4 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_141 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 3) = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_142 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 3) = true) ∧ ¬ (y (3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_143 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 2 && y (2 : ℤ) 4) = true) ∧ ¬ (y (2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_144 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 3 && y (1 : ℤ) 5) = true) ∧ ¬ (y (1 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_145 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 4 && y (0 : ℤ) 6) = true) ∧ ¬ (y (0 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_146 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 4 && y (0 : ℤ) 6) = true) ∧ ¬ (y (0 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_147 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 5 && y (-1 : ℤ) 7) = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_148 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-1 : ℤ) 5 && y (-1 : ℤ) 7) = true) ∧ (y (-1 : ℤ) 5 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_149 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 3) = true) ∧ ¬ ((y (-3 : ℤ) 2 && y (-3 : ℤ) 5) = true) ∧ ¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 4) = true) ∧ ¬ ((y (-5 : ℤ) 4 && y (-5 : ℤ) 7) = true) ∧ ¬ ((y (-4 : ℤ) 3 && y (-4 : ℤ) 6) = true)) := by
  classical
  have g_cov_3_m1 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (-1 : ℤ)
  norm_num at g_cov_3_m1
  have hh := g_cov_3_m1
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_150 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 3) = true) ∧ ¬ (y (-1 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_151 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 1 && y (-2 : ℤ) 4) = true) ∧ ¬ (y (-2 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_152 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 2 && y (-3 : ℤ) 5) = true) ∧ ¬ (y (-3 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_153 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-4 : ℤ) 3 && y (-4 : ℤ) 6) = true) ∧ ¬ (y (-4 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_154 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-5 : ℤ) 4 && y (-5 : ℤ) 7) = true) ∧ ¬ (y (-5 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_155 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 0 && y (0 : ℤ) 3) = true) ∧ ¬ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 4) = true) ∧ ¬ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 6) = true) ∧ ¬ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 5) = true) ∧ ¬ ((y (-4 : ℤ) 4 && y (-4 : ℤ) 7) = true)) := by
  classical
  have g_cov_3_0 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (0 : ℤ)
  norm_num at g_cov_3_0
  have hh := g_cov_3_0
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_156 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 3) = true) ∧ ¬ (y (0 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_157 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 4) = true) ∧ ¬ (y (-1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_158 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 5) = true) ∧ ¬ (y (-2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_159 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 5) = true) ∧ ¬ (y (-2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_160 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 3 && y (-3 : ℤ) 6) = true) ∧ ¬ (y (-3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_161 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-4 : ℤ) 4 && y (-4 : ℤ) 7) = true) ∧ ¬ (y (-4 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_162 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 1 && y (1 : ℤ) 4) = true) ∧ ¬ ((y (-2 : ℤ) 4 && y (-2 : ℤ) 7) = true) ∧ ¬ ((y (-1 : ℤ) 3 && y (-1 : ℤ) 6) = true) ∧ ¬ ((y (0 : ℤ) 2 && y (0 : ℤ) 5) = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 3) = true)) := by
  classical
  have g_cov_3_2 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (2 : ℤ)
  norm_num at g_cov_3_2
  have hh := g_cov_3_2
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_163 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 0 && y (2 : ℤ) 3) = true) ∧ ¬ (y (2 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_164 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 1 && y (1 : ℤ) 4) = true) ∧ ¬ (y (1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_165 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 2 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_166 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 2 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_167 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 3 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_168 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 3 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_169 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 4 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_170 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 3) = true) ∧ ¬ ((y (1 : ℤ) 3 && y (1 : ℤ) 6) = true) ∧ ¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 4) = true) ∧ ¬ ((y (2 : ℤ) 2 && y (2 : ℤ) 5) = true) ∧ ¬ ((y (0 : ℤ) 4 && y (0 : ℤ) 7) = true)) := by
  classical
  have g_cov_3_4 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (4 : ℤ)
  norm_num at g_cov_3_4
  have hh := g_cov_3_4
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_171 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 0 && y (4 : ℤ) 3) = true) ∧ ¬ (y (4 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_172 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 4) = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_173 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 4) = true) ∧ ¬ (y (3 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_174 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 2 && y (2 : ℤ) 5) = true) ∧ ¬ (y (2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_175 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 2 && y (2 : ℤ) 5) = true) ∧ ¬ (y (2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_176 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 3 && y (1 : ℤ) 6) = true) ∧ ¬ (y (1 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_177 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 4 && y (0 : ℤ) 7) = true) ∧ ¬ (y (0 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_178 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 1 && y (4 : ℤ) 4) = true) ∧ ¬ ((y (5 : ℤ) 0 && y (5 : ℤ) 3) = true) ∧ ¬ ((y (2 : ℤ) 3 && y (2 : ℤ) 6) = true) ∧ ¬ ((y (1 : ℤ) 4 && y (1 : ℤ) 7) = true) ∧ ¬ ((y (3 : ℤ) 2 && y (3 : ℤ) 5) = true)) := by
  classical
  have g_cov_3_5 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (5 : ℤ)
  norm_num at g_cov_3_5
  have hh := g_cov_3_5
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_179 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 0 && y (5 : ℤ) 3) = true) ∧ ¬ (y (5 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_180 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 1 && y (4 : ℤ) 4) = true) ∧ ¬ (y (4 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_181 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 2 && y (3 : ℤ) 5) = true) ∧ ¬ (y (3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_182 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 2 && y (3 : ℤ) 5) = true) ∧ ¬ (y (3 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_183 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 3 && y (2 : ℤ) 6) = true) ∧ ¬ (y (2 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_184 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 4 && y (1 : ℤ) 7) = true) ∧ ¬ (y (1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_185 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-7 : ℤ) 2 && y (-7 : ℤ) 7) = true) ∧ ¬ ((y (-5 : ℤ) 0 && y (-5 : ℤ) 5) = true) ∧ ¬ ((y (-6 : ℤ) 1 && y (-6 : ℤ) 6) = true)) := by
  classical
  have g_cov_5_m5 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (-5 : ℤ)
  norm_num at g_cov_5_m5
  have hh := g_cov_5_m5
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_186 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-5 : ℤ) 0 && y (-5 : ℤ) 5) = true) ∧ ¬ (y (-5 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_187 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-6 : ℤ) 1 && y (-6 : ℤ) 6) = true) ∧ ¬ (y (-6 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_188 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-7 : ℤ) 2 = true) ∧ ((y (-7 : ℤ) 2 && y (-7 : ℤ) 7) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_189 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-4 : ℤ) 2 && y (-4 : ℤ) 7) = true) ∧ ¬ ((y (-3 : ℤ) 1 && y (-3 : ℤ) 6) = true) ∧ ¬ ((y (-2 : ℤ) 0 && y (-2 : ℤ) 5) = true)) := by
  classical
  have g_cov_5_m2 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (-2 : ℤ)
  norm_num at g_cov_5_m2
  have hh := g_cov_5_m2
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_190 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 0 && y (-2 : ℤ) 5) = true) ∧ ¬ (y (-2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_191 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 1 && y (-3 : ℤ) 6) = true) ∧ ¬ (y (-3 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_192 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 1 && y (-3 : ℤ) 6) = true) ∧ ¬ (y (-3 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_193 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-4 : ℤ) 2 = true) ∧ ((y (-4 : ℤ) 2 && y (-4 : ℤ) 7) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_194 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 6) = true) ∧ ¬ ((y (-3 : ℤ) 2 && y (-3 : ℤ) 7) = true) ∧ ¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 5) = true)) := by
  classical
  have g_cov_5_m1 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (-1 : ℤ)
  norm_num at g_cov_5_m1
  have hh := g_cov_5_m1
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_195 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 5) = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_196 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 1 && y (-2 : ℤ) 6) = true) ∧ ¬ (y (-2 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_197 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 2 && y (-3 : ℤ) 7) = true) ∧ ¬ (y (-3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_198 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 0 && y (0 : ℤ) 5) = true) ∧ ¬ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ∧ ¬ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_0 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (0 : ℤ)
  norm_num at g_cov_5_0
  have hh := g_cov_5_0
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_199 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_200 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_201 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_202 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_203 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_204 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ∧ ¬ ((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true) ∧ ¬ ((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true)) := by
  classical
  have g_cov_5_1 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (1 : ℤ)
  norm_num at g_cov_5_1
  have hh := g_cov_5_1
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_205 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ∧ ¬ (y (1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_206 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true) ∧ ¬ (y (0 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_207 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true) ∧ ¬ (y (-1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_208 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ∧ ¬ ((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_2 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (2 : ℤ)
  norm_num at g_cov_5_2
  have hh := g_cov_5_2
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_209 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ∧ ¬ (y (2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_210 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ∧ ¬ (y (1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_211 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ∧ ¬ (y (1 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_212 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true) ∧ ¬ (y (0 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_213 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ∧ ¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true)) := by
  classical
  have g_cov_5_3 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (3 : ℤ)
  norm_num at g_cov_5_3
  have hh := g_cov_5_3
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_214 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true) ∧ ¬ (y (3 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_215 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true) ∧ ¬ (y (2 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_216 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ∧ ¬ (y (1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_217 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 5) = true) ∧ ¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 6) = true) ∧ ¬ ((y (2 : ℤ) 2 && y (2 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_4 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (4 : ℤ)
  norm_num at g_cov_5_4
  have hh := g_cov_5_4
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_218 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 5 = true) ∧ ((y (4 : ℤ) 0 && y (4 : ℤ) 5) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_219 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 6) = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_220 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 2 && y (2 : ℤ) 7) = true) ∧ ¬ (y (2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_221 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 2 && y (2 : ℤ) 7) = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_222 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (5 : ℤ) 0 && y (5 : ℤ) 5) = true) ∧ ¬ ((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ ¬ ((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_5 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (5 : ℤ)
  norm_num at g_cov_5_5
  have hh := g_cov_5_5
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_223 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 0 && y (5 : ℤ) 5) = true) ∧ ¬ (y (5 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_224 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ ¬ (y (4 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_225 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ ¬ (y (4 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_226 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ (y (4 : ℤ) 6 = true) ∧ (y (4 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_227 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true) ∧ ¬ (y (3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_228 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true) ∧ (y (3 : ℤ) 2 = true) ∧ (y (3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_229 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ∧ ¬ ((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true) ∧ ¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_6 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (6 : ℤ)
  norm_num at g_cov_5_6
  have hh := g_cov_5_6
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_230 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true) ∧ ¬ (y (6 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_231 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ∧ ¬ (y (5 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_232 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true) ∧ ¬ (y (4 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_233 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true) ∧ (y (4 : ℤ) 2 = true) ∧ (y (4 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_234 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (7 : ℤ) 0 && y (7 : ℤ) 5) = true) ∧ ¬ ((y (6 : ℤ) 1 && y (6 : ℤ) 6) = true) ∧ ¬ ((y (5 : ℤ) 2 && y (5 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_7 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (7 : ℤ)
  norm_num at g_cov_5_7
  have hh := g_cov_5_7
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_upper_clause895_235 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (7 : ℤ) 0 && y (7 : ℤ) 5) = true) ∧ ¬ (y (7 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_236 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 1 && y (6 : ℤ) 6) = true) ∧ ¬ (y (6 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_237 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 2 && y (5 : ℤ) 7) = true) ∧ ¬ (y (5 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_238 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 1 && y (-3 : ℤ) 7) = true) ∧ ((y (-2 : ℤ) 0 && y (-2 : ℤ) 6) = true)) := by
  classical
  have g_ex_1_m2 := h.2.1 1 (by omega) (-2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_m2
  have hh := g_ex_1_m2
  have hb0 : ((y (-2 : ℤ) 0 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 0 && y (-2 : ℤ) 6) <;> decide
  have hb1 : ((y (-3 : ℤ) 1 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 1 && y (-3 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_239 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 0 && y (-2 : ℤ) 6) = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (-2 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_240 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 1 = true) ∧ ¬ ((y (-3 : ℤ) 1 && y (-3 : ℤ) 7) = true) ∧ (y (-3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_241 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 6) = true) ∧ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_m1 := h.2.1 1 (by omega) (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_m1
  have hh := g_ex_1_m1
  have hb0 : ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6)).toNat ≤ 1 := by cases (y (-1 : ℤ) 0 && y (-1 : ℤ) 6) <;> decide
  have hb1 : ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7)).toNat ≤ 1 := by cases (y (-2 : ℤ) 1 && y (-2 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_242 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6) = true) ∧ ¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_m1 := h.2.1 1 (by omega) (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_m1
  have hh := g_ex_1_m1
  have hb0 : ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6)).toNat ≤ 1 := by cases (y (-1 : ℤ) 0 && y (-1 : ℤ) 6) <;> decide
  have hb1 : ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7)).toNat ≤ 1 := by cases (y (-2 : ℤ) 1 && y (-2 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_243 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-1 : ℤ) 6 = true) ∧ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_244 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 6 = true) ∧ ¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6) = true) ∧ (y (-1 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_245 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 1 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_246 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7) = true) ∧ (y (-2 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_247 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 6) = true) ∧ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_0 := h.2.1 1 (by omega) (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_0
  have hh := g_ex_1_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 6)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 6) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 7)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_248 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 6 = true) ∧ ¬ ((y (0 : ℤ) 0 && y (0 : ℤ) 6) = true) ∧ (y (0 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_249 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 7) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_250 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 0 && y (2 : ℤ) 6) = true) ∧ ((y (1 : ℤ) 1 && y (1 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_2 := h.2.1 1 (by omega) (2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_2
  have hh := g_ex_1_2
  have hb0 : ((y (2 : ℤ) 0 && y (2 : ℤ) 6)).toNat ≤ 1 := by cases (y (2 : ℤ) 0 && y (2 : ℤ) 6) <;> decide
  have hb1 : ((y (1 : ℤ) 1 && y (1 : ℤ) 7)).toNat ≤ 1 := by cases (y (1 : ℤ) 1 && y (1 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_251 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 1 && y (1 : ℤ) 7) = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 6) = true)) := by
  classical
  have g_ex_1_2 := h.2.1 1 (by omega) (2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_2
  have hh := g_ex_1_2
  have hb0 : ((y (2 : ℤ) 0 && y (2 : ℤ) 6)).toNat ≤ 1 := by cases (y (2 : ℤ) 0 && y (2 : ℤ) 6) <;> decide
  have hb1 : ((y (1 : ℤ) 1 && y (1 : ℤ) 7)).toNat ≤ 1 := by cases (y (1 : ℤ) 1 && y (1 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_252 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 6 = true) ∧ ((y (2 : ℤ) 0 && y (2 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_253 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 6 = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 6) = true) ∧ (y (2 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_254 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 1 && y (1 : ℤ) 7) = true) ∧ ¬ (y (1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_255 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 1 && y (1 : ℤ) 7) = true) ∧ (y (1 : ℤ) 1 = true) ∧ (y (1 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_256 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ∧ ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_3 := h.2.1 1 (by omega) (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_3
  have hh := g_ex_1_3
  have hb0 : ((y (3 : ℤ) 0 && y (3 : ℤ) 6)).toNat ≤ 1 := by cases (y (3 : ℤ) 0 && y (3 : ℤ) 6) <;> decide
  have hb1 : ((y (2 : ℤ) 1 && y (2 : ℤ) 7)).toNat ≤ 1 := by cases (y (2 : ℤ) 1 && y (2 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_257 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 6 = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ∧ (y (3 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_258 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true) ∧ (y (2 : ℤ) 1 = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_259 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ∧ ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_4 := h.2.1 1 (by omega) (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_4
  have hh := g_ex_1_4
  have hb0 : ((y (4 : ℤ) 0 && y (4 : ℤ) 6)).toNat ≤ 1 := by cases (y (4 : ℤ) 0 && y (4 : ℤ) 6) <;> decide
  have hb1 : ((y (3 : ℤ) 1 && y (3 : ℤ) 7)).toNat ≤ 1 := by cases (y (3 : ℤ) 1 && y (3 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_260 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ∧ ¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_4 := h.2.1 1 (by omega) (4 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_4
  have hh := g_ex_1_4
  have hb0 : ((y (4 : ℤ) 0 && y (4 : ℤ) 6)).toNat ≤ 1 := by cases (y (4 : ℤ) 0 && y (4 : ℤ) 6) <;> decide
  have hb1 : ((y (3 : ℤ) 1 && y (3 : ℤ) 7)).toNat ≤ 1 := by cases (y (3 : ℤ) 1 && y (3 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_261 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 6 = true) ∧ ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_262 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (4 : ℤ) 6 = true) ∧ ¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_263 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_264 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_265 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_266 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ∧ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_267 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ∧ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_268 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ∧ (e (0 : ℤ) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_269 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_270 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_271 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ (e (0 : ℤ) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_272 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ∧ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_273 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ∧ (e (0 : ℤ) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_274 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) ∧ (e (0 : ℤ) = true)) := by
  classical
  have g_ex_2_0 := h.2.2.1 (0 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_0
  have hh := g_ex_2_0
  have hb0 : ((y (0 : ℤ) 0 && y (0 : ℤ) 4)).toNat ≤ 1 := by cases (y (0 : ℤ) 0 && y (0 : ℤ) 4) <;> decide
  have hb1 : ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5)).toNat ≤ 1 := by cases (y (-1 : ℤ) 1 && y (-1 : ℤ) 5) <;> decide
  have hb2 : ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6)).toNat ≤ 1 := by cases (y (-2 : ℤ) 2 && y (-2 : ℤ) 6) <;> decide
  have hb3 : ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7)).toNat ≤ 1 := by cases (y (-3 : ℤ) 3 && y (-3 : ℤ) 7) <;> decide
  have hb4 : (e (0 : ℤ)).toNat ≤ 1 := by cases e (0 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_275 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 4 = true) ∧ ¬ ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ∧ (y (0 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_276 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ ¬ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ (y (-1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_277 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (-2 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_278 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) ∧ (y (-3 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_279 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 3 && y (-2 : ℤ) 7) = true) ∧ ((y (1 : ℤ) 0 && y (1 : ℤ) 4) = true)) := by
  classical
  have g_ex_2_1 := h.2.2.1 (1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_1
  have hh := g_ex_2_1
  have hb0 : ((y (1 : ℤ) 0 && y (1 : ℤ) 4)).toNat ≤ 1 := by cases (y (1 : ℤ) 0 && y (1 : ℤ) 4) <;> decide
  have hb1 : ((y (0 : ℤ) 1 && y (0 : ℤ) 5)).toNat ≤ 1 := by cases (y (0 : ℤ) 1 && y (0 : ℤ) 5) <;> decide
  have hb2 : ((y (-1 : ℤ) 2 && y (-1 : ℤ) 6)).toNat ≤ 1 := by cases (y (-1 : ℤ) 2 && y (-1 : ℤ) 6) <;> decide
  have hb3 : ((y (-2 : ℤ) 3 && y (-2 : ℤ) 7)).toNat ≤ 1 := by cases (y (-2 : ℤ) 3 && y (-2 : ℤ) 7) <;> decide
  have hb4 : (e (1 : ℤ)).toNat ≤ 1 := by cases e (1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_280 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 3 && y (-2 : ℤ) 7) = true) ∧ ((y (0 : ℤ) 1 && y (0 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_1 := h.2.2.1 (1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_1
  have hh := g_ex_2_1
  have hb0 : ((y (1 : ℤ) 0 && y (1 : ℤ) 4)).toNat ≤ 1 := by cases (y (1 : ℤ) 0 && y (1 : ℤ) 4) <;> decide
  have hb1 : ((y (0 : ℤ) 1 && y (0 : ℤ) 5)).toNat ≤ 1 := by cases (y (0 : ℤ) 1 && y (0 : ℤ) 5) <;> decide
  have hb2 : ((y (-1 : ℤ) 2 && y (-1 : ℤ) 6)).toNat ≤ 1 := by cases (y (-1 : ℤ) 2 && y (-1 : ℤ) 6) <;> decide
  have hb3 : ((y (-2 : ℤ) 3 && y (-2 : ℤ) 7)).toNat ≤ 1 := by cases (y (-2 : ℤ) 3 && y (-2 : ℤ) 7) <;> decide
  have hb4 : (e (1 : ℤ)).toNat ≤ 1 := by cases e (1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_281 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 0 && y (1 : ℤ) 4) = true) ∧ (y (1 : ℤ) 4 = true) ∧ (y (1 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_282 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 1 && y (0 : ℤ) 5) = true) ∧ (y (0 : ℤ) 1 = true) ∧ (y (0 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_283 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 3 = true) ∧ ¬ ((y (-2 : ℤ) 3 && y (-2 : ℤ) 7) = true) ∧ (y (-2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_284 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 0 && y (2 : ℤ) 4) = true) ∧ ((y (-1 : ℤ) 3 && y (-1 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_2 := h.2.2.1 (2 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_2
  have hh := g_ex_2_2
  have hb0 : ((y (2 : ℤ) 0 && y (2 : ℤ) 4)).toNat ≤ 1 := by cases (y (2 : ℤ) 0 && y (2 : ℤ) 4) <;> decide
  have hb1 : ((y (1 : ℤ) 1 && y (1 : ℤ) 5)).toNat ≤ 1 := by cases (y (1 : ℤ) 1 && y (1 : ℤ) 5) <;> decide
  have hb2 : ((y (0 : ℤ) 2 && y (0 : ℤ) 6)).toNat ≤ 1 := by cases (y (0 : ℤ) 2 && y (0 : ℤ) 6) <;> decide
  have hb3 : ((y (-1 : ℤ) 3 && y (-1 : ℤ) 7)).toNat ≤ 1 := by cases (y (-1 : ℤ) 3 && y (-1 : ℤ) 7) <;> decide
  have hb4 : (e (2 : ℤ)).toNat ≤ 1 := by cases e (2 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_285 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 4 = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 4) = true) ∧ (y (2 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_286 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-1 : ℤ) 3 && y (-1 : ℤ) 7) = true) ∧ (y (-1 : ℤ) 3 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_287 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 2 && y (3 : ℤ) 6) = true) ∧ ((y (4 : ℤ) 1 && y (4 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_5 := h.2.2.1 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_5
  have hh := g_ex_2_5
  have hb0 : ((y (5 : ℤ) 0 && y (5 : ℤ) 4)).toNat ≤ 1 := by cases (y (5 : ℤ) 0 && y (5 : ℤ) 4) <;> decide
  have hb1 : ((y (4 : ℤ) 1 && y (4 : ℤ) 5)).toNat ≤ 1 := by cases (y (4 : ℤ) 1 && y (4 : ℤ) 5) <;> decide
  have hb2 : ((y (3 : ℤ) 2 && y (3 : ℤ) 6)).toNat ≤ 1 := by cases (y (3 : ℤ) 2 && y (3 : ℤ) 6) <;> decide
  have hb3 : ((y (2 : ℤ) 3 && y (2 : ℤ) 7)).toNat ≤ 1 := by cases (y (2 : ℤ) 3 && y (2 : ℤ) 7) <;> decide
  have hb4 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_288 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 3 && y (2 : ℤ) 7) = true) ∧ ((y (4 : ℤ) 1 && y (4 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_5 := h.2.2.1 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_5
  have hh := g_ex_2_5
  have hb0 : ((y (5 : ℤ) 0 && y (5 : ℤ) 4)).toNat ≤ 1 := by cases (y (5 : ℤ) 0 && y (5 : ℤ) 4) <;> decide
  have hb1 : ((y (4 : ℤ) 1 && y (4 : ℤ) 5)).toNat ≤ 1 := by cases (y (4 : ℤ) 1 && y (4 : ℤ) 5) <;> decide
  have hb2 : ((y (3 : ℤ) 2 && y (3 : ℤ) 6)).toNat ≤ 1 := by cases (y (3 : ℤ) 2 && y (3 : ℤ) 6) <;> decide
  have hb3 : ((y (2 : ℤ) 3 && y (2 : ℤ) 7)).toNat ≤ 1 := by cases (y (2 : ℤ) 3 && y (2 : ℤ) 7) <;> decide
  have hb4 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_289 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (5 : ℤ) = true) ∧ ((y (4 : ℤ) 1 && y (4 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_5 := h.2.2.1 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_5
  have hh := g_ex_2_5
  have hb0 : ((y (5 : ℤ) 0 && y (5 : ℤ) 4)).toNat ≤ 1 := by cases (y (5 : ℤ) 0 && y (5 : ℤ) 4) <;> decide
  have hb1 : ((y (4 : ℤ) 1 && y (4 : ℤ) 5)).toNat ≤ 1 := by cases (y (4 : ℤ) 1 && y (4 : ℤ) 5) <;> decide
  have hb2 : ((y (3 : ℤ) 2 && y (3 : ℤ) 6)).toNat ≤ 1 := by cases (y (3 : ℤ) 2 && y (3 : ℤ) 6) <;> decide
  have hb3 : ((y (2 : ℤ) 3 && y (2 : ℤ) 7)).toNat ≤ 1 := by cases (y (2 : ℤ) 3 && y (2 : ℤ) 7) <;> decide
  have hb4 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_290 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 3 && y (2 : ℤ) 7) = true) ∧ ((y (3 : ℤ) 2 && y (3 : ℤ) 6) = true)) := by
  classical
  have g_ex_2_5 := h.2.2.1 (5 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_5
  have hh := g_ex_2_5
  have hb0 : ((y (5 : ℤ) 0 && y (5 : ℤ) 4)).toNat ≤ 1 := by cases (y (5 : ℤ) 0 && y (5 : ℤ) 4) <;> decide
  have hb1 : ((y (4 : ℤ) 1 && y (4 : ℤ) 5)).toNat ≤ 1 := by cases (y (4 : ℤ) 1 && y (4 : ℤ) 5) <;> decide
  have hb2 : ((y (3 : ℤ) 2 && y (3 : ℤ) 6)).toNat ≤ 1 := by cases (y (3 : ℤ) 2 && y (3 : ℤ) 6) <;> decide
  have hb3 : ((y (2 : ℤ) 3 && y (2 : ℤ) 7)).toNat ≤ 1 := by cases (y (2 : ℤ) 3 && y (2 : ℤ) 7) <;> decide
  have hb4 : (e (5 : ℤ)).toNat ≤ 1 := by cases e (5 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_291 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 1 && y (4 : ℤ) 5) = true) ∧ (y (4 : ℤ) 5 = true) ∧ (y (4 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_292 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 2 = true) ∧ ¬ ((y (3 : ℤ) 2 && y (3 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_293 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 3 = true) ∧ ¬ ((y (2 : ℤ) 3 && y (2 : ℤ) 7) = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_294 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 2 && y (4 : ℤ) 6) = true) ∧ ((y (5 : ℤ) 1 && y (5 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_6 := h.2.2.1 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_6
  have hh := g_ex_2_6
  have hb0 : ((y (6 : ℤ) 0 && y (6 : ℤ) 4)).toNat ≤ 1 := by cases (y (6 : ℤ) 0 && y (6 : ℤ) 4) <;> decide
  have hb1 : ((y (5 : ℤ) 1 && y (5 : ℤ) 5)).toNat ≤ 1 := by cases (y (5 : ℤ) 1 && y (5 : ℤ) 5) <;> decide
  have hb2 : ((y (4 : ℤ) 2 && y (4 : ℤ) 6)).toNat ≤ 1 := by cases (y (4 : ℤ) 2 && y (4 : ℤ) 6) <;> decide
  have hb3 : ((y (3 : ℤ) 3 && y (3 : ℤ) 7)).toNat ≤ 1 := by cases (y (3 : ℤ) 3 && y (3 : ℤ) 7) <;> decide
  have hb4 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_295 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 1 && y (5 : ℤ) 5) = true) ∧ ((y (3 : ℤ) 3 && y (3 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_6 := h.2.2.1 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_6
  have hh := g_ex_2_6
  have hb0 : ((y (6 : ℤ) 0 && y (6 : ℤ) 4)).toNat ≤ 1 := by cases (y (6 : ℤ) 0 && y (6 : ℤ) 4) <;> decide
  have hb1 : ((y (5 : ℤ) 1 && y (5 : ℤ) 5)).toNat ≤ 1 := by cases (y (5 : ℤ) 1 && y (5 : ℤ) 5) <;> decide
  have hb2 : ((y (4 : ℤ) 2 && y (4 : ℤ) 6)).toNat ≤ 1 := by cases (y (4 : ℤ) 2 && y (4 : ℤ) 6) <;> decide
  have hb3 : ((y (3 : ℤ) 3 && y (3 : ℤ) 7)).toNat ≤ 1 := by cases (y (3 : ℤ) 3 && y (3 : ℤ) 7) <;> decide
  have hb4 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_296 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (6 : ℤ) = true) ∧ ((y (5 : ℤ) 1 && y (5 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_6 := h.2.2.1 (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_6
  have hh := g_ex_2_6
  have hb0 : ((y (6 : ℤ) 0 && y (6 : ℤ) 4)).toNat ≤ 1 := by cases (y (6 : ℤ) 0 && y (6 : ℤ) 4) <;> decide
  have hb1 : ((y (5 : ℤ) 1 && y (5 : ℤ) 5)).toNat ≤ 1 := by cases (y (5 : ℤ) 1 && y (5 : ℤ) 5) <;> decide
  have hb2 : ((y (4 : ℤ) 2 && y (4 : ℤ) 6)).toNat ≤ 1 := by cases (y (4 : ℤ) 2 && y (4 : ℤ) 6) <;> decide
  have hb3 : ((y (3 : ℤ) 3 && y (3 : ℤ) 7)).toNat ≤ 1 := by cases (y (3 : ℤ) 3 && y (3 : ℤ) 7) <;> decide
  have hb4 : (e (6 : ℤ)).toNat ≤ 1 := by cases e (6 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_upper_clause895_297 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (5 : ℤ) 5 = true) ∧ ¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 5) = true) ∧ (y (5 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_298 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 6) = true) ∧ (y (4 : ℤ) 2 = true) ∧ (y (4 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_clause895_299 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 3 && y (3 : ℤ) 7) = true) ∧ (y (3 : ℤ) 3 = true) ∧ (y (3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_lower_zero_split895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) :
    (Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≤
      (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat := by
  classical
  by_contra hn
  have bad := rt1_upper_cert895 (y (-8 : ℤ) 7 = true) (y (-7 : ℤ) 7 = true) (y (-7 : ℤ) 2 = true) (y (-7 : ℤ) 6 = true) (y (-6 : ℤ) 6 = true) (y (-6 : ℤ) 5 = true) (y (-5 : ℤ) 7 = true) (y (-5 : ℤ) 4 = true) (y (-5 : ℤ) 5 = true) (y (-4 : ℤ) 7 = true) (y (-4 : ℤ) 2 = true) (y (-4 : ℤ) 6 = true) (y (-4 : ℤ) 3 = true) (y (-4 : ℤ) 4 = true) (y (-3 : ℤ) 7 = true) (y (-3 : ℤ) 1 = true) (y (-3 : ℤ) 2 = true) (y (-3 : ℤ) 6 = true) (y (-3 : ℤ) 3 = true) (y (-3 : ℤ) 5 = true) (y (-2 : ℤ) 0 = true) (y (-2 : ℤ) 7 = true) (y (-2 : ℤ) 1 = true) (y (-2 : ℤ) 2 = true) (y (-2 : ℤ) 6 = true) (y (-2 : ℤ) 3 = true) (y (-2 : ℤ) 4 = true) (y (-2 : ℤ) 5 = true) (y (-1 : ℤ) 0 = true) (y (-1 : ℤ) 7 = true) (y (-1 : ℤ) 1 = true) (y (-1 : ℤ) 2 = true) (y (-1 : ℤ) 6 = true) (y (-1 : ℤ) 3 = true) (y (-1 : ℤ) 4 = true) (y (-1 : ℤ) 5 = true) (y (0 : ℤ) 0 = true) (y (0 : ℤ) 7 = true) (y (0 : ℤ) 1 = true) (y (0 : ℤ) 2 = true) (y (0 : ℤ) 6 = true) (y (0 : ℤ) 3 = true) (y (0 : ℤ) 4 = true) (y (0 : ℤ) 5 = true) (y (1 : ℤ) 0 = true) (y (1 : ℤ) 7 = true) (y (1 : ℤ) 1 = true) (y (1 : ℤ) 2 = true) (y (1 : ℤ) 6 = true) (y (1 : ℤ) 3 = true) (y (1 : ℤ) 4 = true) (y (1 : ℤ) 5 = true) (y (2 : ℤ) 0 = true) (y (2 : ℤ) 7 = true) (y (2 : ℤ) 1 = true) (y (2 : ℤ) 2 = true) (y (2 : ℤ) 6 = true) (y (2 : ℤ) 3 = true) (y (2 : ℤ) 4 = true) (y (2 : ℤ) 5 = true) (y (3 : ℤ) 0 = true) (y (3 : ℤ) 7 = true) (y (3 : ℤ) 1 = true) (y (3 : ℤ) 2 = true) (y (3 : ℤ) 6 = true) (y (3 : ℤ) 3 = true) (y (3 : ℤ) 4 = true) (y (3 : ℤ) 5 = true) (y (4 : ℤ) 0 = true) (y (4 : ℤ) 7 = true) (y (4 : ℤ) 1 = true) (y (4 : ℤ) 2 = true) (y (4 : ℤ) 6 = true) (y (4 : ℤ) 3 = true) (y (4 : ℤ) 4 = true) (y (4 : ℤ) 5 = true) (y (5 : ℤ) 0 = true) (y (5 : ℤ) 1 = true) (y (5 : ℤ) 2 = true) (y (5 : ℤ) 3 = true) (y (5 : ℤ) 5 = true) (y (6 : ℤ) 0 = true) (y (6 : ℤ) 1 = true) (y (6 : ℤ) 5 = true) (y (7 : ℤ) 0 = true) (y (7 : ℤ) 1 = true) (y (7 : ℤ) 5 = true) (y (8 : ℤ) 0 = true) ((y (-2 : ℤ) 0 && y (-2 : ℤ) 6) = true) ((y (-3 : ℤ) 1 && y (-3 : ℤ) 7) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 7) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 6) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 7) = true) ((y (2 : ℤ) 0 && y (2 : ℤ) 6) = true) ((y (1 : ℤ) 1 && y (1 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true) ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) (e (0 : ℤ) = true) ((y (1 : ℤ) 0 && y (1 : ℤ) 4) = true) ((y (0 : ℤ) 1 && y (0 : ℤ) 5) = true) ((y (-2 : ℤ) 3 && y (-2 : ℤ) 7) = true) ((y (2 : ℤ) 0 && y (2 : ℤ) 4) = true) ((y (-1 : ℤ) 3 && y (-1 : ℤ) 7) = true) (e (4 : ℤ) = true) ((y (4 : ℤ) 1 && y (4 : ℤ) 5) = true) ((y (3 : ℤ) 2 && y (3 : ℤ) 6) = true) ((y (2 : ℤ) 3 && y (2 : ℤ) 7) = true) (e (5 : ℤ) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 5) = true) ((y (4 : ℤ) 2 && y (4 : ℤ) 6) = true) ((y (3 : ℤ) 3 && y (3 : ℤ) 7) = true) (e (6 : ℤ) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 2) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 3) = true) ((y (-3 : ℤ) 2 && y (-3 : ℤ) 4) = true) ((y (-4 : ℤ) 3 && y (-4 : ℤ) 5) = true) ((y (-5 : ℤ) 4 && y (-5 : ℤ) 6) = true) ((y (-6 : ℤ) 5 && y (-6 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true) ((y (4 : ℤ) 0 && y (4 : ℤ) 2) = true) ((y (3 : ℤ) 1 && y (3 : ℤ) 3) = true) ((y (2 : ℤ) 2 && y (2 : ℤ) 4) = true) ((y (1 : ℤ) 3 && y (1 : ℤ) 5) = true) ((y (0 : ℤ) 4 && y (0 : ℤ) 6) = true) ((y (-1 : ℤ) 5 && y (-1 : ℤ) 7) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 3) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 4) = true) ((y (-3 : ℤ) 2 && y (-3 : ℤ) 5) = true) ((y (-4 : ℤ) 3 && y (-4 : ℤ) 6) = true) ((y (-5 : ℤ) 4 && y (-5 : ℤ) 7) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 3) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 4) = true) ((y (-2 : ℤ) 2 && y (-2 : ℤ) 5) = true) ((y (-3 : ℤ) 3 && y (-3 : ℤ) 6) = true) ((y (-4 : ℤ) 4 && y (-4 : ℤ) 7) = true) ((y (2 : ℤ) 0 && y (2 : ℤ) 3) = true) ((y (1 : ℤ) 1 && y (1 : ℤ) 4) = true) ((y (0 : ℤ) 2 && y (0 : ℤ) 5) = true) ((y (-1 : ℤ) 3 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 4 && y (-2 : ℤ) 7) = true) ((y (4 : ℤ) 0 && y (4 : ℤ) 3) = true) ((y (3 : ℤ) 1 && y (3 : ℤ) 4) = true) ((y (2 : ℤ) 2 && y (2 : ℤ) 5) = true) ((y (1 : ℤ) 3 && y (1 : ℤ) 6) = true) ((y (0 : ℤ) 4 && y (0 : ℤ) 7) = true) ((y (5 : ℤ) 0 && y (5 : ℤ) 3) = true) ((y (4 : ℤ) 1 && y (4 : ℤ) 4) = true) ((y (3 : ℤ) 2 && y (3 : ℤ) 5) = true) ((y (2 : ℤ) 3 && y (2 : ℤ) 6) = true) ((y (1 : ℤ) 4 && y (1 : ℤ) 7) = true) ((y (-5 : ℤ) 0 && y (-5 : ℤ) 5) = true) ((y (-6 : ℤ) 1 && y (-6 : ℤ) 6) = true) ((y (-7 : ℤ) 2 && y (-7 : ℤ) 7) = true) ((y (-2 : ℤ) 0 && y (-2 : ℤ) 5) = true) ((y (-3 : ℤ) 1 && y (-3 : ℤ) 6) = true) ((y (-4 : ℤ) 2 && y (-4 : ℤ) 7) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 5) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 6) = true) ((y (-3 : ℤ) 2 && y (-3 : ℤ) 7) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 5) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true) ((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true) ((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true) ((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true) ((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ((y (4 : ℤ) 0 && y (4 : ℤ) 5) = true) ((y (3 : ℤ) 1 && y (3 : ℤ) 6) = true) ((y (2 : ℤ) 2 && y (2 : ℤ) 7) = true) ((y (5 : ℤ) 0 && y (5 : ℤ) 5) = true) ((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true) ((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true) ((y (7 : ℤ) 0 && y (7 : ℤ) 5) = true) ((y (6 : ℤ) 1 && y (6 : ℤ) 6) = true) ((y (5 : ℤ) 2 && y (5 : ℤ) 7) = true)
  simp only [rt1_upper_clause895_0 y e h hn, rt1_upper_clause895_1 y e h hn, rt1_upper_clause895_2 y e h hn, rt1_upper_clause895_3 y e h hn, rt1_upper_clause895_4 y e h hn, rt1_upper_clause895_5 y e h hn, rt1_upper_clause895_6 y e h hn, rt1_upper_clause895_7 y e h hn, rt1_upper_clause895_8 y e h hn, rt1_upper_clause895_9 y e h hn, rt1_upper_clause895_10 y e h hn, rt1_upper_clause895_11 y e h hn, rt1_upper_clause895_12 y e h hn, rt1_upper_clause895_13 y e h hn, rt1_upper_clause895_14 y e h hn, rt1_upper_clause895_15 y e h hn, rt1_upper_clause895_16 y e h hn, rt1_upper_clause895_17 y e h hn, rt1_upper_clause895_18 y e h hn, rt1_upper_clause895_19 y e h hn, rt1_upper_clause895_20 y e h hn, rt1_upper_clause895_21 y e h hn, rt1_upper_clause895_22 y e h hn, rt1_upper_clause895_23 y e h hn, rt1_upper_clause895_24 y e h hn, rt1_upper_clause895_25 y e h hn, rt1_upper_clause895_26 y e h hn, rt1_upper_clause895_27 y e h hn, rt1_upper_clause895_28 y e h hn, rt1_upper_clause895_29 y e h hn, rt1_upper_clause895_30 y e h hn, rt1_upper_clause895_31 y e h hn, rt1_upper_clause895_32 y e h hn, rt1_upper_clause895_33 y e h hn, rt1_upper_clause895_34 y e h hn, rt1_upper_clause895_35 y e h hn, rt1_upper_clause895_36 y e h hn, rt1_upper_clause895_37 y e h hn, rt1_upper_clause895_38 y e h hn, rt1_upper_clause895_39 y e h hn, rt1_upper_clause895_40 y e h hn, rt1_upper_clause895_41 y e h hn, rt1_upper_clause895_42 y e h hn, rt1_upper_clause895_43 y e h hn, rt1_upper_clause895_44 y e h hn, rt1_upper_clause895_45 y e h hn, rt1_upper_clause895_46 y e h hn, rt1_upper_clause895_47 y e h hn, rt1_upper_clause895_48 y e h hn, rt1_upper_clause895_49 y e h hn, rt1_upper_clause895_50 y e h hn, rt1_upper_clause895_51 y e h hn, rt1_upper_clause895_52 y e h hn, rt1_upper_clause895_53 y e h hn, rt1_upper_clause895_54 y e h hn, rt1_upper_clause895_55 y e h hn, rt1_upper_clause895_56 y e h hn, rt1_upper_clause895_57 y e h hn, rt1_upper_clause895_58 y e h hn, rt1_upper_clause895_59 y e h hn, rt1_upper_clause895_60 y e h hn, rt1_upper_clause895_61 y e h hn, rt1_upper_clause895_62 y e h hn, rt1_upper_clause895_63 y e h hn, rt1_upper_clause895_64 y e h hn, rt1_upper_clause895_65 y e h hn, rt1_upper_clause895_66 y e h hn, rt1_upper_clause895_67 y e h hn, rt1_upper_clause895_68 y e h hn, rt1_upper_clause895_69 y e h hn, rt1_upper_clause895_70 y e h hn, rt1_upper_clause895_71 y e h hn, rt1_upper_clause895_72 y e h hn, rt1_upper_clause895_73 y e h hn, rt1_upper_clause895_74 y e h hn, rt1_upper_clause895_75 y e h hn, rt1_upper_clause895_76 y e h hn, rt1_upper_clause895_77 y e h hn, rt1_upper_clause895_78 y e h hn, rt1_upper_clause895_79 y e h hn, rt1_upper_clause895_80 y e h hn, rt1_upper_clause895_81 y e h hn, rt1_upper_clause895_82 y e h hn, rt1_upper_clause895_83 y e h hn, rt1_upper_clause895_84 y e h hn, rt1_upper_clause895_85 y e h hn, rt1_upper_clause895_86 y e h hn, rt1_upper_clause895_87 y e h hn, rt1_upper_clause895_88 y e h hn, rt1_upper_clause895_89 y e h hn, rt1_upper_clause895_90 y e h hn, rt1_upper_clause895_91 y e h hn, rt1_upper_clause895_92 y e h hn, rt1_upper_clause895_93 y e h hn, rt1_upper_clause895_94 y e h hn, rt1_upper_clause895_95 y e h hn, rt1_upper_clause895_96 y e h hn, rt1_upper_clause895_97 y e h hn, rt1_upper_clause895_98 y e h hn, rt1_upper_clause895_99 y e h hn, rt1_upper_clause895_100 y e h hn, rt1_upper_clause895_101 y e h hn, rt1_upper_clause895_102 y e h hn, rt1_upper_clause895_103 y e h hn, rt1_upper_clause895_104 y e h hn, rt1_upper_clause895_105 y e h hn, rt1_upper_clause895_106 y e h hn, rt1_upper_clause895_107 y e h hn, rt1_upper_clause895_108 y e h hn, rt1_upper_clause895_109 y e h hn, rt1_upper_clause895_110 y e h hn, rt1_upper_clause895_111 y e h hn, rt1_upper_clause895_112 y e h hn, rt1_upper_clause895_113 y e h hn, rt1_upper_clause895_114 y e h hn, rt1_upper_clause895_115 y e h hn, rt1_upper_clause895_116 y e h hn, rt1_upper_clause895_117 y e h hn, rt1_upper_clause895_118 y e h hn, rt1_upper_clause895_119 y e h hn, rt1_upper_clause895_120 y e h hn, rt1_upper_clause895_121 y e h hn, rt1_upper_clause895_122 y e h hn, rt1_upper_clause895_123 y e h hn, rt1_upper_clause895_124 y e h hn, rt1_upper_clause895_125 y e h hn, rt1_upper_clause895_126 y e h hn, rt1_upper_clause895_127 y e h hn, rt1_upper_clause895_128 y e h hn, rt1_upper_clause895_129 y e h hn, rt1_upper_clause895_130 y e h hn, rt1_upper_clause895_131 y e h hn, rt1_upper_clause895_132 y e h hn, rt1_upper_clause895_133 y e h hn, rt1_upper_clause895_134 y e h hn, rt1_upper_clause895_135 y e h hn, rt1_upper_clause895_136 y e h hn, rt1_upper_clause895_137 y e h hn, rt1_upper_clause895_138 y e h hn, rt1_upper_clause895_139 y e h hn, rt1_upper_clause895_140 y e h hn, rt1_upper_clause895_141 y e h hn, rt1_upper_clause895_142 y e h hn, rt1_upper_clause895_143 y e h hn, rt1_upper_clause895_144 y e h hn, rt1_upper_clause895_145 y e h hn, rt1_upper_clause895_146 y e h hn, rt1_upper_clause895_147 y e h hn, rt1_upper_clause895_148 y e h hn, rt1_upper_clause895_149 y e h hn, rt1_upper_clause895_150 y e h hn, rt1_upper_clause895_151 y e h hn, rt1_upper_clause895_152 y e h hn, rt1_upper_clause895_153 y e h hn, rt1_upper_clause895_154 y e h hn, rt1_upper_clause895_155 y e h hn, rt1_upper_clause895_156 y e h hn, rt1_upper_clause895_157 y e h hn, rt1_upper_clause895_158 y e h hn, rt1_upper_clause895_159 y e h hn, rt1_upper_clause895_160 y e h hn, rt1_upper_clause895_161 y e h hn, rt1_upper_clause895_162 y e h hn, rt1_upper_clause895_163 y e h hn, rt1_upper_clause895_164 y e h hn, rt1_upper_clause895_165 y e h hn, rt1_upper_clause895_166 y e h hn, rt1_upper_clause895_167 y e h hn, rt1_upper_clause895_168 y e h hn, rt1_upper_clause895_169 y e h hn, rt1_upper_clause895_170 y e h hn, rt1_upper_clause895_171 y e h hn, rt1_upper_clause895_172 y e h hn, rt1_upper_clause895_173 y e h hn, rt1_upper_clause895_174 y e h hn, rt1_upper_clause895_175 y e h hn, rt1_upper_clause895_176 y e h hn, rt1_upper_clause895_177 y e h hn, rt1_upper_clause895_178 y e h hn, rt1_upper_clause895_179 y e h hn, rt1_upper_clause895_180 y e h hn, rt1_upper_clause895_181 y e h hn, rt1_upper_clause895_182 y e h hn, rt1_upper_clause895_183 y e h hn, rt1_upper_clause895_184 y e h hn, rt1_upper_clause895_185 y e h hn, rt1_upper_clause895_186 y e h hn, rt1_upper_clause895_187 y e h hn, rt1_upper_clause895_188 y e h hn, rt1_upper_clause895_189 y e h hn, rt1_upper_clause895_190 y e h hn, rt1_upper_clause895_191 y e h hn, rt1_upper_clause895_192 y e h hn, rt1_upper_clause895_193 y e h hn, rt1_upper_clause895_194 y e h hn, rt1_upper_clause895_195 y e h hn, rt1_upper_clause895_196 y e h hn, rt1_upper_clause895_197 y e h hn, rt1_upper_clause895_198 y e h hn, rt1_upper_clause895_199 y e h hn, rt1_upper_clause895_200 y e h hn, rt1_upper_clause895_201 y e h hn, rt1_upper_clause895_202 y e h hn, rt1_upper_clause895_203 y e h hn, rt1_upper_clause895_204 y e h hn, rt1_upper_clause895_205 y e h hn, rt1_upper_clause895_206 y e h hn, rt1_upper_clause895_207 y e h hn, rt1_upper_clause895_208 y e h hn, rt1_upper_clause895_209 y e h hn, rt1_upper_clause895_210 y e h hn, rt1_upper_clause895_211 y e h hn, rt1_upper_clause895_212 y e h hn, rt1_upper_clause895_213 y e h hn, rt1_upper_clause895_214 y e h hn, rt1_upper_clause895_215 y e h hn, rt1_upper_clause895_216 y e h hn, rt1_upper_clause895_217 y e h hn, rt1_upper_clause895_218 y e h hn, rt1_upper_clause895_219 y e h hn, rt1_upper_clause895_220 y e h hn, rt1_upper_clause895_221 y e h hn, rt1_upper_clause895_222 y e h hn, rt1_upper_clause895_223 y e h hn, rt1_upper_clause895_224 y e h hn, rt1_upper_clause895_225 y e h hn, rt1_upper_clause895_226 y e h hn, rt1_upper_clause895_227 y e h hn, rt1_upper_clause895_228 y e h hn, rt1_upper_clause895_229 y e h hn, rt1_upper_clause895_230 y e h hn, rt1_upper_clause895_231 y e h hn, rt1_upper_clause895_232 y e h hn, rt1_upper_clause895_233 y e h hn, rt1_upper_clause895_234 y e h hn, rt1_upper_clause895_235 y e h hn, rt1_upper_clause895_236 y e h hn, rt1_upper_clause895_237 y e h hn, rt1_upper_clause895_238 y e h hn, rt1_upper_clause895_239 y e h hn, rt1_upper_clause895_240 y e h hn, rt1_upper_clause895_241 y e h hn, rt1_upper_clause895_242 y e h hn, rt1_upper_clause895_243 y e h hn, rt1_upper_clause895_244 y e h hn, rt1_upper_clause895_245 y e h hn, rt1_upper_clause895_246 y e h hn, rt1_upper_clause895_247 y e h hn, rt1_upper_clause895_248 y e h hn, rt1_upper_clause895_249 y e h hn, rt1_upper_clause895_250 y e h hn, rt1_upper_clause895_251 y e h hn, rt1_upper_clause895_252 y e h hn, rt1_upper_clause895_253 y e h hn, rt1_upper_clause895_254 y e h hn, rt1_upper_clause895_255 y e h hn, rt1_upper_clause895_256 y e h hn, rt1_upper_clause895_257 y e h hn, rt1_upper_clause895_258 y e h hn, rt1_upper_clause895_259 y e h hn, rt1_upper_clause895_260 y e h hn, rt1_upper_clause895_261 y e h hn, rt1_upper_clause895_262 y e h hn, rt1_upper_clause895_263 y e h hn, rt1_upper_clause895_264 y e h hn, rt1_upper_clause895_265 y e h hn, rt1_upper_clause895_266 y e h hn, rt1_upper_clause895_267 y e h hn, rt1_upper_clause895_268 y e h hn, rt1_upper_clause895_269 y e h hn, rt1_upper_clause895_270 y e h hn, rt1_upper_clause895_271 y e h hn, rt1_upper_clause895_272 y e h hn, rt1_upper_clause895_273 y e h hn, rt1_upper_clause895_274 y e h hn, rt1_upper_clause895_275 y e h hn, rt1_upper_clause895_276 y e h hn, rt1_upper_clause895_277 y e h hn, rt1_upper_clause895_278 y e h hn, rt1_upper_clause895_279 y e h hn, rt1_upper_clause895_280 y e h hn, rt1_upper_clause895_281 y e h hn, rt1_upper_clause895_282 y e h hn, rt1_upper_clause895_283 y e h hn, rt1_upper_clause895_284 y e h hn, rt1_upper_clause895_285 y e h hn, rt1_upper_clause895_286 y e h hn, rt1_upper_clause895_287 y e h hn, rt1_upper_clause895_288 y e h hn, rt1_upper_clause895_289 y e h hn, rt1_upper_clause895_290 y e h hn, rt1_upper_clause895_291 y e h hn, rt1_upper_clause895_292 y e h hn, rt1_upper_clause895_293 y e h hn, rt1_upper_clause895_294 y e h hn, rt1_upper_clause895_295 y e h hn, rt1_upper_clause895_296 y e h hn, rt1_upper_clause895_297 y e h hn, rt1_upper_clause895_298 y e h hn, rt1_upper_clause895_299 y e h hn] at bad

  simp at bad

theorem rt1_model_shift_upper895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) :
    cycle_power_dyadic_defective_half_model 3 (fun p a => y (v+p) a) (fun p => e (v+p)) 0 := by
  rcases h with ⟨hw, hl, ht, hc, hn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw (v+p)
  · intro j hj p
    simpa only [add_sub_assoc] using hl j hj (v+p)
  · intro p
    simpa only [add_sub_assoc, add_zero] using ht (v+p)
  · intro d hd hd8 hd4 p
    obtain ⟨a,ha,ha1,ha2⟩ := hc d hd hd8 hd4 (v+p)
    refine ⟨a, ha, ?_, ?_⟩
    · simpa only [add_sub_assoc] using ha1
    · simpa only [add_sub_assoc] using ha2
  · intro p
    simpa only [add_sub_assoc] using hn (v+p)

theorem rt1_lower_window895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) :
    (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat ≤
      (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat := by
  have hs := rt1_model_shift_upper895 y e h v
  have hu := rt1_lower_zero_split895 (fun p a => y (v+p) a) (fun p => e (v+p)) hs
  simpa only [add_zero, zero_add, add_sub_assoc, zero_sub, sub_eq_add_neg, add_assoc] using hu

end RT1Lower895

theorem cycle_power_eight_corrected_count_lower_window (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) : (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat ≤ (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat := by
  exact RT1Lower895.rt1_lower_window895 y e h v
