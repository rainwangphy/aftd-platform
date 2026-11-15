import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.G

/-!
# cycle_power_eight_corrected_count_upper_window

Topic: combinatorics   Node: 604c3d81cbaf

Provenance: helper lemma. Finite-window ladder for thread RT-1 and arXiv:2610.15635; the compressed, externally verified CNF/LRAT and semantic variable mapping are recorded in the evidence experiments.

In every zero-phase defective half model of exponent three, the corrected lower count at v is at least its value at v+4.
-/

namespace RT1Upper895
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

lrat_proof rt1_lower_cert895
  "p cnf 140 204\n1 0\n2 0\n4 -3 0\n6 0\n9 -8 0\n7 -10 0\n11 0\n12 0\n-14 15 0\n-17 13 0\n18 0\n19 0\n22 -21 0\n20 -25 0\n26 0\n27 0\n-28 29 0\n32 0\n-37 33 0\n38 0\n39 0\n-41 42 0\n-45 40 0\n46 0\n47 0\n-49 50 0\n52 0\n53 0\n56 -55 0\n54 -59 0\n60 0\n-62 63 0\n61 -65 0\n67 0\n68 -69 0\n70 0\n-13 -8 30 34 -18 0\n-5 -13 34 40 -18 0\n-13 -5 30 40 -18 0\n-5 90 40 -13 -18 0\n-13 -5 30 34 -18 0\n-5 90 -13 34 -18 0\n-13 30 -5 90 -18 0\n-86 -13 34 40 -18 0\n-86 -13 30 40 -18 0\n-13 -86 40 90 -18 0\n-13 -86 30 34 -18 0\n-13 90 34 -86 -18 0\n-86 30 90 -13 -18 0\n30 34 -13 40 -18 0\n90 34 -13 40 -18 0\n30 90 -13 40 -18 0\n90 30 -13 34 -18 0\n30 40 34 -8 -18 0\n90 40 -8 34 -18 0\n30 -8 40 90 -18 0\n30 90 34 -8 -18 0\n30 40 34 -5 -18 0\n40 90 -5 34 -18 0\n40 30 -5 90 -18 0\n90 34 30 -5 -18 0\n-86 30 40 34 -18 0\n-86 90 40 34 -18 0\n-86 90 40 30 -18 0\n-86 90 34 30 -18 0\n90 34 30 40 -18 0\n-23 -4 -33 -38 -1 0\n-10 -4 -33 -38 -1 0\n-28 -23 -4 -38 -1 0\n23 33 16 10 89 28 0\n-34 -40 -30 -46 -2 0\n-34 -24 -40 -46 -2 0\n-17 -34 -40 -46 -2 0\n-9 -40 -34 -46 -2 0\n-90 -40 -34 -46 -2 0\n-24 -30 -40 -46 -2 0\n-17 -30 -40 -46 -2 0\n-30 -9 -40 -46 -2 0\n-90 -30 -40 -46 -2 0\n-40 -9 -24 -46 -2 0\n-90 -24 -40 -46 -2 0\n-17 -90 -40 -46 -2 0\n-90 -9 -40 -46 -2 0\n-30 -24 -34 -46 -2 0\n-17 -30 -34 -46 -2 0\n-30 -9 -34 -46 -2 0\n-34 -90 -30 -46 -2 0\n-9 -34 -24 -46 -2 0\n-90 -24 -34 -46 -2 0\n-90 -17 -34 -46 -2 0\n-90 -9 -34 -46 -2 0\n-30 -9 -24 -46 -2 0\n-90 -30 -24 -46 -2 0\n-90 -30 -17 -46 -2 0\n-90 -9 -30 -46 -2 0\n-90 -9 -24 -46 -2 0\n-35 -48 -25 -52 -6 0\n-41 -15 -25 -52 -6 0\n-15 -35 -25 -52 -6 0\n-43 -31 -54 -60 -12 0\n-43 -54 -22 -60 -12 0\n-36 -31 -54 -60 -12 0\n-36 -54 -22 -60 -12 0\n-31 -54 -22 -60 -12 0\n51 44 29 37 55 94 0\n-57 -66 -45 -67 -27 0\n-68 -64 -42 -70 -32 0\n-58 -68 -42 -70 -32 0\n96 98 100 97 95 99 0\n-95 41 0\n-96 35 0\n-97 28 0\n-98 23 0\n-99 16 0\n-100 10 0\n102 104 105 106 101 103 0\n-101 62 0\n57 -102 0\n-103 49 0\n-104 43 0\n-105 36 0\n-106 31 0\n108 107 110 109 111 0\n-107 43 0\n-108 36 0\n-109 28 0\n-110 23 0\n-111 16 0\n112 113 115 114 116 0\n-112 64 0\n-113 58 0\n-114 49 0\n-115 43 0\n-116 36 0\n118 119 117 0\n-117 17 0\n-118 9 0\n-119 3 0\n120 121 122 0\n25 -120 0\n-121 13 0\n-122 8 0\n123 124 125 0\n-123 31 0\n-124 22 0\n-125 14 0\n128 126 127 0\n-126 37 0\n-127 29 0\n21 -128 0\n130 131 129 0\n-129 45 0\n33 -130 0\n-131 28 0\n132 133 134 0\n59 -132 0\n-133 48 0\n-133 50 0\n-134 41 0\n135 136 137 0\n65 -135 0\n-136 54 0\n-137 49 0\n138 139 140 0\n69 -138 0\n-139 66 0\n-140 62 0\n-71 -72 0\n-29 71 -26 0\n72 -20 -19 0\n-73 -74 0\n73 74 0\n42 -73 0\n-42 73 -38 0\n-74 33 0\n74 -33 -32 0\n-75 -76 0\n-50 75 -46 0\n76 -40 -39 0\n-77 -78 0\n-63 77 -60 0\n78 -54 -53 0\n-79 -81 0\n-81 -80 0\n-16 79 -11 0\n80 -7 -10 0\n-3 81 -4 0\n82 85 86 83 84 0\n24 -82 0\n-83 13 0\n-83 17 0\n-84 8 0\n-84 9 0\n-85 5 0\n-87 -88 0\n-89 -87 0\n-44 87 -38 0\n88 -23 -19 0\n-92 -91 0\n-93 -91 0\n-94 -91 0\n91 -61 -65 0\n-56 -55 92 0\n93 -51 -47 0\n"
  "204 d 98 0\n205 -8 -13 30 34 0 11 37 0\n205 d 37 0\n206 -5 -13 34 40 0 11 38 0\n206 d 38 0\n207 -5 -13 30 40 0 11 39 0\n207 d 39 0\n208 -5 -13 40 90 0 11 40 0\n208 d 40 0\n209 -5 -13 30 34 0 11 41 0\n209 d 41 0\n210 -5 -13 34 90 0 11 42 0\n210 d 42 0\n211 -5 -13 30 90 0 11 43 0\n211 d 43 0\n212 -13 34 40 -86 0 11 44 0\n212 d 44 0\n213 -13 30 40 -86 0 11 45 0\n213 d 45 0\n214 -13 40 -86 90 0 11 46 0\n214 d 46 0\n215 -13 30 34 -86 0 11 47 0\n215 d 47 0\n216 -13 34 -86 90 0 11 48 0\n216 d 48 0\n217 -13 30 -86 90 0 11 49 0\n217 d 49 0\n218 -13 30 34 40 0 11 50 0\n218 d 50 0\n219 -13 34 40 90 0 11 51 0\n219 d 51 0\n220 -13 30 40 90 0 11 52 0\n220 d 52 0\n221 -13 30 34 90 0 11 53 0\n221 d 53 0\n222 -8 30 34 40 0 11 54 0\n222 d 54 0\n223 -8 34 40 90 0 11 55 0\n223 d 55 0\n224 -8 30 40 90 0 11 56 0\n224 d 56 0\n225 -8 30 34 90 0 11 57 0\n225 d 57 0\n226 -5 30 34 40 0 11 58 0\n226 d 58 0\n227 -5 34 40 90 0 11 59 0\n227 d 59 0\n228 -5 30 40 90 0 11 60 0\n228 d 60 0\n229 -5 30 34 90 0 11 61 0\n229 d 61 0\n230 30 34 40 -86 0 11 62 0\n230 d 62 0\n231 34 40 -86 90 0 11 63 0\n231 d 63 0\n232 30 40 -86 90 0 11 64 0\n232 d 64 0\n233 30 34 -86 90 0 11 65 0\n233 d 65 0\n234 30 34 40 90 0 11 66 0\n234 d 66 0\n235 -4 -23 -33 0 1 20 67 0\n235 d 67 0\n236 -4 -10 -33 0 1 20 68 0\n236 d 68 0\n237 -4 -23 -28 0 1 20 69 0\n237 d 69 0\n238 -30 -34 -40 0 2 24 71 0\n238 d 71 0\n239 -24 -34 -40 0 2 24 72 0\n239 d 72 0\n240 -17 -34 -40 0 2 24 73 0\n240 d 73 0\n241 -9 -34 -40 0 2 24 74 0\n241 d 74 0\n242 -34 -40 -90 0 2 24 75 0\n242 d 75 0\n243 -24 -30 -40 0 2 24 76 0\n243 d 76 0\n244 -17 -30 -40 0 2 24 77 0\n244 d 77 0\n245 -9 -30 -40 0 2 24 78 0\n245 d 78 0\n246 -30 -40 -90 0 2 24 79 0\n246 d 79 0\n247 -9 -24 -40 0 2 24 80 0\n247 d 80 0\n248 -24 -40 -90 0 2 24 81 0\n248 d 81 0\n249 -17 -40 -90 0 2 24 82 0\n249 d 82 0\n250 -9 -40 -90 0 2 24 83 0\n250 d 83 0\n251 -24 -30 -34 0 2 24 84 0\n251 d 84 0\n252 -17 -30 -34 0 2 24 85 0\n252 d 85 0\n253 -9 -30 -34 0 2 24 86 0\n253 d 86 0\n254 -30 -34 -90 0 2 24 87 0\n254 d 87 0\n255 -9 -24 -34 0 2 24 88 0\n255 d 88 0\n256 -24 -34 -90 0 2 24 89 0\n256 d 89 0\n257 -17 -34 -90 0 2 24 90 0\n257 d 90 0\n258 -9 -34 -90 0 2 24 91 0\n258 d 91 0\n259 -9 -24 -30 0 2 24 92 0\n259 d 92 0\n260 -24 -30 -90 0 2 24 93 0\n260 d 93 0\n261 -17 -30 -90 0 2 24 94 0\n261 d 94 0\n262 -9 -30 -90 0 2 24 95 0\n262 d 95 0\n263 -9 -24 -90 0 2 24 96 0\n263 d 96 0\n264 -25 -35 -48 0 4 27 97 0\n264 d 97 0\n266 -15 -25 -35 0 4 27 99 0\n266 d 99 0\n267 -31 -43 -54 0 8 31 100 0\n267 d 100 0\n268 -22 -43 -54 0 8 31 101 0\n268 d 101 0\n269 -31 -36 -54 0 8 31 102 0\n269 d 102 0\n270 -22 -36 -54 0 8 31 103 0\n270 d 103 0\n271 -22 -31 -54 0 8 31 104 0\n271 d 104 0\n272 -45 -57 -66 0 16 34 106 0\n272 d 106 0\n273 -42 -64 -68 0 18 36 107 0\n273 d 107 0\n274 -42 -58 -68 0 18 36 108 0\n274 d 108 0\n275 -29 71 0 15 169 0\n275 d 169 0\n276 -20 72 0 12 170 0\n276 d 170 0\n277 -42 73 0 20 174 0\n277 d 174 0\n278 -33 74 0 18 176 0\n278 d 176 0\n279 -50 75 0 24 178 0\n279 d 178 0\n280 -40 76 0 21 179 0\n280 d 179 0\n281 -63 77 0 31 181 0\n281 d 181 0\n282 -54 78 0 28 182 0\n282 d 182 0\n283 -16 79 0 7 185 0\n283 d 185 0\n284 -44 87 0 20 197 0\n284 d 197 0\n285 -23 88 0 12 198 0\n285 d 198 0\n286 -51 93 0 25 204 0\n286 d 204 0\n287 -17 34 -40 0 10 249 221 244 0\n287 d 249 244 0\n288 -43 -54 125 0 268 145 143 144 267 0\n288 d 267 0\n289 125 -54 109 110 111 0 288 124 123 125 270 269 145 144 143 0\n289 d 288 124 123 125 269 145 144 143 0\n290 -30 -13 -40 0 245 193 246 243 189 238 287 191 210 194 188 216 0\n290 d 246 243 238 210 216 0\n291 34 -13 -40 83 0 290 209 194 215 205 192 188 189 221 248 0\n291 d 209 215 205 221 248 0\n292 83 -13 -40 0 291 290 242 239 241 217 211 189 193 188 194 0\n292 d 290 242 239 217 211 193 0\n293 -17 -40 0 240 287 0\n293 d 240 287 0\n294 90 30 34 82 83 84 0 229 194 188 233 0\n294 d 229 233 0\n295 30 -8 -9 34 0 225 250 222 0\n295 d 225 222 0\n296 34 -8 -9 0 295 245 262 223 0\n296 d 295 0\n297 -84 0 192 5 296 241 253 258 224 0\n297 d 192 296 0\n298 40 30 -34 90 0 297 224 232 220 228 23 142 141 10 190 194 152 139 136 188 140 189 14 255 276 137 168 135 275 138 17 3 187 154 112 126 183 151 283 153 128 114 278 235 236 171 113 127 115 277 22 159 110 109 111 264 266 157 9 155 146 156 289 30 0\n298 d 224 232 220 228 190 255 236 0\n299 -55 92 0 29 203 0\n299 d 29 203 0\n300 -10 80 0 6 186 0\n300 d 6 186 0\n301 54 10 16 29 133 137 0 30 17 156 155 159 22 277 171 278 19 162 160 161 33 202 201 200 199 286 299 105 284 196 195 70 285 0\n301 d 162 160 161 33 202 201 200 199 286 299 105 284 196 195 70 285 0\n302 23 -25 -54 99 100 111 0 113 282 14 180 276 281 168 32 275 117 167 149 17 154 112 127 126 289 146 9 266 111 109 110 22 277 171 278 19 153 148 151 147 152 150 23 13 280 268 271 270 177 120 133 122 121 134 279 26 119 132 116 118 272 166 164 165 35 273 274 130 131 129 0\n302 d 127 126 289 146 9 266 0\n303 -40 -34 0 293 280 136 191 177 279 26 158 119 132 163 292 141 241 5 137 142 135 139 138 140 3 187 14 183 184 276 283 300 168 128 114 115 275 149 17 301 154 302 282 235 180 19 175 153 281 148 172 151 32 147 173 152 117 167 150 13 268 271 270 120 133 122 121 134 116 118 272 166 164 165 35 273 274 130 131 129 0\n303 d 292 241 0\n304 -4 -23 129 0 235 153 151 154 237 0\n304 d 237 0\n305 -9 -34 0 303 258 298 253 0\n305 d 258 253 0\n306 -17 -34 0 293 257 298 252 0\n306 d 257 252 0\n307 30 -13 -34 0 297 303 306 191 298 213 207 194 188 189 256 0\n307 d 298 213 207 256 0\n308 -13 -34 0 297 303 307 306 191 254 251 189 214 188 194 208 0\n308 d 307 306 254 251 214 208 0\n309 -34 0 303 23 152 305 5 137 142 308 141 10 139 136 140 135 14 138 276 3 168 187 304 275 183 184 113 17 283 300 154 112 128 114 115 151 302 153 30 278 156 171 277 22 159 110 155 109 157 111 264 0\n309 d 303 305 308 0\n310 90 -30 40 83 117 121 0 297 309 23 152 223 142 139 140 14 276 168 275 17 154 112 151 153 278 171 277 22 159 110 227 194 231 188 189 259 137 135 138 3 187 304 183 184 113 283 300 128 114 115 302 109 30 111 156 264 155 157 0\n310 d 223 227 231 259 0\n311 9 117 121 129 0 5 137 142 135 139 138 140 3 14 187 276 183 184 168 283 300 275 128 114 115 304 302 17 113 30 154 112 156 151 153 278 171 277 22 159 110 155 109 157 111 264 0\n311 d 304 17 113 30 154 112 156 151 153 278 171 277 22 159 110 155 109 157 111 264 0\n312 -30 40 83 117 121 0 23 152 311 262 310 0\n312 d 262 310 0\n313 13 40 0 297 309 141 10 136 191 23 152 311 312 234 226 194 230 188 189 263 0\n313 d 10 23 312 234 226 230 263 0\n314 40 0 297 309 313 212 219 218 206 260 189 261 191 194 188 0\n314 d 313 212 219 218 206 260 261 194 188 0\n315 9 0 309 314 293 280 136 191 177 291 279 141 26 158 119 132 163 5 137 311 142 135 152 139 138 140 3 14 187 276 183 184 168 283 300 275 128 114 301 115 149 302 282 235 180 19 175 281 148 172 32 147 173 117 167 150 13 268 271 270 120 133 122 121 134 116 118 272 166 164 165 35 273 274 130 131 129 0\n315 d 280 136 177 291 279 141 26 158 119 132 163 5 137 311 142 135 152 139 138 140 3 14 187 276 183 184 168 283 300 275 128 114 301 115 149 302 282 235 180 19 175 281 148 172 32 147 173 117 167 150 13 268 271 270 120 133 122 121 134 116 118 272 166 164 165 35 273 274 130 131 129 0\n317 0 297 309 314 293 191 315 250 245 247 294 189 0\n"

theorem rt1_clause895_0 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-4 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-4 : ℤ)
  have hp := hpar (-4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_1 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-3 : ℤ)
  have hp := hpar (-3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_2 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-3 : ℤ) 6 = true) ∧ (y (-3 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-3 : ℤ)
  have hp := hpar (-3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_3 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_4 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 6 = true) ∧ (y (-2 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_5 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-2 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-2 : ℤ)
  have hp := hpar (-2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_6 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-1 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_7 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (-1 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_8 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 2 = true) ∧ ¬ (y (-1 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_9 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ ¬ (y (-1 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (-1 : ℤ)
  have hp := hpar (-1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_10 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_11 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_12 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 6 = true) ∧ (y (0 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_13 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 1 = true) ∧ (y (0 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (0 : ℤ)
  have hp := hpar (0 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_14 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_15 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_16 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (1 : ℤ)
  have hp := hpar (1 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_17 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_18 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 5 = true) ∧ ¬ (y (2 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (2 : ℤ)
  have hp := hpar (2 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_19 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_20 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_21 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 2 = true) ∧ ¬ (y (3 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_22 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 5 = true) ∧ ¬ (y (3 : ℤ) 1 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (3 : ℤ)
  have hp := hpar (3 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_23 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_24 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_25 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (4 : ℤ) 2 = true) ∧ ¬ (y (4 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (4 : ℤ)
  have hp := hpar (4 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_26 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_27 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 7 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_28 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 6 = true) ∧ (y (5 : ℤ) 2 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_29 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 1 = true) ∧ (y (5 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (5 : ℤ)
  have hp := hpar (5 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_30 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (6 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (6 : ℤ)
  have hp := hpar (6 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_31 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (6 : ℤ) 2 = true) ∧ ¬ (y (6 : ℤ) 6 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (6 : ℤ)
  have hp := hpar (6 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_32 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (6 : ℤ) 1 = true) ∧ (y (6 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (6 : ℤ)
  have hp := hpar (6 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_33 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (8 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (8 : ℤ)
  have hp := hpar (8 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_34 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (8 : ℤ) 1 = true) ∧ (y (8 : ℤ) 5 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (8 : ℤ)
  have hp := hpar (8 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_35 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (9 : ℤ) 0 = true)) := by
  classical
  obtain ⟨hend, hpar⟩ := rt1_bridge_base895 y e h
  have hh := hend (9 : ℤ)
  have hp := hpar (9 : ℤ)
  clear * - hh hp
  tauto

theorem rt1_clause895_36 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_37 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 3 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_38 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_39 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_40 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_41 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_42 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_43 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_44 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_45 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (e (0 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_46 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ (e (0 : ℤ) = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_47 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 1 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (e (0 : ℤ) = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_48 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_49 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_50 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_51 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_52 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (-1 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_53 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_54 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_55 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_56 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (-2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_57 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_58 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 1 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (-3 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_59 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ ¬ (e (4 : ℤ) = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_60 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_61 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_62 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_63 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_64 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (0 : ℤ) = true) ∧ ¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_65 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (e (4 : ℤ) = true) ∧ ¬ (y (2 : ℤ) 2 = true) ∧ ¬ (y (1 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 1 = true) ∧ (y (0 : ℤ) 0 = true)) := by
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

theorem rt1_clause895_66 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (2 : ℤ) 1 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_67 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 5 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (2 : ℤ) 1 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_68 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 2 = true) ∧ (y (0 : ℤ) 3 = true) ∧ (y (-3 : ℤ) 6 = true) ∧ (y (3 : ℤ) 0 = true) ∧ (y (-4 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_69 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 3 = true) ∧ ¬ (y (2 : ℤ) 1 = true) ∧ ¬ (y (-1 : ℤ) 4 = true) ∧ ¬ (y (-2 : ℤ) 5 = true) ∧ ¬ (e (3 : ℤ) = true) ∧ ¬ (y (1 : ℤ) 2 = true)) := by
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
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_70 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_71 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_72 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_73 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 6 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_74 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_75 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (0 : ℤ) 4 = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_76 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_77 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_78 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_79 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_80 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_81 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ (e (4 : ℤ) = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_82 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_83 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_84 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 5 = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_85 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_86 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 2 = true) ∧ (e (4 : ℤ) = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_87 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-2 : ℤ) 6 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_88 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_89 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (-1 : ℤ) 5 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_90 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (2 : ℤ) 2 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_91 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 3 = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_92 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_93 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (-1 : ℤ) 5 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_94 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (1 : ℤ) 3 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_95 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (4 : ℤ) = true) ∧ (y (-2 : ℤ) 6 = true) ∧ (y (0 : ℤ) 4 = true) ∧ (y (4 : ℤ) 0 = true) ∧ (y (-3 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_96 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 3 = true) ∧ (y (4 : ℤ) 1 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_97 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 2 = true) ∧ (y (-1 : ℤ) 6 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_98 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 6 = true) ∧ (y (2 : ℤ) 3 = true) ∧ (y (0 : ℤ) 5 = true) ∧ (y (5 : ℤ) 0 = true) ∧ (y (-2 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_99 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 3 = true) ∧ (y (1 : ℤ) 5 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_100 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 3 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (0 : ℤ) 6 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_101 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 4 = true) ∧ (y (1 : ℤ) 5 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_102 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (2 : ℤ) 4 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (0 : ℤ) 6 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_103 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 5 = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (0 : ℤ) 6 = true) ∧ (y (6 : ℤ) 0 = true) ∧ (y (-1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_104 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (4 : ℤ) 3 = true) ∧ ¬ (y (3 : ℤ) 4 = true) ∧ ¬ (y (1 : ℤ) 6 = true) ∧ ¬ (y (2 : ℤ) 5 = true) ∧ ¬ (y (5 : ℤ) 2 = true) ∧ ¬ (e (7 : ℤ) = true)) := by
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
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_105 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (5 : ℤ) 3 = true) ∧ (y (7 : ℤ) 1 = true) ∧ (y (3 : ℤ) 5 = true) ∧ (y (8 : ℤ) 0 = true) ∧ (y (1 : ℤ) 7 = true)) := by
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

theorem rt1_clause895_106 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (8 : ℤ) 1 = true) ∧ (y (6 : ℤ) 3 = true) ∧ (y (3 : ℤ) 6 = true) ∧ (y (9 : ℤ) 0 = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_9 := h.2.2.2.2 (9 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_9
  have hh := g_cnt_0_9
  have hb0 : (y (9 : ℤ) 0).toNat ≤ 1 := by cases y (9 : ℤ) 0 <;> decide
  have hb1 : (y (8 : ℤ) 1).toNat ≤ 1 := by cases y (8 : ℤ) 1 <;> decide
  have hb2 : (y (7 : ℤ) 2).toNat ≤ 1 := by cases y (7 : ℤ) 2 <;> decide
  have hb3 : (y (6 : ℤ) 3).toNat ≤ 1 := by cases y (6 : ℤ) 3 <;> decide
  have hb4 : (y (5 : ℤ) 4).toNat ≤ 1 := by cases y (5 : ℤ) 4 <;> decide
  have hb5 : (y (4 : ℤ) 5).toNat ≤ 1 := by cases y (4 : ℤ) 5 <;> decide
  have hb6 : (y (3 : ℤ) 6).toNat ≤ 1 := by cases y (3 : ℤ) 6 <;> decide
  have hb7 : (y (2 : ℤ) 7).toNat ≤ 1 := by cases y (2 : ℤ) 7 <;> decide
  have hb8 : (e (9 : ℤ)).toNat ≤ 1 := by cases e (9 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_107 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (5 : ℤ) 4 = true) ∧ (y (8 : ℤ) 1 = true) ∧ (y (3 : ℤ) 6 = true) ∧ (y (9 : ℤ) 0 = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  have g_cnt_0_9 := h.2.2.2.2 (9 : ℤ)
  norm_num [Finset.sum_range_succ] at g_cnt_0_9
  have hh := g_cnt_0_9
  have hb0 : (y (9 : ℤ) 0).toNat ≤ 1 := by cases y (9 : ℤ) 0 <;> decide
  have hb1 : (y (8 : ℤ) 1).toNat ≤ 1 := by cases y (8 : ℤ) 1 <;> decide
  have hb2 : (y (7 : ℤ) 2).toNat ≤ 1 := by cases y (7 : ℤ) 2 <;> decide
  have hb3 : (y (6 : ℤ) 3).toNat ≤ 1 := by cases y (6 : ℤ) 3 <;> decide
  have hb4 : (y (5 : ℤ) 4).toNat ≤ 1 := by cases y (5 : ℤ) 4 <;> decide
  have hb5 : (y (4 : ℤ) 5).toNat ≤ 1 := by cases y (4 : ℤ) 5 <;> decide
  have hb6 : (y (3 : ℤ) 6).toNat ≤ 1 := by cases y (3 : ℤ) 6 <;> decide
  have hb7 : (y (2 : ℤ) 7).toNat ≤ 1 := by cases y (2 : ℤ) 7 <;> decide
  have hb8 : (e (9 : ℤ)).toNat ≤ 1 := by cases e (9 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_108 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ∧ ¬ ((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ∧ ¬ ((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true) ∧ ¬ ((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ∧ ¬ ((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true)) := by
  classical
  have g_cov_2_3 := h.2.2.2.1 2 (by omega) (by omega) (by omega) (3 : ℤ)
  norm_num at g_cov_2_3
  have hh := g_cov_2_3
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_109 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ∧ ¬ (y (3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_110 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ∧ ¬ (y (2 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_111 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ∧ ¬ (y (1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_112 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ∧ ¬ (y (0 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_113 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_114 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_115 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 3) = true) ∧ ¬ ((y (3 : ℤ) 3 && y (3 : ℤ) 5) = true) ∧ ¬ ((y (2 : ℤ) 4 && y (2 : ℤ) 6) = true) ∧ ¬ ((y (1 : ℤ) 5 && y (1 : ℤ) 7) = true) ∧ ¬ ((y (6 : ℤ) 0 && y (6 : ℤ) 2) = true) ∧ ¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 4) = true)) := by
  classical
  have g_cov_2_6 := h.2.2.2.1 2 (by omega) (by omega) (by omega) (6 : ℤ)
  norm_num at g_cov_2_6
  have hh := g_cov_2_6
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4, hz5⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_116 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 0 && y (6 : ℤ) 2) = true) ∧ ¬ (y (6 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_117 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 3 = true) ∧ ((y (5 : ℤ) 1 && y (5 : ℤ) 3) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_118 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 2 && y (4 : ℤ) 4) = true) ∧ ¬ (y (4 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_119 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 3 && y (3 : ℤ) 5) = true) ∧ ¬ (y (3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_120 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 4 && y (2 : ℤ) 6) = true) ∧ ¬ (y (2 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_121 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 5 && y (1 : ℤ) 7) = true) ∧ ¬ (y (1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_122 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 4) = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 3) = true) ∧ ¬ ((y (0 : ℤ) 3 && y (0 : ℤ) 6) = true) ∧ ¬ ((y (1 : ℤ) 2 && y (1 : ℤ) 5) = true) ∧ ¬ ((y (-1 : ℤ) 4 && y (-1 : ℤ) 7) = true)) := by
  classical
  have g_cov_3_3 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (3 : ℤ)
  norm_num at g_cov_3_3
  have hh := g_cov_3_3
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_123 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 3) = true) ∧ ¬ (y (3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_124 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 4) = true) ∧ ¬ (y (2 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_125 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 2 && y (1 : ℤ) 5) = true) ∧ ¬ (y (1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_126 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 3 && y (0 : ℤ) 6) = true) ∧ ¬ (y (0 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_127 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 4 && y (-1 : ℤ) 7) = true) ∧ ¬ (y (-1 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_128 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (6 : ℤ) 0 && y (6 : ℤ) 3) = true) ∧ ¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 4) = true) ∧ ¬ ((y (3 : ℤ) 3 && y (3 : ℤ) 6) = true) ∧ ¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 5) = true) ∧ ¬ ((y (2 : ℤ) 4 && y (2 : ℤ) 7) = true)) := by
  classical
  have g_cov_3_6 := h.2.2.2.1 3 (by omega) (by omega) (by omega) (6 : ℤ)
  norm_num at g_cov_3_6
  have hh := g_cov_3_6
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_129 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 0 && y (6 : ℤ) 3) = true) ∧ ¬ (y (6 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_130 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 1 && y (5 : ℤ) 4) = true) ∧ ¬ (y (5 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_131 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 2 && y (4 : ℤ) 5) = true) ∧ ¬ (y (4 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_132 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 3 && y (3 : ℤ) 6) = true) ∧ ¬ (y (3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_133 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 4 && y (2 : ℤ) 7) = true) ∧ ¬ (y (2 : ℤ) 4 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_134 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
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

theorem rt1_clause895_135 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 5) = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_136 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 1 && y (-2 : ℤ) 6) = true) ∧ ¬ (y (-2 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_137 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 2 && y (-3 : ℤ) 7) = true) ∧ ¬ (y (-3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_138 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
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

theorem rt1_clause895_139 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 5 = true) ∧ ((y (0 : ℤ) 0 && y (0 : ℤ) 5) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_140 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ∧ ¬ (y (-1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_141 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true) ∧ ¬ (y (-2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_142 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ∧ ¬ ((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true) ∧ ¬ ((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_1 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (1 : ℤ)
  norm_num at g_cov_5_1
  have hh := g_cov_5_1
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_143 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ∧ ¬ (y (1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_144 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true) ∧ ¬ (y (0 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_145 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true) ∧ ¬ (y (-1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_146 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true) ∧ ¬ ((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ∧ ¬ ((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true)) := by
  classical
  have g_cov_5_2 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (2 : ℤ)
  norm_num at g_cov_5_2
  have hh := g_cov_5_2
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_147 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ∧ ¬ (y (2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_148 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ∧ ¬ (y (1 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_149 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 2 = true) ∧ ((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_150 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true) ∧ ¬ ((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true)) := by
  classical
  have g_cov_5_3 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (3 : ℤ)
  norm_num at g_cov_5_3
  have hh := g_cov_5_3
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_151 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true) ∧ ¬ (y (3 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_152 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (2 : ℤ) 1 = true) ∧ ((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_153 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ∧ ¬ (y (1 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_154 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
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

theorem rt1_clause895_155 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (5 : ℤ) 5 = true) ∧ ((y (5 : ℤ) 0 && y (5 : ℤ) 5) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_156 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ ¬ (y (4 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_157 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ∧ ¬ (y (4 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_158 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true) ∧ ¬ (y (3 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_159 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true) ∧ ¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ∧ ¬ ((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_6 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (6 : ℤ)
  norm_num at g_cov_5_6
  have hh := g_cov_5_6
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_160 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (6 : ℤ) 5 = true) ∧ ((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_161 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ∧ ¬ (y (5 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_162 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true) ∧ ¬ (y (4 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_163 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (8 : ℤ) 0 && y (8 : ℤ) 5) = true) ∧ ¬ ((y (7 : ℤ) 1 && y (7 : ℤ) 6) = true) ∧ ¬ ((y (6 : ℤ) 2 && y (6 : ℤ) 7) = true)) := by
  classical
  have g_cov_5_8 := h.2.2.2.1 5 (by omega) (by omega) (by omega) (8 : ℤ)
  norm_num at g_cov_5_8
  have hh := g_cov_5_8
  clear * - hh
  intro hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  rcases hh with ⟨a, ha, ha1, ha2⟩
  interval_cases a <;> norm_num at * <;> simp_all [Bool.and_eq_true]

theorem rt1_clause895_164 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (8 : ℤ) 5 = true) ∧ ((y (8 : ℤ) 0 && y (8 : ℤ) 5) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_165 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (7 : ℤ) 1 && y (7 : ℤ) 6) = true) ∧ ¬ (y (7 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_166 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 2 && y (6 : ℤ) 7) = true) ∧ ¬ (y (6 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_167 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (1 : ℤ) 0 && y (1 : ℤ) 6) = true) ∧ ((y (0 : ℤ) 1 && y (0 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_1 := h.2.1 1 (by omega) (1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_1
  have hh := g_ex_1_1
  have hb0 : ((y (1 : ℤ) 0 && y (1 : ℤ) 6)).toNat ≤ 1 := by cases (y (1 : ℤ) 0 && y (1 : ℤ) 6) <;> decide
  have hb1 : ((y (0 : ℤ) 1 && y (0 : ℤ) 7)).toNat ≤ 1 := by cases (y (0 : ℤ) 1 && y (0 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_168 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (1 : ℤ) 6 = true) ∧ ¬ ((y (1 : ℤ) 0 && y (1 : ℤ) 6) = true) ∧ (y (1 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_169 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 1 && y (0 : ℤ) 7) = true) ∧ (y (0 : ℤ) 1 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_170 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
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

theorem rt1_clause895_171 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ∧ ¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true)) := by
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

theorem rt1_clause895_172 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (3 : ℤ) 6 = true) ∧ ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_173 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 6 = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ∧ (y (3 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_174 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true) ∧ ¬ (y (2 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_175 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true) ∧ (y (2 : ℤ) 1 = true) ∧ (y (2 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_176 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
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

theorem rt1_clause895_177 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (4 : ℤ) 6 = true) ∧ ¬ ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ∧ (y (4 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_178 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true) ∧ (y (3 : ℤ) 1 = true) ∧ (y (3 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_179 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (6 : ℤ) 0 && y (6 : ℤ) 6) = true) ∧ ((y (5 : ℤ) 1 && y (5 : ℤ) 7) = true)) := by
  classical
  have g_ex_1_6 := h.2.1 1 (by omega) (6 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_1_6
  have hh := g_ex_1_6
  have hb0 : ((y (6 : ℤ) 0 && y (6 : ℤ) 6)).toNat ≤ 1 := by cases (y (6 : ℤ) 0 && y (6 : ℤ) 6) <;> decide
  have hb1 : ((y (5 : ℤ) 1 && y (5 : ℤ) 7)).toNat ≤ 1 := by cases (y (5 : ℤ) 1 && y (5 : ℤ) 7) <;> decide
  clear * - hh hb0 hb1
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_180 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (6 : ℤ) 6 = true) ∧ ¬ ((y (6 : ℤ) 0 && y (6 : ℤ) 6) = true) ∧ (y (6 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_181 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (5 : ℤ) 1 && y (5 : ℤ) 7) = true) ∧ (y (5 : ℤ) 1 = true) ∧ (y (5 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_182 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 0 && y (-1 : ℤ) 4) = true) ∧ ((y (-3 : ℤ) 2 && y (-3 : ℤ) 6) = true)) := by
  classical
  have g_ex_2_m1 := h.2.2.1 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_m1
  have hh := g_ex_2_m1
  have hb0 : ((y (-1 : ℤ) 0 && y (-1 : ℤ) 4)).toNat ≤ 1 := by cases (y (-1 : ℤ) 0 && y (-1 : ℤ) 4) <;> decide
  have hb1 : ((y (-2 : ℤ) 1 && y (-2 : ℤ) 5)).toNat ≤ 1 := by cases (y (-2 : ℤ) 1 && y (-2 : ℤ) 5) <;> decide
  have hb2 : ((y (-3 : ℤ) 2 && y (-3 : ℤ) 6)).toNat ≤ 1 := by cases (y (-3 : ℤ) 2 && y (-3 : ℤ) 6) <;> decide
  have hb3 : ((y (-4 : ℤ) 3 && y (-4 : ℤ) 7)).toNat ≤ 1 := by cases (y (-4 : ℤ) 3 && y (-4 : ℤ) 7) <;> decide
  have hb4 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_183 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 2 && y (-3 : ℤ) 6) = true) ∧ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_m1 := h.2.2.1 (-1 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_m1
  have hh := g_ex_2_m1
  have hb0 : ((y (-1 : ℤ) 0 && y (-1 : ℤ) 4)).toNat ≤ 1 := by cases (y (-1 : ℤ) 0 && y (-1 : ℤ) 4) <;> decide
  have hb1 : ((y (-2 : ℤ) 1 && y (-2 : ℤ) 5)).toNat ≤ 1 := by cases (y (-2 : ℤ) 1 && y (-2 : ℤ) 5) <;> decide
  have hb2 : ((y (-3 : ℤ) 2 && y (-3 : ℤ) 6)).toNat ≤ 1 := by cases (y (-3 : ℤ) 2 && y (-3 : ℤ) 6) <;> decide
  have hb3 : ((y (-4 : ℤ) 3 && y (-4 : ℤ) 7)).toNat ≤ 1 := by cases (y (-4 : ℤ) 3 && y (-4 : ℤ) 7) <;> decide
  have hb4 : (e (-1 : ℤ)).toNat ≤ 1 := by cases e (-1 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_184 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-1 : ℤ) 4 = true) ∧ ¬ ((y (-1 : ℤ) 0 && y (-1 : ℤ) 4) = true) ∧ (y (-1 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_185 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (-2 : ℤ) 1 && y (-2 : ℤ) 5) = true) ∧ (y (-2 : ℤ) 1 = true) ∧ (y (-2 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_186 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (-3 : ℤ) 2 = true) ∧ ¬ ((y (-3 : ℤ) 2 && y (-3 : ℤ) 6) = true) ∧ (y (-3 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_187 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ∧ ¬ ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) ∧ ¬ (e (0 : ℤ) = true) ∧ ¬ ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ¬ ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true)) := by
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
  rcases hz with ⟨hz0, hz1, hz2, hz3, hz4⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_188 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ (y (0 : ℤ) 4 = true) ∧ ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_189 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ¬ (y (-1 : ℤ) 1 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_190 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ∧ ¬ (y (-1 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_191 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ∧ ¬ (y (-2 : ℤ) 2 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_192 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ∧ ¬ (y (-2 : ℤ) 6 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_193 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) ∧ ¬ (y (-3 : ℤ) 3 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_194 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (3 : ℤ) 0 && y (3 : ℤ) 4) = true) ∧ ((y (0 : ℤ) 3 && y (0 : ℤ) 7) = true)) := by
  classical
  have g_ex_2_3 := h.2.2.1 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_3
  have hh := g_ex_2_3
  have hb0 : ((y (3 : ℤ) 0 && y (3 : ℤ) 4)).toNat ≤ 1 := by cases (y (3 : ℤ) 0 && y (3 : ℤ) 4) <;> decide
  have hb1 : ((y (2 : ℤ) 1 && y (2 : ℤ) 5)).toNat ≤ 1 := by cases (y (2 : ℤ) 1 && y (2 : ℤ) 5) <;> decide
  have hb2 : ((y (1 : ℤ) 2 && y (1 : ℤ) 6)).toNat ≤ 1 := by cases (y (1 : ℤ) 2 && y (1 : ℤ) 6) <;> decide
  have hb3 : ((y (0 : ℤ) 3 && y (0 : ℤ) 7)).toNat ≤ 1 := by cases (y (0 : ℤ) 3 && y (0 : ℤ) 7) <;> decide
  have hb4 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_195 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (3 : ℤ) = true) ∧ ((y (3 : ℤ) 0 && y (3 : ℤ) 4) = true)) := by
  classical
  have g_ex_2_3 := h.2.2.1 (3 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_3
  have hh := g_ex_2_3
  have hb0 : ((y (3 : ℤ) 0 && y (3 : ℤ) 4)).toNat ≤ 1 := by cases (y (3 : ℤ) 0 && y (3 : ℤ) 4) <;> decide
  have hb1 : ((y (2 : ℤ) 1 && y (2 : ℤ) 5)).toNat ≤ 1 := by cases (y (2 : ℤ) 1 && y (2 : ℤ) 5) <;> decide
  have hb2 : ((y (1 : ℤ) 2 && y (1 : ℤ) 6)).toNat ≤ 1 := by cases (y (1 : ℤ) 2 && y (1 : ℤ) 6) <;> decide
  have hb3 : ((y (0 : ℤ) 3 && y (0 : ℤ) 7)).toNat ≤ 1 := by cases (y (0 : ℤ) 3 && y (0 : ℤ) 7) <;> decide
  have hb4 : (e (3 : ℤ)).toNat ≤ 1 := by cases e (3 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_196 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (3 : ℤ) 4 = true) ∧ ¬ ((y (3 : ℤ) 0 && y (3 : ℤ) 4) = true) ∧ (y (3 : ℤ) 0 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_197 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (0 : ℤ) 3 && y (0 : ℤ) 7) = true) ∧ (y (0 : ℤ) 3 = true) ∧ (y (0 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_198 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (5 : ℤ) 2 && y (5 : ℤ) 6) = true) ∧ ((y (6 : ℤ) 1 && y (6 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_7 := h.2.2.1 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_7
  have hh := g_ex_2_7
  have hb0 : ((y (7 : ℤ) 0 && y (7 : ℤ) 4)).toNat ≤ 1 := by cases (y (7 : ℤ) 0 && y (7 : ℤ) 4) <;> decide
  have hb1 : ((y (6 : ℤ) 1 && y (6 : ℤ) 5)).toNat ≤ 1 := by cases (y (6 : ℤ) 1 && y (6 : ℤ) 5) <;> decide
  have hb2 : ((y (5 : ℤ) 2 && y (5 : ℤ) 6)).toNat ≤ 1 := by cases (y (5 : ℤ) 2 && y (5 : ℤ) 6) <;> decide
  have hb3 : ((y (4 : ℤ) 3 && y (4 : ℤ) 7)).toNat ≤ 1 := by cases (y (4 : ℤ) 3 && y (4 : ℤ) 7) <;> decide
  have hb4 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_199 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (((y (4 : ℤ) 3 && y (4 : ℤ) 7) = true) ∧ ((y (6 : ℤ) 1 && y (6 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_7 := h.2.2.1 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_7
  have hh := g_ex_2_7
  have hb0 : ((y (7 : ℤ) 0 && y (7 : ℤ) 4)).toNat ≤ 1 := by cases (y (7 : ℤ) 0 && y (7 : ℤ) 4) <;> decide
  have hb1 : ((y (6 : ℤ) 1 && y (6 : ℤ) 5)).toNat ≤ 1 := by cases (y (6 : ℤ) 1 && y (6 : ℤ) 5) <;> decide
  have hb2 : ((y (5 : ℤ) 2 && y (5 : ℤ) 6)).toNat ≤ 1 := by cases (y (5 : ℤ) 2 && y (5 : ℤ) 6) <;> decide
  have hb3 : ((y (4 : ℤ) 3 && y (4 : ℤ) 7)).toNat ≤ 1 := by cases (y (4 : ℤ) 3 && y (4 : ℤ) 7) <;> decide
  have hb4 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_200 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((e (7 : ℤ) = true) ∧ ((y (6 : ℤ) 1 && y (6 : ℤ) 5) = true)) := by
  classical
  have g_ex_2_7 := h.2.2.1 (7 : ℤ)
  norm_num [Finset.sum_range_succ] at g_ex_2_7
  have hh := g_ex_2_7
  have hb0 : ((y (7 : ℤ) 0 && y (7 : ℤ) 4)).toNat ≤ 1 := by cases (y (7 : ℤ) 0 && y (7 : ℤ) 4) <;> decide
  have hb1 : ((y (6 : ℤ) 1 && y (6 : ℤ) 5)).toNat ≤ 1 := by cases (y (6 : ℤ) 1 && y (6 : ℤ) 5) <;> decide
  have hb2 : ((y (5 : ℤ) 2 && y (5 : ℤ) 6)).toNat ≤ 1 := by cases (y (5 : ℤ) 2 && y (5 : ℤ) 6) <;> decide
  have hb3 : ((y (4 : ℤ) 3 && y (4 : ℤ) 7)).toNat ≤ 1 := by cases (y (4 : ℤ) 3 && y (4 : ℤ) 7) <;> decide
  have hb4 : (e (7 : ℤ)).toNat ≤ 1 := by cases e (7 : ℤ) <;> decide
  clear * - hh hb0 hb1 hb2 hb3 hb4
  intro hz
  rcases hz with ⟨hz0, hz1⟩
  simp_all only [Bool.not_eq_true, Bool.toNat_true, Bool.toNat_false]
  omega

theorem rt1_clause895_201 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (6 : ℤ) 1 && y (6 : ℤ) 5) = true) ∧ (y (6 : ℤ) 1 = true) ∧ (y (6 : ℤ) 5 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_202 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ ((y (5 : ℤ) 6 = true) ∧ (y (5 : ℤ) 2 = true) ∧ ¬ ((y (5 : ℤ) 2 && y (5 : ℤ) 6) = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_clause895_203 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0)
    (hn : ¬ ((Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
       (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat)) : ¬ (¬ ((y (4 : ℤ) 3 && y (4 : ℤ) 7) = true) ∧ (y (4 : ℤ) 3 = true) ∧ (y (4 : ℤ) 7 = true)) := by
  classical
  simp only [Bool.and_eq_true] <;> tauto

theorem rt1_upper_zero_split895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) :
    (Finset.range 4).sum (fun a => (y (0-(a:ℤ)) a).toNat) + (e 0).toNat ≥
      (Finset.range 4).sum (fun a => (y (4-(a:ℤ)) a).toNat) + (e 4).toNat := by
  classical
  by_contra hn
  have bad := rt1_lower_cert895 (y (-4 : ℤ) 7 = true) (y (-3 : ℤ) 7 = true) (y (-3 : ℤ) 2 = true) (y (-3 : ℤ) 6 = true) (y (-3 : ℤ) 3 = true) (y (-2 : ℤ) 7 = true) (y (-2 : ℤ) 1 = true) (y (-2 : ℤ) 2 = true) (y (-2 : ℤ) 6 = true) (y (-2 : ℤ) 5 = true) (y (-1 : ℤ) 0 = true) (y (-1 : ℤ) 7 = true) (y (-1 : ℤ) 1 = true) (y (-1 : ℤ) 2 = true) (y (-1 : ℤ) 6 = true) (y (-1 : ℤ) 4 = true) (y (-1 : ℤ) 5 = true) (y (0 : ℤ) 0 = true) (y (0 : ℤ) 7 = true) (y (0 : ℤ) 1 = true) (y (0 : ℤ) 2 = true) (y (0 : ℤ) 6 = true) (y (0 : ℤ) 3 = true) (y (0 : ℤ) 4 = true) (y (0 : ℤ) 5 = true) (y (1 : ℤ) 0 = true) (y (1 : ℤ) 7 = true) (y (1 : ℤ) 2 = true) (y (1 : ℤ) 6 = true) (y (1 : ℤ) 3 = true) (y (1 : ℤ) 5 = true) (y (2 : ℤ) 7 = true) (y (2 : ℤ) 1 = true) (y (2 : ℤ) 2 = true) (y (2 : ℤ) 3 = true) (y (2 : ℤ) 4 = true) (y (2 : ℤ) 5 = true) (y (3 : ℤ) 0 = true) (y (3 : ℤ) 7 = true) (y (3 : ℤ) 1 = true) (y (3 : ℤ) 2 = true) (y (3 : ℤ) 6 = true) (y (3 : ℤ) 3 = true) (y (3 : ℤ) 4 = true) (y (3 : ℤ) 5 = true) (y (4 : ℤ) 0 = true) (y (4 : ℤ) 7 = true) (y (4 : ℤ) 1 = true) (y (4 : ℤ) 2 = true) (y (4 : ℤ) 6 = true) (y (4 : ℤ) 3 = true) (y (5 : ℤ) 0 = true) (y (5 : ℤ) 7 = true) (y (5 : ℤ) 1 = true) (y (5 : ℤ) 2 = true) (y (5 : ℤ) 6 = true) (y (5 : ℤ) 3 = true) (y (5 : ℤ) 4 = true) (y (5 : ℤ) 5 = true) (y (6 : ℤ) 0 = true) (y (6 : ℤ) 1 = true) (y (6 : ℤ) 2 = true) (y (6 : ℤ) 6 = true) (y (6 : ℤ) 3 = true) (y (6 : ℤ) 5 = true) (y (7 : ℤ) 1 = true) (y (8 : ℤ) 0 = true) (y (8 : ℤ) 1 = true) (y (8 : ℤ) 5 = true) (y (9 : ℤ) 0 = true) ((y (1 : ℤ) 0 && y (1 : ℤ) 6) = true) ((y (0 : ℤ) 1 && y (0 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 6) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 7) = true) ((y (4 : ℤ) 0 && y (4 : ℤ) 6) = true) ((y (3 : ℤ) 1 && y (3 : ℤ) 7) = true) ((y (6 : ℤ) 0 && y (6 : ℤ) 6) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 7) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 4) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 5) = true) ((y (-3 : ℤ) 2 && y (-3 : ℤ) 6) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 4) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 5) = true) ((y (-2 : ℤ) 2 && y (-2 : ℤ) 6) = true) ((y (-3 : ℤ) 3 && y (-3 : ℤ) 7) = true) (e (0 : ℤ) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 4) = true) ((y (0 : ℤ) 3 && y (0 : ℤ) 7) = true) (e (3 : ℤ) = true) (e (4 : ℤ) = true) ((y (6 : ℤ) 1 && y (6 : ℤ) 5) = true) ((y (5 : ℤ) 2 && y (5 : ℤ) 6) = true) ((y (4 : ℤ) 3 && y (4 : ℤ) 7) = true) (e (7 : ℤ) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 2) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 3) = true) ((y (1 : ℤ) 2 && y (1 : ℤ) 4) = true) ((y (0 : ℤ) 3 && y (0 : ℤ) 5) = true) ((y (-1 : ℤ) 4 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 5 && y (-2 : ℤ) 7) = true) ((y (6 : ℤ) 0 && y (6 : ℤ) 2) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 3) = true) ((y (4 : ℤ) 2 && y (4 : ℤ) 4) = true) ((y (3 : ℤ) 3 && y (3 : ℤ) 5) = true) ((y (2 : ℤ) 4 && y (2 : ℤ) 6) = true) ((y (1 : ℤ) 5 && y (1 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 3) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 4) = true) ((y (1 : ℤ) 2 && y (1 : ℤ) 5) = true) ((y (0 : ℤ) 3 && y (0 : ℤ) 6) = true) ((y (-1 : ℤ) 4 && y (-1 : ℤ) 7) = true) ((y (6 : ℤ) 0 && y (6 : ℤ) 3) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 4) = true) ((y (4 : ℤ) 2 && y (4 : ℤ) 5) = true) ((y (3 : ℤ) 3 && y (3 : ℤ) 6) = true) ((y (2 : ℤ) 4 && y (2 : ℤ) 7) = true) ((y (-1 : ℤ) 0 && y (-1 : ℤ) 5) = true) ((y (-2 : ℤ) 1 && y (-2 : ℤ) 6) = true) ((y (-3 : ℤ) 2 && y (-3 : ℤ) 7) = true) ((y (0 : ℤ) 0 && y (0 : ℤ) 5) = true) ((y (-1 : ℤ) 1 && y (-1 : ℤ) 6) = true) ((y (-2 : ℤ) 2 && y (-2 : ℤ) 7) = true) ((y (1 : ℤ) 0 && y (1 : ℤ) 5) = true) ((y (0 : ℤ) 1 && y (0 : ℤ) 6) = true) ((y (-1 : ℤ) 2 && y (-1 : ℤ) 7) = true) ((y (2 : ℤ) 0 && y (2 : ℤ) 5) = true) ((y (1 : ℤ) 1 && y (1 : ℤ) 6) = true) ((y (0 : ℤ) 2 && y (0 : ℤ) 7) = true) ((y (3 : ℤ) 0 && y (3 : ℤ) 5) = true) ((y (2 : ℤ) 1 && y (2 : ℤ) 6) = true) ((y (1 : ℤ) 2 && y (1 : ℤ) 7) = true) ((y (5 : ℤ) 0 && y (5 : ℤ) 5) = true) ((y (4 : ℤ) 1 && y (4 : ℤ) 6) = true) ((y (3 : ℤ) 2 && y (3 : ℤ) 7) = true) ((y (6 : ℤ) 0 && y (6 : ℤ) 5) = true) ((y (5 : ℤ) 1 && y (5 : ℤ) 6) = true) ((y (4 : ℤ) 2 && y (4 : ℤ) 7) = true) ((y (8 : ℤ) 0 && y (8 : ℤ) 5) = true) ((y (7 : ℤ) 1 && y (7 : ℤ) 6) = true) ((y (6 : ℤ) 2 && y (6 : ℤ) 7) = true)
  simp only [rt1_clause895_0 y e h hn, rt1_clause895_1 y e h hn, rt1_clause895_2 y e h hn, rt1_clause895_3 y e h hn, rt1_clause895_4 y e h hn, rt1_clause895_5 y e h hn, rt1_clause895_6 y e h hn, rt1_clause895_7 y e h hn, rt1_clause895_8 y e h hn, rt1_clause895_9 y e h hn, rt1_clause895_10 y e h hn, rt1_clause895_11 y e h hn, rt1_clause895_12 y e h hn, rt1_clause895_13 y e h hn, rt1_clause895_14 y e h hn, rt1_clause895_15 y e h hn, rt1_clause895_16 y e h hn, rt1_clause895_17 y e h hn, rt1_clause895_18 y e h hn, rt1_clause895_19 y e h hn, rt1_clause895_20 y e h hn, rt1_clause895_21 y e h hn, rt1_clause895_22 y e h hn, rt1_clause895_23 y e h hn, rt1_clause895_24 y e h hn, rt1_clause895_25 y e h hn, rt1_clause895_26 y e h hn, rt1_clause895_27 y e h hn, rt1_clause895_28 y e h hn, rt1_clause895_29 y e h hn, rt1_clause895_30 y e h hn, rt1_clause895_31 y e h hn, rt1_clause895_32 y e h hn, rt1_clause895_33 y e h hn, rt1_clause895_34 y e h hn, rt1_clause895_35 y e h hn, rt1_clause895_36 y e h hn, rt1_clause895_37 y e h hn, rt1_clause895_38 y e h hn, rt1_clause895_39 y e h hn, rt1_clause895_40 y e h hn, rt1_clause895_41 y e h hn, rt1_clause895_42 y e h hn, rt1_clause895_43 y e h hn, rt1_clause895_44 y e h hn, rt1_clause895_45 y e h hn, rt1_clause895_46 y e h hn, rt1_clause895_47 y e h hn, rt1_clause895_48 y e h hn, rt1_clause895_49 y e h hn, rt1_clause895_50 y e h hn, rt1_clause895_51 y e h hn, rt1_clause895_52 y e h hn, rt1_clause895_53 y e h hn, rt1_clause895_54 y e h hn, rt1_clause895_55 y e h hn, rt1_clause895_56 y e h hn, rt1_clause895_57 y e h hn, rt1_clause895_58 y e h hn, rt1_clause895_59 y e h hn, rt1_clause895_60 y e h hn, rt1_clause895_61 y e h hn, rt1_clause895_62 y e h hn, rt1_clause895_63 y e h hn, rt1_clause895_64 y e h hn, rt1_clause895_65 y e h hn, rt1_clause895_66 y e h hn, rt1_clause895_67 y e h hn, rt1_clause895_68 y e h hn, rt1_clause895_69 y e h hn, rt1_clause895_70 y e h hn, rt1_clause895_71 y e h hn, rt1_clause895_72 y e h hn, rt1_clause895_73 y e h hn, rt1_clause895_74 y e h hn, rt1_clause895_75 y e h hn, rt1_clause895_76 y e h hn, rt1_clause895_77 y e h hn, rt1_clause895_78 y e h hn, rt1_clause895_79 y e h hn, rt1_clause895_80 y e h hn, rt1_clause895_81 y e h hn, rt1_clause895_82 y e h hn, rt1_clause895_83 y e h hn, rt1_clause895_84 y e h hn, rt1_clause895_85 y e h hn, rt1_clause895_86 y e h hn, rt1_clause895_87 y e h hn, rt1_clause895_88 y e h hn, rt1_clause895_89 y e h hn, rt1_clause895_90 y e h hn, rt1_clause895_91 y e h hn, rt1_clause895_92 y e h hn, rt1_clause895_93 y e h hn, rt1_clause895_94 y e h hn, rt1_clause895_95 y e h hn, rt1_clause895_96 y e h hn, rt1_clause895_97 y e h hn, rt1_clause895_98 y e h hn, rt1_clause895_99 y e h hn, rt1_clause895_100 y e h hn, rt1_clause895_101 y e h hn, rt1_clause895_102 y e h hn, rt1_clause895_103 y e h hn, rt1_clause895_104 y e h hn, rt1_clause895_105 y e h hn, rt1_clause895_106 y e h hn, rt1_clause895_107 y e h hn, rt1_clause895_108 y e h hn, rt1_clause895_109 y e h hn, rt1_clause895_110 y e h hn, rt1_clause895_111 y e h hn, rt1_clause895_112 y e h hn, rt1_clause895_113 y e h hn, rt1_clause895_114 y e h hn, rt1_clause895_115 y e h hn, rt1_clause895_116 y e h hn, rt1_clause895_117 y e h hn, rt1_clause895_118 y e h hn, rt1_clause895_119 y e h hn, rt1_clause895_120 y e h hn, rt1_clause895_121 y e h hn, rt1_clause895_122 y e h hn, rt1_clause895_123 y e h hn, rt1_clause895_124 y e h hn, rt1_clause895_125 y e h hn, rt1_clause895_126 y e h hn, rt1_clause895_127 y e h hn, rt1_clause895_128 y e h hn, rt1_clause895_129 y e h hn, rt1_clause895_130 y e h hn, rt1_clause895_131 y e h hn, rt1_clause895_132 y e h hn, rt1_clause895_133 y e h hn, rt1_clause895_134 y e h hn, rt1_clause895_135 y e h hn, rt1_clause895_136 y e h hn, rt1_clause895_137 y e h hn, rt1_clause895_138 y e h hn, rt1_clause895_139 y e h hn, rt1_clause895_140 y e h hn, rt1_clause895_141 y e h hn, rt1_clause895_142 y e h hn, rt1_clause895_143 y e h hn, rt1_clause895_144 y e h hn, rt1_clause895_145 y e h hn, rt1_clause895_146 y e h hn, rt1_clause895_147 y e h hn, rt1_clause895_148 y e h hn, rt1_clause895_149 y e h hn, rt1_clause895_150 y e h hn, rt1_clause895_151 y e h hn, rt1_clause895_152 y e h hn, rt1_clause895_153 y e h hn, rt1_clause895_154 y e h hn, rt1_clause895_155 y e h hn, rt1_clause895_156 y e h hn, rt1_clause895_157 y e h hn, rt1_clause895_158 y e h hn, rt1_clause895_159 y e h hn, rt1_clause895_160 y e h hn, rt1_clause895_161 y e h hn, rt1_clause895_162 y e h hn, rt1_clause895_163 y e h hn, rt1_clause895_164 y e h hn, rt1_clause895_165 y e h hn, rt1_clause895_166 y e h hn, rt1_clause895_167 y e h hn, rt1_clause895_168 y e h hn, rt1_clause895_169 y e h hn, rt1_clause895_170 y e h hn, rt1_clause895_171 y e h hn, rt1_clause895_172 y e h hn, rt1_clause895_173 y e h hn, rt1_clause895_174 y e h hn, rt1_clause895_175 y e h hn, rt1_clause895_176 y e h hn, rt1_clause895_177 y e h hn, rt1_clause895_178 y e h hn, rt1_clause895_179 y e h hn, rt1_clause895_180 y e h hn, rt1_clause895_181 y e h hn, rt1_clause895_182 y e h hn, rt1_clause895_183 y e h hn, rt1_clause895_184 y e h hn, rt1_clause895_185 y e h hn, rt1_clause895_186 y e h hn, rt1_clause895_187 y e h hn, rt1_clause895_188 y e h hn, rt1_clause895_189 y e h hn, rt1_clause895_190 y e h hn, rt1_clause895_191 y e h hn, rt1_clause895_192 y e h hn, rt1_clause895_193 y e h hn, rt1_clause895_194 y e h hn, rt1_clause895_195 y e h hn, rt1_clause895_196 y e h hn, rt1_clause895_197 y e h hn, rt1_clause895_198 y e h hn, rt1_clause895_199 y e h hn, rt1_clause895_200 y e h hn, rt1_clause895_201 y e h hn, rt1_clause895_202 y e h hn, rt1_clause895_203 y e h hn] at bad

  simp at bad

theorem rt1_model_shift895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
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

theorem rt1_upper_window895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) :
    (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat ≥
      (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat := by
  have hs := rt1_model_shift895 y e h v
  have hu := rt1_upper_zero_split895 (fun p a => y (v+p) a) (fun p => e (v+p)) hs
  simpa only [add_zero, zero_add, add_sub_assoc, zero_sub, sub_eq_add_neg, add_assoc] using hu

end RT1Upper895

theorem cycle_power_eight_corrected_count_upper_window (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) : (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat ≥ (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat := by
  exact RT1Upper895.rt1_upper_window895 y e h v
