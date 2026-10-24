import AFTD.Prelude

/-!
# nat_le_sixty_three_in_span_powers_of_two

Topic: combinatorial_games   Node: e875aa25504d

Provenance: helper lemma. arXiv:2610.15145 Theorem 7.3 proof

If a set $S$ of natural numbers contains $0$ and the powers of two $2^i$ for all $0 \le i \le 5$, and is closed under bitwise XOR, then every natural number $g \le 63$ belongs to $S$.
-/

/-- Any subset of natural numbers containing 0 and the first six powers of 2 and closed under XOR contains all integers up to 63. -/
theorem nat_le_sixty_three_in_span_powers_of_two (S : Set ℕ) (h0 : 0 ∈ S) (hp : ∀ i : ℕ, i ≤ 5 → 2^i ∈ S) (hxor : ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S) (g : ℕ) (hg : g ≤ 63) : g ∈ S := by
  have h1 : (1 : ℕ) ∈ S := hp 0 (by omega)
  have h2 : (2 : ℕ) ∈ S := hp 1 (by omega)
  have h3 : (3 : ℕ) ∈ S := hxor 2 h2 1 h1
  have h4 : (4 : ℕ) ∈ S := hp 2 (by omega)
  have h5 : (5 : ℕ) ∈ S := hxor 4 h4 1 h1
  have h6 : (6 : ℕ) ∈ S := hxor 4 h4 2 h2
  have h7 : (7 : ℕ) ∈ S := hxor 4 h4 3 h3
  have h8 : (8 : ℕ) ∈ S := hp 3 (by omega)
  have h9 : (9 : ℕ) ∈ S := hxor 8 h8 1 h1
  have h10 : (10 : ℕ) ∈ S := hxor 8 h8 2 h2
  have h11 : (11 : ℕ) ∈ S := hxor 8 h8 3 h3
  have h12 : (12 : ℕ) ∈ S := hxor 8 h8 4 h4
  have h13 : (13 : ℕ) ∈ S := hxor 8 h8 5 h5
  have h14 : (14 : ℕ) ∈ S := hxor 8 h8 6 h6
  have h15 : (15 : ℕ) ∈ S := hxor 8 h8 7 h7
  have h16 : (16 : ℕ) ∈ S := hp 4 (by omega)
  have h17 : (17 : ℕ) ∈ S := hxor 16 h16 1 h1
  have h18 : (18 : ℕ) ∈ S := hxor 16 h16 2 h2
  have h19 : (19 : ℕ) ∈ S := hxor 16 h16 3 h3
  have h20 : (20 : ℕ) ∈ S := hxor 16 h16 4 h4
  have h21 : (21 : ℕ) ∈ S := hxor 16 h16 5 h5
  have h22 : (22 : ℕ) ∈ S := hxor 16 h16 6 h6
  have h23 : (23 : ℕ) ∈ S := hxor 16 h16 7 h7
  have h24 : (24 : ℕ) ∈ S := hxor 16 h16 8 h8
  have h25 : (25 : ℕ) ∈ S := hxor 16 h16 9 h9
  have h26 : (26 : ℕ) ∈ S := hxor 16 h16 10 h10
  have h27 : (27 : ℕ) ∈ S := hxor 16 h16 11 h11
  have h28 : (28 : ℕ) ∈ S := hxor 16 h16 12 h12
  have h29 : (29 : ℕ) ∈ S := hxor 16 h16 13 h13
  have h30 : (30 : ℕ) ∈ S := hxor 16 h16 14 h14
  have h31 : (31 : ℕ) ∈ S := hxor 16 h16 15 h15
  have h32 : (32 : ℕ) ∈ S := hp 5 (by omega)
  have h33 : (33 : ℕ) ∈ S := hxor 32 h32 1 h1
  have h34 : (34 : ℕ) ∈ S := hxor 32 h32 2 h2
  have h35 : (35 : ℕ) ∈ S := hxor 32 h32 3 h3
  have h36 : (36 : ℕ) ∈ S := hxor 32 h32 4 h4
  have h37 : (37 : ℕ) ∈ S := hxor 32 h32 5 h5
  have h38 : (38 : ℕ) ∈ S := hxor 32 h32 6 h6
  have h39 : (39 : ℕ) ∈ S := hxor 32 h32 7 h7
  have h40 : (40 : ℕ) ∈ S := hxor 32 h32 8 h8
  have h41 : (41 : ℕ) ∈ S := hxor 32 h32 9 h9
  have h42 : (42 : ℕ) ∈ S := hxor 32 h32 10 h10
  have h43 : (43 : ℕ) ∈ S := hxor 32 h32 11 h11
  have h44 : (44 : ℕ) ∈ S := hxor 32 h32 12 h12
  have h45 : (45 : ℕ) ∈ S := hxor 32 h32 13 h13
  have h46 : (46 : ℕ) ∈ S := hxor 32 h32 14 h14
  have h47 : (47 : ℕ) ∈ S := hxor 32 h32 15 h15
  have h48 : (48 : ℕ) ∈ S := hxor 32 h32 16 h16
  have h49 : (49 : ℕ) ∈ S := hxor 32 h32 17 h17
  have h50 : (50 : ℕ) ∈ S := hxor 32 h32 18 h18
  have h51 : (51 : ℕ) ∈ S := hxor 32 h32 19 h19
  have h52 : (52 : ℕ) ∈ S := hxor 32 h32 20 h20
  have h53 : (53 : ℕ) ∈ S := hxor 32 h32 21 h21
  have h54 : (54 : ℕ) ∈ S := hxor 32 h32 22 h22
  have h55 : (55 : ℕ) ∈ S := hxor 32 h32 23 h23
  have h56 : (56 : ℕ) ∈ S := hxor 32 h32 24 h24
  have h57 : (57 : ℕ) ∈ S := hxor 32 h32 25 h25
  have h58 : (58 : ℕ) ∈ S := hxor 32 h32 26 h26
  have h59 : (59 : ℕ) ∈ S := hxor 32 h32 27 h27
  have h60 : (60 : ℕ) ∈ S := hxor 32 h32 28 h28
  have h61 : (61 : ℕ) ∈ S := hxor 32 h32 29 h29
  have h62 : (62 : ℕ) ∈ S := hxor 32 h32 30 h30
  have h63 : (63 : ℕ) ∈ S := hxor 32 h32 31 h31
  interval_cases g <;> assumption
