import AFTD.Prelude

/-!
# b5_gap_nonneg

Topic: graphs   Node: 424994ea6843

Provenance: helper lemma. the polynomial core of b5_clique_bound_iff (the B_5 analogue of the computation in the proof of Theorem 3.1 of arXiv:2610.21388 (Stronger spectral bound for clique number))

For positive integers a, b, c, d, e with (a,b,c,d) ∉ {(1,1,1,1), (1,1,1,2), (1,2,1,1)}: tr ≤ n^2 (1 - 1/ω)^2 where tr = Σ (x-1)^2 + 2(ab + cd + bd + e(a+b+c+d)), n = a+b+c+d+e and ω = e + max(a+b, b+d, c+d).
-/

set_option maxHeartbeats 2000000 in
theorem b5_gap_A_m2 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ b + d) (h2 : c + d ≤ b + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ 2*(a:ℝ)*(c:ℝ) + 2*(a:ℝ)*(d:ℝ) - 2*(a:ℝ) + 2*(b:ℝ)*(c:ℝ) - 2*(c:ℝ) - 4 := by
  obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, b = c + r := ⟨b - c, by omega⟩
  rcases (show 2 ≤ a ∨ 2 ≤ c ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ r) ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ s) ∨
      (a = 1 ∧ c = 1 ∧ 1 ≤ r ∧ 1 ≤ s) by omega) with h | h | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h, h'⟩
  · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 1 + q := ⟨c - 1, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨p, rfl⟩ : ∃ p, a = 1 + p := ⟨a - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 2 + q := ⟨c - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 2 + t := ⟨r - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 1 + t := ⟨r - 1, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, s = 1 + u := ⟨s - 1, by omega⟩
    push_cast; ring_nf; positivity

set_option maxHeartbeats 2000000 in
theorem b5_gap_A_m3 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ c + d) (h2 : b + d ≤ c + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ 2*(a:ℝ)*(c:ℝ) + 2*(a:ℝ)*(d:ℝ) - 2*(a:ℝ) + 2*(b:ℝ)*(c:ℝ) - 2*(b:ℝ) - 4 := by
  obtain ⟨r, rfl⟩ : ∃ r, c = b + r := ⟨c - b, by omega⟩
  by_cases had : a ≤ d
  · obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
    rcases (show 2 ≤ a ∨ (a = 1 ∧ 3 ≤ b) ∨ (a = 1 ∧ b = 2 ∧ s = 0) ∨ (a = 1 ∧ b = 2 ∧ 1 ≤ s) ∨
        (a = 1 ∧ b = 1 ∧ 1 ≤ r) ∨ (a = 1 ∧ b = 1 ∧ r = 0 ∧ 2 ≤ s) by omega) with
      h | ⟨rfl, h⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩
    · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, b = 1 + q := ⟨b - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨q, rfl⟩ : ∃ q, b = 3 + q := ⟨b - 3, by omega⟩
      push_cast; ring_nf; positivity
    · push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 1 + v := ⟨s - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, r = 1 + v := ⟨r - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 2 + v := ⟨s - 2, by omega⟩
      push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, a = d + t := ⟨a - d, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, t = 1 + v := ⟨t - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, d = 1 + q := ⟨d - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, b = 1 + p := ⟨b - 1, by omega⟩
    push_cast; ring_nf; positivity

theorem b5_gap_A_m1 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : b + d ≤ a + b) (h2 : c + d ≤ a + b) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ 2*(a:ℝ)*(c:ℝ) + 2*(a:ℝ)*(d:ℝ) + 2*(b:ℝ)*(c:ℝ) - 2*(c:ℝ) - 2*(d:ℝ) - 4 := by
  have := b5_gap_A_m3 c d a b hc hd ha hb (by omega) (by omega) (by omega)
  ring_nf at this ⊢
  linarith

set_option maxHeartbeats 2000000 in
theorem b5_gap_D_m2 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ b + d) (h2 : c + d ≤ b + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ -2*(a:ℝ)^2 + 4*(a:ℝ)*(b:ℝ)*(c:ℝ) + 4*(a:ℝ)*(b:ℝ)*(d:ℝ) - 4*(a:ℝ)*(b:ℝ) + 4*(a:ℝ)*(c:ℝ)*(d:ℝ) + 4*(a:ℝ)*(d:ℝ)^2 - 2*(a:ℝ) + 4*(b:ℝ)^2*(c:ℝ) + 4*(b:ℝ)*(c:ℝ)*(d:ℝ) - 8*(b:ℝ) - 2*(c:ℝ)^2 - 4*(c:ℝ)*(d:ℝ) - 2*(c:ℝ) - 8*(d:ℝ) - 8 := by
  obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, b = c + r := ⟨b - c, by omega⟩
  rcases (show 2 ≤ a ∨ 2 ≤ c ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ r) ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ s) ∨
      (a = 1 ∧ c = 1 ∧ 1 ≤ r ∧ 1 ≤ s) by omega) with h | h | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h, h'⟩
  · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 1 + q := ⟨c - 1, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨p, rfl⟩ : ∃ p, a = 1 + p := ⟨a - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 2 + q := ⟨c - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 2 + t := ⟨r - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 1 + t := ⟨r - 1, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, s = 1 + u := ⟨s - 1, by omega⟩
    push_cast; ring_nf; positivity

set_option maxHeartbeats 2000000 in
theorem b5_gap_D_m3 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ c + d) (h2 : b + d ≤ c + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ -2*(a:ℝ)^2 - 4*(a:ℝ)*(b:ℝ) + 4*(a:ℝ)*(c:ℝ)^2 + 8*(a:ℝ)*(c:ℝ)*(d:ℝ) + 4*(a:ℝ)*(d:ℝ)^2 - 2*(a:ℝ) - 2*(b:ℝ)^2 + 4*(b:ℝ)*(c:ℝ)^2 + 4*(b:ℝ)*(c:ℝ)*(d:ℝ) - 4*(b:ℝ)*(d:ℝ) - 2*(b:ℝ) - 8*(c:ℝ) - 8*(d:ℝ) - 8 := by
  obtain ⟨r, rfl⟩ : ∃ r, c = b + r := ⟨c - b, by omega⟩
  by_cases had : a ≤ d
  · obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
    rcases (show 2 ≤ a ∨ (a = 1 ∧ 3 ≤ b) ∨ (a = 1 ∧ b = 2 ∧ s = 0) ∨ (a = 1 ∧ b = 2 ∧ 1 ≤ s) ∨
        (a = 1 ∧ b = 1 ∧ 1 ≤ r) ∨ (a = 1 ∧ b = 1 ∧ r = 0 ∧ 2 ≤ s) by omega) with
      h | ⟨rfl, h⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩
    · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, b = 1 + q := ⟨b - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨q, rfl⟩ : ∃ q, b = 3 + q := ⟨b - 3, by omega⟩
      push_cast; ring_nf; positivity
    · push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 1 + v := ⟨s - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, r = 1 + v := ⟨r - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 2 + v := ⟨s - 2, by omega⟩
      push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, a = d + t := ⟨a - d, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, t = 1 + v := ⟨t - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, d = 1 + q := ⟨d - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, b = 1 + p := ⟨b - 1, by omega⟩
    push_cast; ring_nf; positivity

theorem b5_gap_D_m1 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : b + d ≤ a + b) (h2 : c + d ≤ a + b) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ 4*(a:ℝ)^2*(c:ℝ) + 4*(a:ℝ)^2*(d:ℝ) + 8*(a:ℝ)*(b:ℝ)*(c:ℝ) + 4*(a:ℝ)*(b:ℝ)*(d:ℝ) - 8*(a:ℝ) + 4*(b:ℝ)^2*(c:ℝ) - 4*(b:ℝ)*(d:ℝ) - 8*(b:ℝ) - 2*(c:ℝ)^2 - 4*(c:ℝ)*(d:ℝ) - 2*(c:ℝ) - 2*(d:ℝ)^2 - 2*(d:ℝ) - 8 := by
  have := b5_gap_D_m3 c d a b hc hd ha hb (by omega) (by omega) (by omega)
  ring_nf at this ⊢
  linarith

set_option maxHeartbeats 2000000 in
theorem b5_gap_G_m2 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ b + d) (h2 : c + d ≤ b + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ -2*(a:ℝ)^2*(b:ℝ) - 2*(a:ℝ)^2*(d:ℝ) - (a:ℝ)^2 + 2*(a:ℝ)*(b:ℝ)^2*(c:ℝ) + 2*(a:ℝ)*(b:ℝ)^2*(d:ℝ) - 2*(a:ℝ)*(b:ℝ)^2 + 4*(a:ℝ)*(b:ℝ)*(c:ℝ)*(d:ℝ) + 4*(a:ℝ)*(b:ℝ)*(d:ℝ)^2 - 2*(a:ℝ)*(b:ℝ) + 2*(a:ℝ)*(c:ℝ)*(d:ℝ)^2 + 2*(a:ℝ)*(d:ℝ)^3 + 2*(a:ℝ)*(d:ℝ)^2 + 2*(b:ℝ)^3*(c:ℝ) + 4*(b:ℝ)^2*(c:ℝ)*(d:ℝ) + 2*(b:ℝ)^2*(c:ℝ) - 4*(b:ℝ)^2 - 2*(b:ℝ)*(c:ℝ)^2 + 2*(b:ℝ)*(c:ℝ)*(d:ℝ)^2 - 8*(b:ℝ)*(d:ℝ) - 8*(b:ℝ) - 2*(c:ℝ)^2*(d:ℝ) - (c:ℝ)^2 - 2*(c:ℝ)*(d:ℝ)^2 - 2*(c:ℝ)*(d:ℝ) - 4*(d:ℝ)^2 - 8*(d:ℝ) - 4 := by
  obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, b = c + r := ⟨b - c, by omega⟩
  rcases (show 2 ≤ a ∨ 2 ≤ c ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ r) ∨ (a = 1 ∧ c = 1 ∧ 2 ≤ s) ∨
      (a = 1 ∧ c = 1 ∧ 1 ≤ r ∧ 1 ≤ s) by omega) with h | h | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h, h'⟩
  · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 1 + q := ⟨c - 1, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨p, rfl⟩ : ∃ p, a = 1 + p := ⟨a - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, c = 2 + q := ⟨c - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 2 + t := ⟨r - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
    push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, r = 1 + t := ⟨r - 1, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, s = 1 + u := ⟨s - 1, by omega⟩
    push_cast; ring_nf; positivity

set_option maxHeartbeats 2000000 in
theorem b5_gap_G_m3 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : a + b ≤ c + d) (h2 : b + d ≤ c + d) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ -2*(a:ℝ)^2*(c:ℝ) - 2*(a:ℝ)^2*(d:ℝ) - (a:ℝ)^2 - 4*(a:ℝ)*(b:ℝ)*(c:ℝ) - 4*(a:ℝ)*(b:ℝ)*(d:ℝ) - 2*(a:ℝ)*(b:ℝ) + 2*(a:ℝ)*(c:ℝ)^3 + 6*(a:ℝ)*(c:ℝ)^2*(d:ℝ) + 2*(a:ℝ)*(c:ℝ)^2 + 6*(a:ℝ)*(c:ℝ)*(d:ℝ)^2 + 4*(a:ℝ)*(c:ℝ)*(d:ℝ) + 2*(a:ℝ)*(d:ℝ)^3 + 2*(a:ℝ)*(d:ℝ)^2 - 2*(b:ℝ)^2*(c:ℝ) - 2*(b:ℝ)^2*(d:ℝ) - (b:ℝ)^2 + 2*(b:ℝ)*(c:ℝ)^3 + 4*(b:ℝ)*(c:ℝ)^2*(d:ℝ) + 2*(b:ℝ)*(c:ℝ)^2 + 2*(b:ℝ)*(c:ℝ)*(d:ℝ)^2 - 2*(b:ℝ)*(d:ℝ)^2 - 2*(b:ℝ)*(d:ℝ) - 4*(c:ℝ)^2 - 8*(c:ℝ)*(d:ℝ) - 8*(c:ℝ) - 4*(d:ℝ)^2 - 8*(d:ℝ) - 4 := by
  obtain ⟨r, rfl⟩ : ∃ r, c = b + r := ⟨c - b, by omega⟩
  by_cases had : a ≤ d
  · obtain ⟨s, rfl⟩ : ∃ s, d = a + s := ⟨d - a, by omega⟩
    rcases (show 2 ≤ a ∨ (a = 1 ∧ 3 ≤ b) ∨ (a = 1 ∧ b = 2 ∧ s = 0) ∨ (a = 1 ∧ b = 2 ∧ 1 ≤ s) ∨
        (a = 1 ∧ b = 1 ∧ 1 ≤ r) ∨ (a = 1 ∧ b = 1 ∧ r = 0 ∧ 2 ≤ s) by omega) with
      h | ⟨rfl, h⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, rfl, h⟩
    · obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, b = 1 + q := ⟨b - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨q, rfl⟩ : ∃ q, b = 3 + q := ⟨b - 3, by omega⟩
      push_cast; ring_nf; positivity
    · push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 1 + v := ⟨s - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, r = 1 + v := ⟨r - 1, by omega⟩
      push_cast; ring_nf; positivity
    · obtain ⟨v, rfl⟩ : ∃ v, s = 2 + v := ⟨s - 2, by omega⟩
      push_cast; ring_nf; positivity
  · obtain ⟨t, rfl⟩ : ∃ t, a = d + t := ⟨a - d, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, t = 1 + v := ⟨t - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, d = 1 + q := ⟨d - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, b = 1 + p := ⟨b - 1, by omega⟩
    push_cast; ring_nf; positivity

theorem b5_gap_G_m1 (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h1 : b + d ≤ a + b) (h2 : c + d ≤ a + b) (hx : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d) :
    (0 : ℝ) ≤ 2*(a:ℝ)^3*(c:ℝ) + 2*(a:ℝ)^3*(d:ℝ) + 6*(a:ℝ)^2*(b:ℝ)*(c:ℝ) + 4*(a:ℝ)^2*(b:ℝ)*(d:ℝ) + 2*(a:ℝ)^2*(c:ℝ) + 2*(a:ℝ)^2*(d:ℝ) - 4*(a:ℝ)^2 + 6*(a:ℝ)*(b:ℝ)^2*(c:ℝ) + 2*(a:ℝ)*(b:ℝ)^2*(d:ℝ) + 4*(a:ℝ)*(b:ℝ)*(c:ℝ) - 8*(a:ℝ)*(b:ℝ) - 2*(a:ℝ)*(c:ℝ)^2 - 4*(a:ℝ)*(c:ℝ)*(d:ℝ) - 2*(a:ℝ)*(d:ℝ)^2 - 8*(a:ℝ) + 2*(b:ℝ)^3*(c:ℝ) + 2*(b:ℝ)^2*(c:ℝ) - 2*(b:ℝ)^2*(d:ℝ) - 4*(b:ℝ)^2 - 2*(b:ℝ)*(c:ℝ)^2 - 4*(b:ℝ)*(c:ℝ)*(d:ℝ) - 2*(b:ℝ)*(d:ℝ)^2 - 2*(b:ℝ)*(d:ℝ) - 8*(b:ℝ) - (c:ℝ)^2 - 2*(c:ℝ)*(d:ℝ) - (d:ℝ)^2 - 4 := by
  have := b5_gap_G_m3 c d a b hc hd ha hb (by omega) (by omega) (by omega)
  ring_nf at this ⊢
  linarith

theorem b5_gap_identity_m1 (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 * (e + (a + b) - 1) ^ 2
      - ((a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 + (d - 1) ^ 2 + (e - 1) ^ 2
        + 2 * (a * b + c * d + b * d + e * (a + b + c + d))) * (e + (a + b)) ^ 2
      = (2*a^3*c + 2*a^3*d + 6*a^2*b*c + 4*a^2*b*d + 2*a^2*c + 2*a^2*d - 4*a^2 + 6*a*b^2*c + 2*a*b^2*d + 4*a*b*c - 8*a*b - 2*a*c^2 - 4*a*c*d - 2*a*d^2 - 8*a + 2*b^3*c + 2*b^2*c - 2*b^2*d - 4*b^2 - 2*b*c^2 - 4*b*c*d - 2*b*d^2 - 2*b*d - 8*b - c^2 - 2*c*d - d^2 - 4) + (4*a^2*c + 4*a^2*d + 8*a*b*c + 4*a*b*d - 8*a + 4*b^2*c - 4*b*d - 8*b - 2*c^2 - 4*c*d - 2*c - 2*d^2 - 2*d - 8) * (e - 1) + (2*a*c + 2*a*d + 2*b*c - 2*c - 2*d - 4) * (e - 1) ^ 2 := by
  ring

theorem b5_gap_identity_m2 (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 * (e + (b + d) - 1) ^ 2
      - ((a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 + (d - 1) ^ 2 + (e - 1) ^ 2
        + 2 * (a * b + c * d + b * d + e * (a + b + c + d))) * (e + (b + d)) ^ 2
      = (-2*a^2*b - 2*a^2*d - a^2 + 2*a*b^2*c + 2*a*b^2*d - 2*a*b^2 + 4*a*b*c*d + 4*a*b*d^2 - 2*a*b + 2*a*c*d^2 + 2*a*d^3 + 2*a*d^2 + 2*b^3*c + 4*b^2*c*d + 2*b^2*c - 4*b^2 - 2*b*c^2 + 2*b*c*d^2 - 8*b*d - 8*b - 2*c^2*d - c^2 - 2*c*d^2 - 2*c*d - 4*d^2 - 8*d - 4) + (-2*a^2 + 4*a*b*c + 4*a*b*d - 4*a*b + 4*a*c*d + 4*a*d^2 - 2*a + 4*b^2*c + 4*b*c*d - 8*b - 2*c^2 - 4*c*d - 2*c - 8*d - 8) * (e - 1) + (2*a*c + 2*a*d - 2*a + 2*b*c - 2*c - 4) * (e - 1) ^ 2 := by
  ring

theorem b5_gap_identity_m3 (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 * (e + (c + d) - 1) ^ 2
      - ((a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 + (d - 1) ^ 2 + (e - 1) ^ 2
        + 2 * (a * b + c * d + b * d + e * (a + b + c + d))) * (e + (c + d)) ^ 2
      = (-2*a^2*c - 2*a^2*d - a^2 - 4*a*b*c - 4*a*b*d - 2*a*b + 2*a*c^3 + 6*a*c^2*d + 2*a*c^2 + 6*a*c*d^2 + 4*a*c*d + 2*a*d^3 + 2*a*d^2 - 2*b^2*c - 2*b^2*d - b^2 + 2*b*c^3 + 4*b*c^2*d + 2*b*c^2 + 2*b*c*d^2 - 2*b*d^2 - 2*b*d - 4*c^2 - 8*c*d - 8*c - 4*d^2 - 8*d - 4) + (-2*a^2 - 4*a*b + 4*a*c^2 + 8*a*c*d + 4*a*d^2 - 2*a - 2*b^2 + 4*b*c^2 + 4*b*c*d - 4*b*d - 2*b - 8*c - 8*d - 8) * (e - 1) + (2*a*c + 2*a*d - 2*a + 2*b*c - 2*b - 4) * (e - 1) ^ 2 := by
  ring

theorem b5_gap_nonneg (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hx : ¬ (a = 1 ∧ c = 1 ∧ ((b = 1 ∧ d = 1) ∨ (b = 1 ∧ d = 2) ∨ (b = 2 ∧ d = 1)))) :
    ((a : ℝ) - 1) ^ 2 + ((b : ℝ) - 1) ^ 2 + ((c : ℝ) - 1) ^ 2 + ((d : ℝ) - 1) ^ 2 + ((e : ℝ) - 1) ^ 2
        + 2 * ((a : ℝ) * b + c * d + b * d + e * (a + b + c + d))
      ≤ ((a : ℝ) + b + c + d + e) ^ 2 * (1 - 1 / ((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ)) ^ 2 := by
  have hx' : 2 ≤ a ∨ 2 ≤ c ∨ 4 ≤ b + d := by omega
  have hxR : (2:ℝ) ≤ a ∨ (2:ℝ) ≤ c ∨ (4:ℝ) ≤ b + d := by
    rcases hx' with h | h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (Or.inl (by exact_mod_cast h))
    · exact Or.inr (Or.inr (by exact_mod_cast h))
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hcR : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have heR : (0:ℝ) ≤ (e:ℝ) - 1 := by
    have : (1:ℝ) ≤ e := by exact_mod_cast he
    linarith
  have hw : (0:ℝ) < ((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ) := by
    have : 1 ≤ e + max (max (a + b) (b + d)) (c + d) := by omega
    exact_mod_cast this
  rw [show (1:ℝ) - 1 / ((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ)
      = (((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ) - 1)
        / ((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ) by field_simp]
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  have hcases : (max (max (a + b) (b + d)) (c + d) = a + b ∧ b + d ≤ a + b ∧ c + d ≤ a + b) ∨
      (max (max (a + b) (b + d)) (c + d) = b + d ∧ a + b ≤ b + d ∧ c + d ≤ b + d) ∨
      (max (max (a + b) (b + d)) (c + d) = c + d ∧ a + b ≤ c + d ∧ b + d ≤ c + d) := by omega
  rcases hcases with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩
  · rw [hm]; push_cast
    have h1R : (b:ℝ) + d ≤ a + b := by exact_mod_cast h1
    have h2R : (c:ℝ) + d ≤ a + b := by exact_mod_cast h2
    have hA := b5_gap_A_m1 a b c d ha hb hc hd h1 h2 hx'
    have hD := b5_gap_D_m1 a b c d ha hb hc hd h1 h2 hx'
    have hG := b5_gap_G_m1 a b c d ha hb hc hd h1 h2 hx'
    have key := b5_gap_identity_m1 a b c d e
    have := mul_nonneg hA (sq_nonneg ((e:ℝ) - 1))
    have := mul_nonneg hD heR
    linarith
  · rw [hm]; push_cast
    have h1R : (a:ℝ) + b ≤ b + d := by exact_mod_cast h1
    have h2R : (c:ℝ) + d ≤ b + d := by exact_mod_cast h2
    have hA := b5_gap_A_m2 a b c d ha hb hc hd h1 h2 hx'
    have hD := b5_gap_D_m2 a b c d ha hb hc hd h1 h2 hx'
    have hG := b5_gap_G_m2 a b c d ha hb hc hd h1 h2 hx'
    have key := b5_gap_identity_m2 a b c d e
    have := mul_nonneg hA (sq_nonneg ((e:ℝ) - 1))
    have := mul_nonneg hD heR
    linarith
  · rw [hm]; push_cast
    have h1R : (a:ℝ) + b ≤ c + d := by exact_mod_cast h1
    have h2R : (b:ℝ) + d ≤ c + d := by exact_mod_cast h2
    have hA := b5_gap_A_m3 a b c d ha hb hc hd h1 h2 hx'
    have hD := b5_gap_D_m3 a b c d ha hb hc hd h1 h2 hx'
    have hG := b5_gap_G_m3 a b c d ha hb hc hd h1 h2 hx'
    have key := b5_gap_identity_m3 a b c d e
    have := mul_nonneg hA (sq_nonneg ((e:ℝ) - 1))
    have := mul_nonneg hD heR
    linarith
