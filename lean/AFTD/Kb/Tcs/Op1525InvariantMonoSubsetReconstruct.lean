import AFTD.Prelude

/-!
# op1525_invariant_mono_subset_reconstruct

Topic: combinatorics   Node: baa6946926f0

Provenance: original. Related work: A structural reconstruction criterion for the partition-switching model in OP-1525; compare arXiv:2611.13901, Section 4.1.

Let A and B be Boolean colorings of a set V, and let P be a predicate on permutations of V preserving a subset S. Assume A is constant on S, that S has three distinct points, and that two distinct points lie outside S. Suppose a bijection π matches every one-point flip of A with the flip of B at π(v), up to a permutation allowed by P and a global color exchange, with those choices allowed to vary by card. Then A and B themselves agree up to a permitted permutation and global color exchange. No finiteness or group-closure assumption is needed.
-/

namespace OP1525Mono
variable {V : Type} [DecidableEq V]

def flip (f : V → Bool) (v x : V) : Bool := xor (f x) (decide (x = v))
def mono (S : Set V) (f : V → Bool) : Prop := ∀ x ∈ S, ∀ y ∈ S, f x = f y

lemma xor_cancel_common (x y c : Bool) : xor x c = xor y c → x = y := by
  cases x <;> cases y <;> cases c <;> decide
lemma xor_cancel_flip (a b c d : Bool) : xor a d = xor (xor b d) c → a = xor b c := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma fresh_of_three (S : Set V) (a b c : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u v : V) :
    ∃ z ∈ S, z ≠ u ∧ z ≠ v := by
  by_cases h : a ≠ u ∧ a ≠ v
  · exact ⟨a, ha, h⟩
  by_cases h' : b ≠ u ∧ b ≠ v
  · exact ⟨b, hb, h'⟩
  by_cases h'' : c ≠ u ∧ c ≠ v
  · exact ⟨c, hc, h''⟩
  exfalso
  push_neg at h h' h''
  have ha' : a = u ∨ a = v := by by_cases ht : a = u <;> aesop
  have hb' : b = u ∨ b = v := by by_cases ht : b = u <;> aesop
  have hc' : c = u ∨ c = v := by by_cases ht : c = u <;> aesop
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
    rcases hc' with hc' | hc' <;> subst_vars <;> contradiction

lemma mono_of_two_flips (S : Set V) (f : V → Bool) (u v : V) (huv : u ≠ v)
    (hthree : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h1 : mono S (flip f u)) (h2 : mono S (flip f v)) : mono S f := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hthree
  obtain ⟨z, hz, hzu, hzv⟩ := fresh_of_three S a b c ha hb hc hab hac hbc u v
  have heq (x : V) (hx : x ∈ S) : f x = f z := by
    by_cases hxu : x = u
    · have hxv : x ≠ v := by simpa [hxu] using huv
      have hh := h2 x hx z hz
      simpa [mono, flip, hxv, hzv] using hh
    · have hh := h1 x hx z hz
      simpa [mono, flip, hxu, hzu] using hh
  intro x hx y hy
  exact (heq x hx).trans (heq y hy).symm

lemma flip_outside_mono (S : Set V) (f : V → Bool) (v : V)
    (hf : mono S f) (hv : v ∉ S) : mono S (flip f v) := by
  intro x hx y hy
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hyv : y ≠ v := fun h => hv (h ▸ hy)
  simpa [flip, hxv, hyv] using hf x hx y hy

lemma transfer_mono (S : Set V) (F H : V → Bool) (g : Equiv.Perm V) (c : Bool)
    (hpres : ∀ x, x ∈ S ↔ g x ∈ S)
    (heq : ∀ x, F (g x) = xor (H x) c) (hF : mono S F) : mono S H := by
  intro x hx y hy
  apply xor_cancel_common _ _ c
  rw [← heq x, ← heq y]
  exact hF (g x) ((hpres x).mp hx) (g y) ((hpres y).mp hy)

end OP1525Mono

open OP1525Mono

theorem op1525_invariant_mono_subset_reconstruct
    {V : Type} [DecidableEq V]
    (A B : V → Bool) (P : Equiv.Perm V → Prop) (S : Set V)
    (a b c : V) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (u v : V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hA : ∀ x ∈ S, ∀ y ∈ S, A x = A y)
    (hpres : ∀ g, P g → ∀ x, x ∈ S ↔ g x ∈ S)
    (π : Equiv.Perm V)
    (hdeck : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (A (g x)) (decide (g x = w)) =
        xor (xor (B x) (decide (x = π w))) d) :
    ∃ g, P g ∧ ∃ d : Bool, ∀ x, A (g x) = xor (B x) d := by
  have hthree : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  obtain ⟨g1, hg1, d1, heq1⟩ := hdeck u
  obtain ⟨g2, hg2, d2, heq2⟩ := hdeck v
  have hB1 : mono S (flip B (π u)) :=
    transfer_mono S _ _ g1 d1 (hpres g1 hg1) heq1 (flip_outside_mono S A u hA hu)
  have hB2 : mono S (flip B (π v)) :=
    transfer_mono S _ _ g2 d2 (hpres g2 hg2) heq2 (flip_outside_mono S A v hA hv)
  have hB : mono S B := mono_of_two_flips S B (π u) (π v) (fun h => huv (π.injective h)) hthree hB1 hB2
  obtain ⟨g, hg, d, heq⟩ := hdeck a
  let q := g.symm a
  have hgq : g q = a := by simp [q]
  have hq : q ∈ S := by
    apply (hpres g hg q).mpr
    simpa [hgq] using ha
  have hmatch : q = π a := by
    by_contra hne
    obtain ⟨z, hz, hzq, hzw⟩ := fresh_of_three S a b c ha hb hc hab hac hbc q (π a)
    have hgzS : g z ∈ S := (hpres g hg z).mp hz
    have hgz : g z ≠ a := by
      intro he
      apply hzq
      apply g.injective
      simpa [hgq] using he
    have hAz : A (g z) = A a := hA (g z) hgzS a ha
    have hBqz : B q = B z := hB q hq z hz
    have hqeq := heq q
    have hzeq := heq z
    simp [hgq, hne, hBqz] at hqeq
    simp [hgz, hzw, hAz] at hzeq
    cases hAa : A a <;> cases hBz : B z <;> cases hd : d <;>
      simp [hAa, hBz, hd] at hqeq hzeq
  refine ⟨g, hg, d, ?_⟩
  intro x
  have hEq := heq x
  have hpred : (g x = a) ↔ x = π a := by
    constructor
    · intro h
      have hsame : g x = g q := h.trans hgq.symm
      exact (g.injective hsame).trans hmatch
    · intro h
      subst x
      simpa [hmatch] using hgq
  have hdec : decide (g x = a) = decide (x = π a) := by
    simp only [hpred]
  rw [hdec] at hEq
  exact xor_cancel_flip _ _ _ _ hEq
