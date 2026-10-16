import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# ErrorCorrectingCodes.Codeword.hamming_ball_size

Topic: information   Node: 7e312ee9f435

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.hamming_ball_size`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/HammingBound.lean (Apache-2.0); 1 adapted; compiled here.

Cardinality of Hamming balls. Let $\alpha$ be a finite alphabet, and regard a codeword of length $n$ as a function
$\mathrm{Fin}\,n \to \alpha$, with the Hamming distance $d(x,y)$ counting the
coordinates in which two codewords differ. For every radius $l$ and every center
codeword $c$, the Hamming ball $B_l(c) = \{c' : d(c',c) \le l\}$ has cardinality
\[
\abs{B_l(c)} \;=\; \sum_{i=0}^{l} \binom{n}{i}\,(\abs{\alpha}-1)^{i},
\]
where $\abs{\alpha}$ is the number of symbols in the alphabet.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ErrorCorrectingCodes ErrorCorrectingCodes.Codeword in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Volume formula**: the Hamming ball of radius `l` centred at any codeword has exactly `Σ_{i=0}^{l} C(n,i) · (|α|-1)^i` elements. -/
theorem ErrorCorrectingCodes.Codeword.hamming_ball_size (n l : ℕ) :
    ∀ c : Codeword n α,
      (hamming_ball l c).card =
        Finset.sum (Finset.range (l + 1)) (λ i => Nat.choose n i * (Fintype.card α - 1)^i) := by {
  intro c
  simp

  have h_card_x0 : ∀ d, {c' : Codeword n α | hamming_distance c' Codeword.zero = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d := by
    intro d
    dsimp [hamming_distance, zero]

    let d_comb : Finset (Finset (Fin n)) := Finset.powersetCard d Finset.univ
    have h_card_d_comb : d_comb.card = Nat.choose n d := by
      simp [d_comb]

    let α_nonzero := {x : α | x ≠ 0}.toFinset
    have h_card_α_nonzero : α_nonzero.card = Fintype.card α - 1 := by
      have h0 : α_nonzero = Finset.univ.erase 0 := by ext x; simp [α_nonzero]
      rw [h0, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

    have h_card_fun : ∀ s ∈ d_comb, Fintype.card (s → α_nonzero) = (Fintype.card α - 1)^d := by
      intro s hs
      rw [Fintype.card_fun]
      rw [show Fintype.card { x // x ∈ α_nonzero } = Fintype.card α - 1 by
        simpa using h_card_α_nonzero]
      dsimp[d_comb] at hs
      simp! at *
      rw[hs]

    let f := fun (s : Finset (Fin n)) ↦ (Finset.univ : Finset (s → α_nonzero))

    have : ∀ s ∈ d_comb, (f s).card = (Fintype.card α - 1)^d := by intro s hs; exact h_card_fun s hs

    let S := d_comb.sigma f
    have h_card_S : S.card = Nat.choose n d * (Fintype.card α - 1) ^ d := by
      simp [S]
      rw [Finset.sum_eq_card_nsmul this, h_card_d_comb]
      rfl

    rw[←h_card_S]
    let f' : (s : ((k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero }))) → s ∈ S → Codeword n α := fun s _ ↦ (fun i ↦ if h : i ∈ s.1 then s.2 ⟨i, h⟩ else 0)

    symm
    apply Finset.card_bij f'

    -- f' maps S to the hamming ball
    have h_f'_map_to_ball: ∀ (a : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S), f' a ha ∈ toFinset {c' | hammingDist c' zero = d} := by
      intros a ha
      dsimp[S] at ha
      apply Finset.mem_sigma.1 at ha
      rw [Set.mem_toFinset, Set.mem_setOf_eq]
      have hcard : (Finset.univ.filter (fun i => i ∈ a.fst)).card = d := by
        simpa [d_comb] using ha.1
      rw [← hcard]
      unfold hammingDist
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hx : x ∈ a.fst
      · have hmem := (a.snd ⟨x, hx⟩).2
        simp only [α_nonzero, Set.mem_toFinset, Set.mem_setOf_eq] at hmem
        simp [f', zero, hx, hmem]
      · simp [f', zero, hx]

    exact h_f'_map_to_ball

    -- f' is injective
    have h_f'_injective: ∀ (a : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S),
     ∀ (b : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (hb : b ∈ S), f' a ha = f' b hb → a = b := by
      intros a h_a b h_b
      intro h_feq
      let f_a := (f' a h_a)
      let f_b := (f' b h_b)
      have fab_eq: f_a = f_b := by exact h_feq

      have first_eq: a.1 = b.1 := by
        ext x
        constructor
        · intro h1
          by_contra h_xb
          have h_fbzero: f_b x = 0 := by simp[f_b, f']; intro h_inb; exact absurd h_inb h_xb
          have h_fazero: f_a x = 0 := by rw[fab_eq]; exact h_fbzero
          dsimp[f_a, f'] at h_fazero; simp at h_fazero
          let a₀ := a.2 ⟨x, h1⟩
          apply h_fazero at h1
          have h_azero : ¬a₀.val ≠ 0 := by simp; exact h1
          have h_anonzero : a₀.val ∈ α_nonzero := by exact a₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_anonzero
          exact absurd h_anonzero h_azero
        · intro h2
          by_contra h_xa
          have h_fazero: f_a x = 0 := by simp[f_a, f']; intro h_ina; exact absurd h_ina h_xa
          have h_fbzero: f_b x = 0 := by rw[←fab_eq]; exact h_fazero
          dsimp[f_b, f'] at h_fbzero; simp at h_fbzero
          let b₀ := b.2 ⟨x, h2⟩
          apply h_fbzero at h2
          have h_bzero : ¬b₀.val ≠ 0 := by simp; exact h2
          have h_bnonzero : b₀.val ∈ α_nonzero := by exact b₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_bnonzero
          exact absurd h_bnonzero h_bzero

      have h_2eq : ({ x // x ∈ b.fst } → { x // x ∈ α_nonzero }) = ({ x // x ∈ a.fst } → { x // x ∈ α_nonzero }) := by rw[first_eq]

      let b' := cast h_2eq b.2
      have h_bheq : HEq b' b.2 := by simp[b']

      ext
      rw[first_eq]
      refine HEq.symm (heq_of_cast_eq h_2eq ?h_f'_injective.a.x)
      funext x
      suffices b' x = a.snd x by {
        exact this
      }

      have h₁' : f_a x = a.2 x := by
        simp [f_a, f']
      have h₂ : (f_a x) = (f_b x) := by rw[fab_eq]
      have h₃ : (f_b x) = (b' x) := by
        dsimp[f_b, f']
        have h₃' : ↑x ∈ b.1 := by
          have h₃'' : ↑x ∈ a.1 := by simp
          rw[← first_eq]
          exact h₃''
        simp[h₃']

        have : Sigma.snd b { val := ↑x, property := (h₃' : ↑x ∈ b.fst) } = b' x := by
          try dsimp[f_b, f']
          apply congr_heq -- Life Saving Theorem
          exact h_bheq.symm
          refine (Subtype.heq_iff_coe_eq ?this.h₂.h).mpr rfl
          rw[first_eq]
          tauto
        exact this


      rw[h₃] at h₂
      rw[h₂] at h₁'
      exact SetCoe.ext h₁'

    exact h_f'_injective

    -- f' is surjective
    have h_f'_surjective: ∀ b ∈ toFinset {c' | hammingDist c' zero = d}, ∃ a, ∃ (ha : a ∈ S), f' a ha = b := by
      intro b
      intro h_b
      let a₁ := toFinset { i | b i ≠ 0 }

      have h_y : ∀ y ∈ a₁, (b ↑y) ∈ α_nonzero := by
        intro y hy
        simp [α_nonzero, a₁] at hy ⊢
        exact hy

      let a₂ (y : { x // x ∈ a₁ }) : { x // x ∈ α_nonzero } := ⟨b y, by {
        apply h_y
        exact y.property
      }⟩

      use ⟨a₁, a₂⟩

      have h_a : ⟨a₁, a₂⟩ ∈ S := by
        simp[a₁, a₂, S, d_comb]
        have h_d : hammingDist b zero = d := by rw[Set.mem_toFinset, Set.mem_setOf] at h_b; exact h_b
        unfold hammingDist at h_d
        have h_setEq : (toFinset {i | ¬b i = 0}) = (filter (fun i => b i ≠ zero i) Finset.univ) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq]
          exact Iff.rfl
        constructor
        · exact h_d
        · simp[f]

      use h_a
      funext x
      by_cases h_x : b x = 0
      · have hx : x ∉ a₁ := by simp [a₁, h_x]
        simp [f', hx, h_x]
      · have hx : x ∈ a₁ := by simp [a₁, h_x]
        simp [f', hx, a₂]

    exact h_f'_surjective




  have h_card_dist_eq : ∀ d, {c' : Codeword n α | hamming_distance c' c = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d := by
    intro d
    rw[← h_card_x0]
    apply Finset.card_bij (fun a _ ↦ sub a c)
    · intro a ha
      rw [Set.mem_toFinset, Set.mem_setOf_eq] at ha ⊢
      unfold hamming_distance at ha ⊢
      rw [← ha, hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm]
      congr 1; ext i; simp [sub, zero]; try ring
    · intro a _ b _ hab
      ext i
      have := congrFun hab i
      simpa [sub] using this
    · intro b hb
      refine ⟨add b c, ?_, ?_⟩
      · rw [Set.mem_toFinset, Set.mem_setOf_eq] at hb ⊢
        unfold hamming_distance at hb ⊢
        rw [← hb, hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm]
        congr 1; ext i; simp [add, zero]
      · ext i; simp [sub, add]

  induction l
  · simp [hamming_distance]
    refine (Fintype.existsUnique_iff_card_one fun x => x = c).mp ?_
    simp
  · expose_names

    rw[Nat.succ_add]
    rw[Finset.sum_range_succ]
    rw[← h]

    have : Fintype.card { x // hamming_distance x c ≤n_1+ 1 } = Fintype.card { x // hamming_distance x c ≤n_1} + Fintype.card { x // hamming_distance x c = n_1 + 1} := by
      have : fun x ↦ hamming_distance x c ≤ n_1 + 1 = fun x ↦ hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 := by
        ext x
        constructor
        · intros h_d1
          apply Nat.eq_or_lt_of_le at h_d1
          rcases h_d1 with hl | hr
          right
          exact hl
          left
          linarith
        · intros h_or
          rcases h_or with hl | hr
          linarith
          linarith

      have : {x // hamming_distance x c ≤ n_1 + 1} = {x // hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 } := by exact congrArg Subtype this

      have : Fintype.card {x // hamming_distance x c ≤ n_1 + 1} = Fintype.card {x // hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 } := by exact Fintype.card_congr' this

      rw[this]

      have : Disjoint (fun x ↦ hamming_distance x c ≤ n_1)  (fun x ↦ hamming_distance x c = n_1 + 1) := by
        apply Pi.disjoint_iff.2
        intros c'
        simp
        intro hc'
        linarith

      apply Fintype.card_subtype_or_disjoint
      exact this

    rw[Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype] at this
    rw[this]
    simp
    have : {c' : Codeword n α | hamming_distance c' c = n_1 + 1}.toFinset.card = Nat.choose n (n_1 + 1) * (Fintype.card α - 1)^(n_1 + 1) := by exact h_card_dist_eq (n_1 + 1)
    simp at this
    linarith
}
