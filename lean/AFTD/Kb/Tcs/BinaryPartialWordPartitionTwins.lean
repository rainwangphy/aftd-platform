import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeMem
import AFTD.Kb.Tcs.BinaryPartialWordCubeCoverIff

/-!
# binary_partial_word_partition_twins

Topic: combinatorics   Node: a23691bf6e45

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

If a coordinate appears in exactly two parts of a Boolean cube partition, once at each value, those parts have equal supports and agree at every other supported coordinate.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_twins
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (v : V) (hsing : ∀ bit : Bool,
      (univ.filter (fun i => v ∈ s i ∧ b i v = bit)).card = 1) :
    ∃ i₀ i₁ : I, i₀ ≠ i₁ ∧ v ∈ s i₀ ∧ b i₀ v = false ∧
      v ∈ s i₁ ∧ b i₁ v = true ∧
      (∀ i, v ∈ s i → i = i₀ ∨ i = i₁) ∧ s i₀ = s i₁ ∧
      (∀ w ∈ s i₀, w ≠ v → b i₀ w = b i₁ w) := by
  classical
  obtain ⟨i₀, hi₀⟩ := card_eq_one.mp (hsing false)
  obtain ⟨i₁, hi₁⟩ := card_eq_one.mp (hsing true)
  have hzero : v ∈ s i₀ ∧ b i₀ v = false := by
    have : i₀ ∈ univ.filter (fun i => v ∈ s i ∧ b i v = false) := by rw [hi₀]; simp
    exact (mem_filter.mp this).2
  have hone : v ∈ s i₁ ∧ b i₁ v = true := by
    have : i₁ ∈ univ.filter (fun i => v ∈ s i ∧ b i v = true) := by rw [hi₁]; simp
    exact (mem_filter.mp this).2
  have hne : i₀ ≠ i₁ := by
    intro he
    have : b i₀ v = true := he ▸ hone.2
    rw [hzero.2] at this
    contradiction
  have huniq (i : I) (hvi : v ∈ s i) : i = i₀ ∨ i = i₁ := by
    cases hbit : b i v
    · left
      have : i ∈ univ.filter (fun j => v ∈ s j ∧ b j v = false) :=
        mem_filter.mpr ⟨mem_univ _, hvi, hbit⟩
      simpa only [hi₀, mem_singleton] using this
    · right
      have : i ∈ univ.filter (fun j => v ∈ s j ∧ b j v = true) :=
        mem_filter.mpr ⟨mem_univ _, hvi, hbit⟩
      simpa only [hi₁, mem_singleton] using this
  have hflip (a d : I) (had : a ≠ d) (hva : v ∈ s a) (hvd : v ∈ s d)
      (hopp : b d v = !(b a v))
      (honly : ∀ j, v ∈ s j → j = a ∨ j = d) :
      ∀ f, f ∈ binary_partial_word_cube (s a) (b a) →
        Function.update f v (!f v) ∈ binary_partial_word_cube (s d) (b d) := by
    intro f hf
    let g := Function.update f v (!f v)
    obtain ⟨j, hj⟩ := (binary_partial_word_cube_cover_iff s b).mp hcover g
    have hfv : f v = b a v := (binary_partial_word_cube_mem _ _ _).mp hf v hva
    have hja : j ≠ a := by
      intro he
      subst j
      have heq := hj v hva
      have hnot : (!f v) ≠ f v := by cases f v <;> decide
      exact hnot (by simpa only [g, Function.update_self, ← hfv] using heq)
    have hvj : v ∈ s j := by
      by_contra hn
      obtain ⟨w, hw, hbits⟩ := hconflict a j hja.symm
      have hwv : w ≠ v := by rintro rfl; exact hn (mem_inter.mp hw).2
      have he := hj w (mem_inter.mp hw).2
      have hfa := (binary_partial_word_cube_mem _ _ _).mp hf w (mem_inter.mp hw).1
      exact hbits (hfa.symm.trans (by simpa only [g, Function.update_of_ne hwv] using he))
    have hjd : j = d := (honly j hvj).resolve_left hja
    subst j
    exact (binary_partial_word_cube_mem _ _ _).mpr hj
  have hf₀ := hflip i₀ i₁ hne hzero.1 hone.1 (by simp [hzero.2, hone.2]) huniq
  have hf₁ := hflip i₁ i₀ hne.symm hone.1 hzero.1 (by simp [hzero.2, hone.2])
    (fun j hj => (huniq j hj).symm)
  have hsub (a d : I)
      (hflipad : ∀ f, f ∈ binary_partial_word_cube (s a) (b a) →
        Function.update f v (!f v) ∈ binary_partial_word_cube (s d) (b d))
      (hva : v ∈ s a) : s d ⊆ s a := by
    intro w hwd
    by_contra hwa
    have hwv : w ≠ v := by rintro rfl; exact hwa hva
    let f := Function.update (b a) w (!(b d w))
    have hf : f ∈ binary_partial_word_cube (s a) (b a) := by
      rw [binary_partial_word_cube_mem]
      intro u hu
      have huw : u ≠ w := by rintro rfl; exact hwa hu
      simp only [f, Function.update_of_ne huw]
    have hgd := hflipad f hf
    have he := (binary_partial_word_cube_mem _ _ _).mp hgd w hwd
    have hnot : (!(b d w)) ≠ b d w := by cases b d w <;> decide
    exact hnot (by simpa only [Function.update_of_ne hwv, f, Function.update_self] using he)
  have hsupport : s i₀ = s i₁ := (hsub i₁ i₀ hf₁ hone.1).antisymm (hsub i₀ i₁ hf₀ hzero.1)
  refine ⟨i₀, i₁, hne, hzero.1, hzero.2, hone.1, hone.2, huniq, hsupport, ?_⟩
  intro w hw hwv
  have hbmem : b i₀ ∈ binary_partial_word_cube (s i₀) (b i₀) :=
    (binary_partial_word_cube_mem _ _ _).mpr (fun u hu => rfl)
  have hgd := hf₀ (b i₀) hbmem
  have he := (binary_partial_word_cube_mem _ _ _).mp hgd w (hsupport ▸ hw)
  simpa only [Function.update_of_ne hwv] using he
