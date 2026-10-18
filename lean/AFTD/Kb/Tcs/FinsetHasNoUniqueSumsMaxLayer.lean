import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetUnorderedSumRepCount
import AFTD.Kb.Tcs.FinsetSumCollisionPreserving

/-!
# finset_has_no_unique_sums_max_layer

Topic: combinatorics   Node: f6d38bdb10ae

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

Let A be NUS and let x be a rational collision-preserving weight on A. Then the set of elements of A maximizing x (i.e. {a ∈ A : x a = M} for a value M attained and dominating all of x on A) is again NUS.
-/

/-- The top layer of a collision-preserving weight on a NUS set is again NUS: this is the maximum-layer argument behind Lemma 2.1 of arXiv:2610.09349. -/
theorem finset_has_no_unique_sums_max_layer {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (hA : finset_has_no_unique_sums A) (x : G → ℚ)
    (hx : finset_sum_collision_preserving A x) (M : ℚ)
    (hM : ∀ a ∈ A, x a ≤ M) (hMne : ∃ a ∈ A, x a = M) :
    finset_has_no_unique_sums (A.filter (fun a => x a = M)) := by
  classical
  set L : Finset G := A.filter (fun a => x a = M) with hL
  have hmemL : ∀ a, a ∈ L ↔ a ∈ A ∧ x a = M := by
    intro a; rw [hL, Finset.mem_filter]
  have hAL : L ⊆ A := by rw [hL]; exact Finset.filter_subset _ _
  have key : ∀ p ∈ L, ∀ q ∈ L, ∀ a ∈ A, ∀ b ∈ A, a + b = p + q → x a = M ∧ x b = M := by
    intro p hp q hq a ha b hb hab
    obtain ⟨hpA, hpM⟩ := (hmemL p).mp hp
    obtain ⟨hqA, hqM⟩ := (hmemL q).mp hq
    have hcol : x a + x b = x p + x q := hx a ha b hb p hpA q hqA hab
    have ha' : x a ≤ M := hM a ha
    have hb' : x b ≤ M := hM b hb
    constructor <;> linarith
  constructor
  · obtain ⟨a₀, ha₀A, ha₀M⟩ := hMne
    have ha₀L : a₀ ∈ L := (hmemL a₀).mpr ⟨ha₀A, ha₀M⟩
    have hrep : 2 ≤ finset_unordered_sum_rep_count A (a₀ + a₀) := hA.2 a₀ ha₀A a₀ ha₀A
    have hcard : 1 < (A.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = a₀ + a₀)).card := hrep
    obtain ⟨z, hzS, hzne⟩ := Finset.exists_mem_ne hcard (Sym2.mk a₀ a₀)
    obtain ⟨c, d, hcd⟩ := (Sym2.exists (α := G) (f := fun w => w = z)).mp ⟨z, rfl⟩
    have hzS' : Sym2.mk c d ∈ A.sym2.filter (fun w => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ w = a₀ + a₀) := by
      rw [hcd]; exact hzS
    rw [Finset.mem_filter] at hzS'
    obtain ⟨hzA, hzsum⟩ := hzS'
    obtain ⟨hcA, hdA⟩ := Finset.mk_mem_sym2_iff.mp hzA
    have hsum : c + d = a₀ + a₀ := by
      rw [Sym2.lift_mk] at hzsum; exact hzsum
    obtain ⟨hcM, hdM⟩ := key a₀ ha₀L a₀ ha₀L c hcA d hdA hsum
    have hne : c ≠ a₀ ∨ d ≠ a₀ := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hzne (by rw [← hcd, h.1, h.2])
    rcases hne with h | h
    · exact Finset.one_lt_card.mpr ⟨a₀, ha₀L, c, (hmemL c).mpr ⟨hcA, hcM⟩, Ne.symm h⟩
    · exact Finset.one_lt_card.mpr ⟨a₀, ha₀L, d, (hmemL d).mpr ⟨hdA, hdM⟩, Ne.symm h⟩
  · intro p hp q hq
    have hpA : p ∈ A := hAL hp
    have hqA : q ∈ A := hAL hq
    have hset : (A.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = p + q))
        = (L.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = p + q)) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hzA, hz⟩
        refine ⟨Finset.mem_sym2_iff.mpr ?_, hz⟩
        intro a ha
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp ha
        have hbA : b ∈ A := by
          have h1 : Sym2.mk a b ∈ A.sym2 := by rw [← hb]; exact hzA
          exact (Finset.mk_mem_sym2_iff.mp h1).2
        have hab : a + b = p + q := by
          rw [hb, Sym2.lift_mk] at hz; exact hz
        exact (hmemL a).mpr ⟨Finset.mem_sym2_iff.mp hzA a ha,
          (key p hp q hq a (Finset.mem_sym2_iff.mp hzA a ha) b hbA hab).1⟩
      · rintro ⟨hzL, hz⟩
        exact ⟨Finset.sym2_mono hAL hzL, hz⟩
    have h1 : finset_unordered_sum_rep_count L (p + q)
        = (L.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = p + q)).card := rfl
    have h2 : finset_unordered_sum_rep_count A (p + q)
        = (A.sym2.filter (fun z => Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ z = p + q)).card := rfl
    rw [h1, ← hset, ← h2]
    exact hA.2 p hpA q hqA
