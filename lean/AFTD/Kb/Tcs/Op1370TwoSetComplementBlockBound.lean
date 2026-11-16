import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370ZeroFiberCount

/-!
# op1370_two_set_complement_block_bound

Topic: combinatorics   Node: fdc03de47dcc

Provenance: original. Related work: A conditional two-set deficit toward Conjecture 4.3 of arXiv:2611.12199, without uncomplementedness or nonemptiness assumptions.

Let n be at least three and let indexed families of subsets of Fin n be mutually strongly incomparable. Suppose there is a coordinate x such that for every nonempty family, some set {x,y} occurs in a different family and its complement occurs in a different family; these two other families may coincide. Then the total size of all families is at most 2^(n-1)-2.
-/

theorem op1370_two_set_complement_block_bound (n t : ℕ) (hn : 3 ≤ n)
    (𝒜 : Fin t → Finset (Finset (Fin n))) (hinc : strongly_incomparable 𝒜)
    (x : Fin n)
    (hblock : ∀ i : Fin t, (𝒜 i).Nonempty → ∃ j k : Fin t, j ≠ i ∧ k ≠ i ∧
      ∃ y : Fin n, ({x, y} : Finset (Fin n)) ∈ 𝒜 j ∧ ({x, y} : Finset (Fin n))ᶜ ∈ 𝒜 k) :
    ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 2 := by
  open Finset in
  classical
  let U := univ.biUnion 𝒜
  have hdisj : ∀ i j : Fin t, i ≠ j → Disjoint (𝒜 i) (𝒜 j) := by
    intro i j hij
    rw [disjoint_left]
    intro S hSi hSj
    exact hinc i j hij S hSi S hSj (Subset.refl S)
  have hsum : U.card = ∑ i, (𝒜 i).card := by
    dsimp [U]
    rw [card_biUnion (fun i _ j _ hij => hdisj i j hij)]
  have hempty : (∅ : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, k, hji, hki, y, hw, hc⟩ := hblock i ⟨∅, hi⟩
    exact hinc i j hji.symm ∅ hi {x, y} hw (empty_subset _)
  have huniv : (univ : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, k, hji, hki, y, hw, hc⟩ := hblock i ⟨univ, hi⟩
    exact hinc j i hji {x, y} hw univ hi (subset_univ _)
  have hx : ({x} : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, k, hji, hki, y, hw, hc⟩ := hblock i ⟨{x}, hi⟩
    have hsub : ({x} : Finset (Fin n)) ⊆ {x, y} := by simp
    exact hinc i j hji.symm {x} hi {x, y} hw hsub
  have hV : (univ.erase x : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, k, hji, hki, y, hw, hc⟩ := hblock i ⟨univ.erase x, hi⟩
    have hsub : ({x, y} : Finset (Fin n))ᶜ ⊆ univ.erase x := by
      intro z hz
      rw [mem_erase]
      refine ⟨?_, mem_univ _⟩
      intro hzx
      subst z
      exact (mem_compl.mp hz) (by simp)
    exact hinc k i hki ({x,y} : Finset (Fin n))ᶜ hc (univ.erase x) hi hsub
  have hno : ∀ S ∈ U, x ∉ S → insert x S ∉ U := by
    intro S hS hxS hSx
    obtain ⟨i, _, hSi⟩ := mem_biUnion.mp hS
    obtain ⟨i', _, hSxi⟩ := mem_biUnion.mp hSx
    have heq : i = i' := by
      by_contra hne
      exact hinc i i' hne S hSi (insert x S) hSxi (subset_insert x S)
    subst i'
    obtain ⟨j, k, hji, hki, y, hw, hc⟩ := hblock i ⟨S, hSi⟩
    have hy : y ∉ S := by
      intro hyS
      have hsub : ({x,y} : Finset (Fin n)) ⊆ insert x S := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem hyS
      exact hinc j i hji {x,y} hw (insert x S) hSxi hsub
    have hsub : S ⊆ ({x,y} : Finset (Fin n))ᶜ := by
      intro z hz
      rw [mem_compl]
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun hzx => hxS (hzx ▸ hz), fun hzy => hy (hzy ▸ hz)⟩
    exact hinc i k hki.symm S hSi ({x,y} : Finset (Fin n))ᶜ hc hsub
  have hover : ((U.filter (fun S => x ∉ S)) ∩
      ((U.filter (fun S => x ∈ S)).image (fun S => S.erase x))).card = 0 := by
    apply card_eq_zero.mpr
    rw [eq_empty_iff_forall_notMem]
    intro S hS
    obtain ⟨hP, hQ⟩ := mem_inter.mp hS
    have hSU : S ∈ U := (mem_filter.mp hP).1
    have hxS : x ∉ S := (mem_filter.mp hP).2
    obtain ⟨T, hT, hTS⟩ := mem_image.mp hQ
    have hTU : T ∈ U := (mem_filter.mp hT).1
    have hxT : x ∈ T := (mem_filter.mp hT).2
    have hTeq : T = insert x S := by
      have he := insert_erase hxT
      rw [hTS] at he
      exact he.symm
    exact hno S hSU hxS (hTeq ▸ hTU)
  have h := op1370_zero_fiber_count n hn U x hempty hx hV huniv hover
  rwa [hsum] at h
