import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkMajorityGrowth

/-!
# prioritized_borel_fork_prefix_chain

Topic: automata   Node: 387b940a6a5c

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For every n, there is a visible n-block word such that every prefix of length k admits at least k+1 compatible hidden histories.
-/

theorem prioritized_borel_fork_prefix_chain (color : List Bool → List Bool → Bool) (n : ℕ) :
    ∃ u : List Bool, u.length = n ∧
      ∀ k ≤ n, ∃ S : Finset (List Bool), k + 1 ≤ S.card ∧
        ∀ h ∈ S, PrioritizedBorelForkValid color (u.take k) h := by
  classical
  have hs : Function.Injective (fun h : List Bool => h ++ [false]) :=
    List.append_left_injective [false]
  have he : Function.Injective (fun h : List Bool => h ++ [true]) :=
    List.append_left_injective [true]
  have hdiff : ∀ a b : List Bool, a ++ [false] ≠ b ++ [true] := by
    intro a b h
    have hh := congrArg List.getLast? h
    simp at hh
  induction n with
  | zero =>
      refine ⟨[], rfl, ?_⟩
      intro k hk
      have : k = 0 := by omega
      subst k
      refine ⟨{[]}, by simp, ?_⟩
      intro h hh
      simp only [Finset.mem_singleton] at hh
      subst h
      simpa using (PrioritizedBorelForkValid.root (color := color))
  | succ n ih =>
      obtain ⟨u, hlen, hchain⟩ := ih
      obtain ⟨S, hsize, hvalid⟩ := hchain n le_rfl
      have hu : u.take n = u := by simp [← hlen]
      rw [hu] at hvalid
      obtain ⟨bit, hb⟩ := prioritized_borel_fork_majority_growth S
        (fun h => h ++ [false]) (fun h => h ++ [true]) hs he hdiff (color u)
      let T := (S.image (fun h => h ++ [false])) ∪
        ((S.filter fun h => color u h = bit).image (fun h => h ++ [true]))
      have ht : n+2 ≤ T.card := by
        have hm : 3 * S.card ≤ 2 * T.card := hb
        omega
      have hv : ∀ h ∈ T, PrioritizedBorelForkValid color (u ++ [bit]) h := by
        intro h hh
        rcases Finset.mem_union.mp hh with hs' | he'
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs'
          exact PrioritizedBorelForkValid.stay bit (hvalid a ha)
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he'
          obtain ⟨haS, hcolor⟩ := Finset.mem_filter.mp ha
          simpa [hcolor] using (PrioritizedBorelForkValid.exit (hvalid a haS))
      refine ⟨u ++ [bit], by simp [hlen], ?_⟩
      intro k hk
      by_cases hkn : k ≤ n
      · obtain ⟨S', hs', hv'⟩ := hchain k hkn
        refine ⟨S', hs', ?_⟩
        have heq : (u ++ [bit]).take k = u.take k := by
          apply List.take_append_of_le_length
          omega
        simpa [heq] using hv'
      · have hk' : k = n+1 := by omega
        subst k
        refine ⟨T, by omega, ?_⟩
        have heq : (u ++ [bit]).take (n+1) = u ++ [bit] := by simp [hlen]
        simpa [heq] using hv
