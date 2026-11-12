import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkMajorityGrowth
import AFTD.Kb.Tcs.PrioritizedBorelForkValid

/-!
# prioritized_borel_fork_exponential_histories

Topic: automata   Node: 1998b8c4d3e7

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

For every history-dependent excursion response and every n, some common n-block output has at least (3/2)^n compatible hidden histories.
-/

theorem prioritized_borel_fork_exponential_histories (color : List Bool → List Bool → Bool) (n : ℕ) :
    ∃ u : List Bool, ∃ S : Finset (List Bool),
      u.length = n ∧ n + 1 ≤ S.card ∧ 3 ^ n ≤ 2 ^ n * S.card ∧
      ∀ h ∈ S, PrioritizedBorelForkValid color u h := by
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
      refine ⟨[], {[]}, by simp, by simp, by simp, ?_⟩
      intro h hh
      simp only [Finset.mem_singleton] at hh
      subst h
      exact PrioritizedBorelForkValid.root
  | succ n ih =>
      obtain ⟨u, S, hlen, hlinear, hgrowth, hvalid⟩ := ih
      obtain ⟨bit, hb⟩ := prioritized_borel_fork_majority_growth S
        (fun h => h ++ [false]) (fun h => h ++ [true]) hs he hdiff (color u)
      let T := (S.image (fun h => h ++ [false])) ∪
        ((S.filter fun h => color u h = bit).image (fun h => h ++ [true]))
      refine ⟨u ++ [bit], T, by simp [hlen], ?_, ?_, ?_⟩
      · have hm : 3 * S.card ≤ 2 * T.card := hb
        omega
      · have hm : 3 * S.card ≤ 2 * T.card := hb
        calc
          3 ^ (n+1) = 3 * 3 ^ n := by simp [pow_succ, Nat.mul_comm]
          _ ≤ 3 * (2 ^ n * S.card) := Nat.mul_le_mul_left 3 hgrowth
          _ = 2 ^ n * (3 * S.card) := by ring
          _ ≤ 2 ^ n * (2 * T.card) := Nat.mul_le_mul_left _ hm
          _ = 2 ^ (n+1) * T.card := by ring
      · intro h hh
        rcases Finset.mem_union.mp hh with hs' | he'
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs'
          exact PrioritizedBorelForkValid.stay bit (hvalid a ha)
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he'
          obtain ⟨haS, hcolor⟩ := Finset.mem_filter.mp ha
          simpa [hcolor] using (PrioritizedBorelForkValid.exit (hvalid a haS))
