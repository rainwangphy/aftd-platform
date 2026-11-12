import AFTD.Prelude

/-!
# prioritized_borel_finite_history_shadow

Topic: automata   Node: 9e266de9cca8

Provenance: helper lemma. arXiv:2611.10136, Sections 5.2.1-5.2.4; finite-history shadowing along a fixed branch

Let P be a prefix-closed predicate on finite lists over a finite alphabet. If P has a list of every finite length, then there is an infinite sequence all of whose finite prefixes satisfy P.
-/

theorem prioritized_borel_finite_history_shadow (A : Type) [Fintype A] (P : List A → Prop) (hprefix : ∀ xs ys, P (xs ++ ys) → P xs) (hdepth : ∀ n, ∃ xs : List A, xs.length = n ∧ P xs) : ∃ f : ℕ → A, ∀ n, P (List.ofFn (fun i : Fin n => f i)) := by
  classical
  let H (n : ℕ) := { f : Fin n → A // P (List.ofFn f) }
  have hn : ∀ n, Nonempty (H n) := by
    intro n
    obtain ⟨xs, hlen, hp⟩ := hdepth n
    subst n
    exact ⟨⟨xs.get, by simpa using hp⟩⟩
  letI : ∀ n, Nonempty (H n) := hn
  let π : {i j : ℕ} → i ≤ j → H j → H i := fun {i j} hij x =>
    ⟨Fin.take i hij x.1, by
      rw [Fin.ofFn_take_eq_take_ofFn]
      apply hprefix _ ((List.ofFn x.1).drop i)
      simpa using x.2⟩
  have hrefl : ∀ ⦃i⦄ (a : H i), π rfl.le a = a := by
    intro i a
    apply Subtype.ext
    exact Fin.take_eq_self a.1
  have htrans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a,
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intro i j k hij hjk a
    apply Subtype.ext
    exact Fin.take_take hij hjk a.1
  have hfin : ∀ i a, {b : H (i+1) | π (Nat.le_add_right i 1) b = a}.Finite := by
    intro i a
    exact Set.toFinite _
  obtain ⟨seq, hseq⟩ := exists_seq_forall_proj_of_forall_finite π hrefl htrans hfin
  let f : ℕ → A := fun n => (seq (n+1)).1 ⟨n, Nat.lt_succ_self n⟩
  refine ⟨f, ?_⟩
  intro n
  have heq : (fun i : Fin n => f i) = (seq n).1 := by
    funext i
    have h := congrFun (congrArg Subtype.val (hseq (Nat.succ_le_iff.mpr i.isLt)))
      (⟨i.val, Nat.lt_succ_self i.val⟩ : Fin (i.val+1))
    simpa [f, π, Fin.take] using h.symm
  rw [heq]
  exact (seq n).2
