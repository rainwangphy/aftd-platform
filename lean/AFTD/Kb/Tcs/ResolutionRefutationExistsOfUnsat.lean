import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionRefutation
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.IsResolutionDerivation

/-!
# resolution_refutation_exists_of_unsat

Topic: proof_complexity   Node: 7a2bf7068dfd

Provenance: formalization of a published result. Source: standard textbook result (proof complexity): refutational completeness of resolution, as recalled in arXiv:2610.02047, Sec. 3.1

Completeness of resolution, the length-free part of the problem: every unsatisfiable CNF formula has a resolution refutation.
-/

/-- The variable of a literal. -/
def resolution_lit_var {V : Type*} : CnfLit V → V
  | CnfLit.pos v => v
  | CnfLit.neg v => v


/-- One step of a resolution derivation, for a sequence indexed by `ℕ`. -/
def resolution_step_at {V : Type*} (F : Finset (Finset (CnfLit V)))
    (f : ℕ → Finset (CnfLit V)) (i : ℕ) : Prop :=
  f i ∈ F ∨ (∃ j < i, f j ⊆ f i) ∨
  (∃ j < i, ∃ k < i, ∃ (x : V) (C D : Finset (CnfLit V)),
    (∀ l, l ∈ f j ↔ l ∈ C ∨ l = CnfLit.pos x) ∧ (∀ l, l ∈ f k ↔ l ∈ D ∨ l = CnfLit.neg x) ∧
    (∀ l, l ∈ f i ↔ l ∈ C ∨ l ∈ D))

theorem resolution_step_at_transport {V : Type*} {F : Finset (Finset (CnfLit V))}
    {f g : ℕ → Finset (CnfLit V)} {i : ℕ} (σ : ℕ → ℕ) (hσ : ∀ j < i, σ j < σ i)
    (hg : ∀ j ≤ i, g (σ j) = f j) (h : resolution_step_at F f i) :
    resolution_step_at F g (σ i) := by
  rcases h with h | ⟨j, hj, h⟩ | ⟨j, hj, k, hk, x, C, D, h1, h2, h3⟩
  · left; rw [hg i le_rfl]; exact h
  · right; left; exact ⟨σ j, hσ j hj, by rw [hg j hj.le, hg i le_rfl]; exact h⟩
  · right; right
    refine ⟨σ j, hσ j hj, σ k, hσ k hk, x, C, D, ?_, ?_, ?_⟩
    · rw [hg j hj.le]; exact h1
    · rw [hg k hk.le]; exact h2
    · rw [hg i le_rfl]; exact h3

/-- The sequence of a list, padded with the empty clause. -/
def resolution_seq {V : Type*} (π : List (Finset (CnfLit V))) (k : ℕ) : Finset (CnfLit V) :=
  (π[k]?).getD ∅

theorem resolution_seq_of_lt {V : Type*} (π : List (Finset (CnfLit V))) {k : ℕ}
    (hk : k < π.length) : resolution_seq π k = π[k] := by
  simp [resolution_seq, List.getElem?_eq_getElem hk]

theorem is_resolution_derivation_of_steps {V : Type*} (F : Finset (Finset (CnfLit V)))
    (π : List (Finset (CnfLit V)))
    (h : ∀ i < π.length, resolution_step_at F (resolution_seq π) i) :
    is_resolution_derivation F π := by
  intro i
  have hi := i.isLt
  rcases h i.val hi with h | ⟨j, hj, h⟩ | ⟨j, hj, k, hk, x, C, D, h1, h2, h3⟩
  · left; rw [resolution_seq_of_lt π hi] at h; simpa using h
  · right; left
    refine ⟨⟨j, by omega⟩, by simp [Fin.lt_def, hj], ?_⟩
    rw [resolution_seq_of_lt π hi, resolution_seq_of_lt π (by omega)] at h
    simpa using h
  · right; right
    refine ⟨⟨j, by omega⟩, ⟨k, by omega⟩, by simp [Fin.lt_def, hj], by simp [Fin.lt_def, hk],
      x, C, D, ?_, ?_, ?_⟩
    · rw [resolution_seq_of_lt π (by omega)] at h1; simpa using h1
    · rw [resolution_seq_of_lt π (by omega)] at h2; simpa using h2
    · rw [resolution_seq_of_lt π hi] at h3; simpa using h3

/-- Tree-like resolution derivability. -/
inductive ResolutionDerivable {V : Type*} (F : Finset (Finset (CnfLit V))) :
    Finset (CnfLit V) → Prop
  | ax {C : Finset (CnfLit V)} : C ∈ F → ResolutionDerivable F C
  | weak {C E : Finset (CnfLit V)} : ResolutionDerivable F C → C ⊆ E → ResolutionDerivable F E
  | res {x : V} {A B C D E : Finset (CnfLit V)} : ResolutionDerivable F A →
      ResolutionDerivable F B → (∀ l, l ∈ A ↔ l ∈ C ∨ l = CnfLit.pos x) →
      (∀ l, l ∈ B ↔ l ∈ D ∨ l = CnfLit.neg x) → (∀ l, l ∈ E ↔ l ∈ C ∨ l ∈ D) →
      ResolutionDerivable F E

theorem resolution_seq_append_left {V : Type*} (π ρ : List (Finset (CnfLit V))) {k : ℕ}
    (hk : k < π.length) : resolution_seq (π ++ ρ) k = resolution_seq π k := by
  simp [resolution_seq, List.getElem?_append_left hk]

theorem resolution_seq_append_right {V : Type*} (π ρ : List (Finset (CnfLit V))) (k : ℕ) :
    resolution_seq (π ++ ρ) (k + π.length) = resolution_seq ρ k := by
  simp [resolution_seq, List.getElem?_append_right (Nat.le_add_left _ _)]

/-- Steps of `π` stay steps of `π ++ ρ`. -/
theorem resolution_steps_append_left {V : Type*} (F : Finset (Finset (CnfLit V)))
    (π ρ : List (Finset (CnfLit V)))
    (h : ∀ i < π.length, resolution_step_at F (resolution_seq π) i) :
    ∀ i < π.length, resolution_step_at F (resolution_seq (π ++ ρ)) i := by
  intro i hi
  exact resolution_step_at_transport id (fun j hj => hj)
    (fun j hj => by simp only [id]; exact resolution_seq_append_left π ρ (by omega)) (h i hi)

/-- Steps of `ρ` become steps of `π ++ ρ`, shifted by `π.length`. -/
theorem resolution_steps_append_right {V : Type*} (F : Finset (Finset (CnfLit V)))
    (π ρ : List (Finset (CnfLit V)))
    (h : ∀ i < ρ.length, resolution_step_at F (resolution_seq ρ) i) :
    ∀ i < ρ.length, resolution_step_at F (resolution_seq (π ++ ρ)) (i + π.length) := by
  intro i hi
  exact resolution_step_at_transport (· + π.length) (fun j hj => by show j + π.length < i + π.length; omega)
    (fun j _ => resolution_seq_append_right π ρ j) (h i hi)

theorem resolution_derivable_seq {V : Type*} {F : Finset (Finset (CnfLit V))}
    {E : Finset (CnfLit V)} (h : ResolutionDerivable F E) :
    ∃ π : List (Finset (CnfLit V)), ∃ n, π.length = n + 1 ∧ resolution_seq π n = E ∧
      ∀ i < π.length, resolution_step_at F (resolution_seq π) i := by
  induction h with
  | @ax C hC =>
    refine ⟨[C], 0, rfl, by simp [resolution_seq], ?_⟩
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    left; simpa [resolution_seq] using hC
  | @weak C E _ hCE ih =>
    obtain ⟨π, n, hlen, hlast, hsteps⟩ := ih
    refine ⟨π ++ [E], n + 1, by simp [hlen], ?_, ?_⟩
    · have := resolution_seq_append_right π [E] 0
      rw [show n + 1 = 0 + π.length by omega, this]; simp [resolution_seq]
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hin : i < π.length
      · exact resolution_steps_append_left F π [E] hsteps i hin
      · have hi' : i = n + 1 := by omega
        subst hi'
        right; left
        refine ⟨n, by omega, ?_⟩
        rw [resolution_seq_append_left π [E] (by omega), hlast]
        have := resolution_seq_append_right π [E] 0
        rw [show 0 + π.length = n + 1 by omega] at this
        rw [this]; simpa [resolution_seq] using hCE
  | @res x A B C D E _ _ hA hB hE ihA ihB =>
    obtain ⟨π, n, hlen, hlast, hsteps⟩ := ihA
    obtain ⟨ρ, m, hlen', hlast', hsteps'⟩ := ihB
    refine ⟨π ++ ρ ++ [E], n + m + 2, by simp [hlen, hlen']; omega, ?_, ?_⟩
    · have := resolution_seq_append_right (π ++ ρ) [E] 0
      rw [show n + m + 2 = 0 + (π ++ ρ).length by simp; omega, this]; simp [resolution_seq]
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases h1 : i < π.length
      · have := resolution_steps_append_left F π ρ hsteps i h1
        exact resolution_steps_append_left F (π ++ ρ) [E] (fun i hi => by
          by_cases h1' : i < π.length
          · exact resolution_steps_append_left F π ρ hsteps i h1'
          · have := resolution_steps_append_right F π ρ hsteps' (i - π.length)
              (by simp at hi; omega)
            rwa [Nat.sub_add_cancel (by omega)] at this) i (by simp; omega)
      · by_cases h2 : i < π.length + ρ.length
        · have := resolution_steps_append_right F π ρ hsteps' (i - π.length) (by omega)
          rw [Nat.sub_add_cancel (by omega)] at this
          exact resolution_steps_append_left F (π ++ ρ) [E] (fun i hi => by
            by_cases h1' : i < π.length
            · exact resolution_steps_append_left F π ρ hsteps i h1'
            · have := resolution_steps_append_right F π ρ hsteps' (i - π.length)
                (by simp at hi; omega)
              rwa [Nat.sub_add_cancel (by omega)] at this) i (by simp; omega)
        · have hi' : i = n + m + 2 := by omega
          subst hi'
          right; right
          refine ⟨n, by omega, n + 1 + m, by omega, x, C, D, ?_, ?_, ?_⟩
          · rw [resolution_seq_append_left _ _ (by simp; omega),
              resolution_seq_append_left _ _ (by omega), hlast]
            exact hA
          · rw [resolution_seq_append_left _ _ (by simp; omega)]
            have := resolution_seq_append_right π ρ m
            rw [show m + π.length = n + 1 + m by omega] at this
            rw [this, hlast']
            exact hB
          · have := resolution_seq_append_right (π ++ ρ) [E] 0
            rw [show 0 + (π ++ ρ).length = n + m + 2 by simp; omega] at this
            rw [this]; simpa [resolution_seq] using hE

/-- A literal is true under an assignment. -/
def resolution_lit_true {V : Type*} (τ : V → Bool) : CnfLit V → Prop
  | CnfLit.pos v => τ v = true
  | CnfLit.neg v => τ v = false

theorem resolution_derivable_of_unsat {V : Type*} [DecidableEq V]
    (F : Finset (Finset (CnfLit V)))
    (hF : ∀ τ : V → Bool, ∃ C ∈ F, ∀ l ∈ C, ¬ resolution_lit_true τ l) :
    ∀ (X : Finset V) (K : Finset (CnfLit V)), (∀ v, ¬ (CnfLit.pos v ∈ K ∧ CnfLit.neg v ∈ K)) →
      (∀ C ∈ F, ∀ l ∈ C, resolution_lit_var l ∈ X ∨ CnfLit.pos (resolution_lit_var l) ∈ K ∨
        CnfLit.neg (resolution_lit_var l) ∈ K) →
      ResolutionDerivable F K := by
  classical
  intro X
  induction X using Finset.induction_on with
  | empty =>
    intro K hK hvars
    obtain ⟨C, hCF, hC⟩ := hF (fun v => if CnfLit.pos v ∈ K then false else true)
    refine ResolutionDerivable.weak (ResolutionDerivable.ax hCF) ?_
    intro l hl
    have hfalse := hC l hl
    rcases hvars C hCF l hl with h | h | h
    · simp at h
    · cases l with
      | pos v =>
        simp only [resolution_lit_var] at h; exact h
      | neg v =>
        simp only [resolution_lit_var] at h
        exact (hfalse (by simp [resolution_lit_true, h])).elim
    · cases l with
      | pos v =>
        simp only [resolution_lit_var] at h
        by_contra hpos
        exact hfalse (by simp [resolution_lit_true, hpos])
      | neg v =>
        simp only [resolution_lit_var] at h; exact h
  | @insert x X hx ih =>
    intro K hK hvars
    by_cases hxK : CnfLit.pos x ∈ K ∨ CnfLit.neg x ∈ K
    · apply ih K hK
      intro C hC l hl
      rcases hvars C hC l hl with h | h | h
      · rcases Finset.mem_insert.1 h with h | h
        · rw [h]; exact Or.inr hxK
        · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · push_neg at hxK
      have hsub : ∀ K' : Finset (CnfLit V), K ⊆ K' → (CnfLit.pos x ∈ K' ∨ CnfLit.neg x ∈ K') →
          ∀ C ∈ F, ∀ l ∈ C, resolution_lit_var l ∈ X ∨ CnfLit.pos (resolution_lit_var l) ∈ K' ∨
            CnfLit.neg (resolution_lit_var l) ∈ K' := by
        intro K' hKK' hx' C hC l hl
        rcases hvars C hC l hl with h | h | h
        · rcases Finset.mem_insert.1 h with h | h
          · rw [h]; exact Or.inr hx'
          · exact Or.inl h
        · exact Or.inr (Or.inl (hKK' h))
        · exact Or.inr (Or.inr (hKK' h))
      have h1 := ih (insert (CnfLit.pos x) K) (by
          intro v ⟨hp, hn⟩
          rcases Finset.mem_insert.1 hp with hp | hp <;> rcases Finset.mem_insert.1 hn with hn | hn
          · cases hn
          · cases hp; exact hxK.2 hn
          · cases hn
          · exact hK v ⟨hp, hn⟩)
        (hsub _ (Finset.subset_insert _ _) (Or.inl (Finset.mem_insert_self _ _)))
      have h2 := ih (insert (CnfLit.neg x) K) (by
          intro v ⟨hp, hn⟩
          rcases Finset.mem_insert.1 hp with hp | hp <;> rcases Finset.mem_insert.1 hn with hn | hn
          · cases hp
          · cases hp
          · cases hn; exact hxK.1 hp
          · exact hK v ⟨hp, hn⟩)
        (hsub _ (Finset.subset_insert _ _) (Or.inr (Finset.mem_insert_self _ _)))
      exact ResolutionDerivable.res (x := x) (C := K) (D := K) h1 h2
        (fun l => by simp [Finset.mem_insert, or_comm]) (fun l => by simp [Finset.mem_insert, or_comm])
        (fun l => by simp)

theorem resolution_refutation_exists_of_unsat (F : Finset (Finset (CnfLit ℕ))) (h : ¬ CnfSatisfiable (F.toList.map Finset.toList)) : ∃ π, is_resolution_refutation F π := by
  classical
  have hF : ∀ τ : ℕ → Bool, ∃ C ∈ F, ∀ l ∈ C, ¬ resolution_lit_true τ l := by
    intro τ
    by_contra hne
    push_neg at hne
    apply h
    refine ⟨τ, ?_⟩
    intro c hc
    simp only [List.mem_map, Finset.mem_toList] at hc
    obtain ⟨C, hC, rfl⟩ := hc
    obtain ⟨l, hl, hlt⟩ := hne C hC
    refine ⟨l, by simpa using hl, ?_⟩
    cases l <;> simpa [resolution_lit_true] using hlt
  have hder := resolution_derivable_of_unsat F hF (F.biUnion fun C => C.image resolution_lit_var) ∅
    (by simp) (fun C hC l hl => Or.inl (Finset.mem_biUnion.2 ⟨C, hC, Finset.mem_image_of_mem _ hl⟩))
  obtain ⟨π, n, hlen, hlast, hsteps⟩ := resolution_derivable_seq hder
  refine ⟨π, is_resolution_derivation_of_steps F π hsteps, ?_⟩
  have hn : n < π.length := by omega
  rw [resolution_seq_of_lt π hn] at hlast
  rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel, List.getElem?_eq_getElem hn, hlast]
