import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularIffEnfa

/-!
# is_regular_kstar

Topic: automata   Node: e73060300b08

The Kleene star of any regular language is regular.
-/

open Set Computability
open scoped Classical

def is_regular_kstar_enfa {α : Type*} {σ : Type*} (M : εNFA α σ) : εNFA α (Option σ) where
  step
    | none, none => { some s | s ∈ M.start }
    | none, some _ => ∅
    | some s, none => { some t | t ∈ M.step s none } ∪ if s ∈ M.accept then {none} else ∅
    | some s, some a => { some t | t ∈ M.step s (some a) }
  start := {none}
  accept := {none}

lemma is_regular_kstar_isPath_lift {α σ : Type*} (M : εNFA α σ) {s t : σ} {w : List (Option α)}
    (h : M.IsPath s t w) : (is_regular_kstar_enfa M).IsPath (some s) (some t) w := by
  induction h with
  | nil u => exact εNFA.IsPath.nil (some u)
  | cons u v w a rest hstep hpath ih =>
    refine εNFA.IsPath.cons (some u) (some v) (some w) a rest ?_ ih
    cases a with
    | none =>
      left; exact ⟨u, hstep, rfl⟩
    | some a =>
      exact ⟨u, hstep, rfl⟩

lemma is_regular_kstar_start_step {α σ : Type*} (M : εNFA α σ) {s : σ} (hs : s ∈ M.start) :
    (is_regular_kstar_enfa M).IsPath none (some s) [none] := by
  have : some s ∈ (is_regular_kstar_enfa M).step none none := ⟨s, hs, rfl⟩
  exact εNFA.IsPath.cons (some s) none (some s) none [] this (εNFA.IsPath.nil (some s))

lemma is_regular_kstar_accept_step {α σ : Type*} (M : εNFA α σ) {s : σ} (hs : s ∈ M.accept) :
    (is_regular_kstar_enfa M).IsPath (some s) none [none] := by
  have : (none : Option σ) ∈ (is_regular_kstar_enfa M).step (some s) none := by
    right; rw [if_pos hs]; exact Set.mem_singleton none
  exact εNFA.IsPath.cons none (some s) none none [] this (εNFA.IsPath.nil none)

lemma is_regular_kstar_path_of_mem {α σ : Type*} (M : εNFA α σ) {w : List α} (hw : w ∈ M.accepts) :
    ∃ p : List (Option α), p.reduceOption = w ∧ (is_regular_kstar_enfa M).IsPath none none p := by
  rw [εNFA.mem_accepts_iff_exists_path] at hw
  obtain ⟨s₁, s₂, x', hs₁, hs₂, rfl, hpath⟩ := hw
  refine ⟨[none] ++ (x' ++ [none]), ?_, ?_⟩
  · simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · rw [εNFA.isPath_append]
    refine ⟨some s₁, is_regular_kstar_start_step M hs₁, ?_⟩
    rw [εNFA.isPath_append]
    exact ⟨some s₂, is_regular_kstar_isPath_lift M hpath, is_regular_kstar_accept_step M hs₂⟩

lemma is_regular_kstar_path_of_kstar {α σ : Type*} (M : εNFA α σ) {w : List α} (hw : w ∈ (M.accepts)∗) :
    ∃ p : List (Option α), p.reduceOption = w ∧ (is_regular_kstar_enfa M).IsPath none none p := by
  rw [Language.mem_kstar] at hw
  obtain ⟨L, rfl, hL⟩ := hw
  induction L with
  | nil =>
    refine ⟨[], rfl, εNFA.IsPath.nil none⟩
  | cons y ys ih =>
    have hy : y ∈ M.accepts := hL y (by simp)
    obtain ⟨p₁, hp₁, hpath₁⟩ := is_regular_kstar_path_of_mem M hy
    obtain ⟨p₂, hp₂, hpath₂⟩ := ih (fun z hz => hL z (by simp [hz]))
    refine ⟨p₁ ++ p₂, ?_, ?_⟩
    · rw [List.reduceOption_append, hp₁, hp₂, List.flatten_cons]
    · rw [εNFA.isPath_append]
      exact ⟨none, hpath₁, hpath₂⟩

lemma is_regular_kstar_path_some_to_none {α σ : Type*} (M : εNFA α σ) (q : List (Option α)) :
    ∀ (s : σ), (is_regular_kstar_enfa M).IsPath (some s) none q →
      ∃ (q₁ : List (Option α)) (s₂ : σ) (q₂ : List (Option α)),
        q = q₁ ++ none :: q₂ ∧
        M.IsPath s s₂ q₁ ∧
        s₂ ∈ M.accept ∧
        (is_regular_kstar_enfa M).IsPath none none q₂ := by
  induction q with
  | nil =>
    intro s h
    have := h.eq_of_nil
    contradiction
  | cons b q ih =>
    intro s h
    cases h with
    | cons t _ _ _ _ hstep hpath =>
      cases b with
      | none =>
        change t ∈ ({ some u | u ∈ M.step s none } ∪ if s ∈ M.accept then {none} else ∅) at hstep
        rcases hstep with (⟨u, hu, rfl⟩ | ht)
        · obtain ⟨q₁, s₂, q₂, rfl, hM, hs₂, hrest⟩ := ih u hpath
          exact ⟨none :: q₁, s₂, q₂, rfl, εNFA.IsPath.cons u s s₂ none q₁ hu hM, hs₂, hrest⟩
        · split_ifs at ht with hs
          · have : t = none := ht
            subst this
            exact ⟨[], s, q, rfl, εNFA.IsPath.nil s, hs, hpath⟩
          · contradiction
      | some a =>
        change t ∈ { some u | u ∈ M.step s (some a) } at hstep
        obtain ⟨u, hu, rfl⟩ := hstep
        obtain ⟨q₁, s₂, q₂, rfl, hM, hs₂, hrest⟩ := ih u hpath
        exact ⟨some a :: q₁, s₂, q₂, rfl, εNFA.IsPath.cons u s s₂ (some a) q₁ hu hM, hs₂, hrest⟩

lemma is_regular_kstar_path_none_to_none {α σ : Type*} (M : εNFA α σ) (p : List (Option α)) :
    (is_regular_kstar_enfa M).IsPath none none p → p.reduceOption ∈ (M.accepts)∗ := by
  intro h
  induction' hn : p.length using Nat.strong_induction_on with n ih generalizing p
  cases p with
  | nil =>
    simp [Language.nil_mem_kstar]
  | cons a q =>
    cases h with
    | cons t _ _ _ _ hstep hpath =>
      cases a with
      | some a =>
        change t ∈ (∅ : Set (Option σ)) at hstep
        contradiction
      | none =>
        change t ∈ { some s | s ∈ M.start } at hstep
        obtain ⟨s₁, hs₁, rfl⟩ := hstep
        obtain ⟨q₁, s₂, q₂, rfl, hpath₁, hs₂, hpath₂⟩ := is_regular_kstar_path_some_to_none M q s₁ hpath
        have hlen : q₂.length < n := by
          subst hn
          simp; omega
        have ih_q₂ := ih q₂.length hlen q₂ hpath₂ rfl
        have h_q₁ : q₁.reduceOption ∈ M.accepts := by
          rw [εNFA.mem_accepts_iff_exists_path]
          exact ⟨s₁, s₂, q₁, hs₁, hs₂, rfl, hpath₁⟩
        have h_mul : q₁.reduceOption ++ q₂.reduceOption ∈ M.accepts * (M.accepts)∗ :=
          Language.append_mem_mul h_q₁ ih_q₂
        have h_sub : M.accepts * (M.accepts)∗ ≤ (M.accepts)∗ := mul_kstar_le_kstar
        simp [List.reduceOption_cons_of_none, List.reduceOption_append]
        exact h_sub h_mul

lemma is_regular_kstar_accepts {α σ : Type*} (M : εNFA α σ) :
    (is_regular_kstar_enfa M).accepts = (M.accepts)∗ := by
  ext w
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, rfl, hpath⟩
    change s₁ = none at hs₁
    change s₂ = none at hs₂
    subst hs₁ hs₂
    exact is_regular_kstar_path_none_to_none M x' hpath
  · intro hw
    obtain ⟨p, rfl, hpath⟩ := is_regular_kstar_path_of_kstar M hw
    exact ⟨none, none, p, rfl, rfl, rfl, hpath⟩

/-- Regular languages are closed under Kleene star. -/
theorem is_regular_kstar {α : Type*} {L : Language α} (h : L.IsRegular) : (KStar.kstar L).IsRegular := by
  rw [is_regular_iff_enfa] at h ⊢
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨Option σ, inferInstance, is_regular_kstar_enfa M, is_regular_kstar_accepts M⟩
