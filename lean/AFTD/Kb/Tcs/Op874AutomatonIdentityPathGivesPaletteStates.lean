import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonIdentityPath
import AFTD.Kb.Tcs.Op874SeparatedWindowAutomatonAcceptance

/-!
# op874_automaton_identity_path_gives_palette_states

Topic: graphs   Node: a46a825858a7

Provenance: helper lemma. Cyclic-index transfer for the OP-874 separated-defect automaton.

A closed path through the 24 ordered four-color states yields a cyclic sequence of color permutations whose first positions shift along the cycle and whose forced steps use the fourth color.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

theorem path_has_states (start : Fin 24) (fs : List Bool) (finish : Fin 24)
    (hp : path start fs finish) :
    ∃ ss : List (Fin 24),
      ss.length = fs.length + 1 ∧ ss[0]? = some start ∧ ss[fs.length]? = some finish ∧
      ∀ i f, fs[i]? = some f →
        ∃ x y : Fin 24, ss[i]? = some x ∧ ss[i+1]? = some y ∧ transition f x y := by
  induction fs generalizing start with
  | nil =>
    change finish = start at hp
    subst finish
    refine ⟨[start], by simp, rfl, rfl, ?_⟩
    intro i f hf
    simp at hf
  | cons f fs ih =>
    change ∃ mid : Fin 24, transition f start mid ∧ path mid fs finish at hp
    obtain ⟨mid, hstep, hp⟩ := hp
    obtain ⟨ss, hlen, hhead, hlast, hsteps⟩ := ih mid hp
    refine ⟨start :: ss, by simp [hlen], rfl, ?_, ?_⟩
    · simpa using hlast
    · intro i flag hflag
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hflag
        subst flag
        refine ⟨start, mid, rfl, ?_, hstep⟩
        simpa using hhead
      | succ i =>
        simp only [List.getElem?_cons_succ] at hflag
        obtain ⟨x, y, hx, hy, hxy⟩ := hsteps i flag hflag
        exact ⟨x, y, by simpa using hx, by simpa using hy, hxy⟩
end In1081Separated
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Separated

def select (p : Colors) : Fin 4 → Fin 4 := ![p.1, p.2.1, p.2.2.1, p.2.2.2]

theorem color_states_bijective (i : Fin 24) : Function.Bijective (select colorStates[i.val]!) := by
  revert i
  decide

noncomputable def permAt (i : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (select colorStates[i.val]!) (color_states_bijective i)

theorem transition_perm (f : Bool) (i j : Fin 24) (h : transition f i j) :
    permAt j 0 = permAt i 1 ∧ permAt j 1 = permAt i 2 ∧
      (f = true → permAt j 2 = permAt i 3) := by
  rcases h with h4 | ⟨hf, h3⟩
  · have he : colorStates[j.val]! = rotate4 colorStates[i.val]! := by
      rw [h4]
      exact step4_colors i
    constructor
    · change select colorStates[j.val]! 0 = select colorStates[i.val]! 1
      rw [he]; rfl
    constructor
    · change select colorStates[j.val]! 1 = select colorStates[i.val]! 2
      rw [he]; rfl
    · intro _
      change select colorStates[j.val]! 2 = select colorStates[i.val]! 3
      rw [he]; rfl
  · have he : colorStates[j.val]! = rotate3 colorStates[i.val]! := by
      rw [h3]
      exact step3_colors i
    constructor
    · change select colorStates[j.val]! 0 = select colorStates[i.val]! 1
      rw [he]; rfl
    constructor
    · change select colorStates[j.val]! 1 = select colorStates[i.val]! 2
      rw [he]; rfl
    · intro ht
      rw [hf] at ht
      contradiction
end In1081Separated
open In1081Separated

theorem op874_automaton_identity_path_gives_palette_states
    (n : ℕ) [NeZero n] (hn : 6 ≤ n) (flags : Fin n → Bool)
    (hp : path (0 : Fin 24) (List.ofFn flags) (0 : Fin 24)) :
    ∃ s : Fin n → Equiv.Perm (Fin 4),
      ∀ i, s (i+1) 0 = s i 1 ∧ s (i+1) 1 = s i 2 ∧
        (flags i = true → s (i+1) 2 = s i 3) := by
  obtain ⟨ss, hlen, hhead, hlast, hsteps⟩ := path_has_states 0 (List.ofFn flags) 0 hp
  have hlen' : ss.length = n+1 := by simpa using hlen
  let stateAt : Fin n → Fin 24 := fun i => ss[i.val]'(by rw [hlen']; have := i.isLt; omega)
  have hget (i : Fin n) : ss[i.val]? = some (stateAt i) := by
    have hi : i.val < ss.length := by rw [hlen']; have := i.isLt; omega
    simpa [stateAt] using (List.getElem?_eq_getElem hi)
  have hs0 : stateAt 0 = 0 := by
    have h := hget 0
    simpa [hhead] using (Option.some.inj (h.symm.trans hhead))
  have hlast' : ss[n]? = some (0 : Fin 24) := by simpa using hlast
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hgetnext (i : Fin n) : ss[i.val+1]? = some (stateAt (i+1)) := by
    by_cases hi : i.val+1 < n
    · have hval : (i+1).val = i.val+1 := by
        rw [Fin.val_add, hone, Nat.mod_eq_of_lt hi]
      simpa [hval] using hget (i+1)
    · have heq : i.val+1 = n := by have := i.isLt; omega
      have hnext : i+1 = 0 := by
        apply Fin.ext
        rw [Fin.val_add, hone, heq]
        simp
      rw [heq, hlast', hnext, hs0]
  refine ⟨fun i => permAt (stateAt i), ?_⟩
  intro i
  have hflag : (List.ofFn flags)[i.val]? = some (flags i) := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp
  obtain ⟨x, y, hx, hy, ht⟩ := hsteps i.val (flags i) hflag
  have hx' : x = stateAt i := by
    have h := hget i
    rw [hx] at h
    exact Option.some.inj h
  have hy' : y = stateAt (i+1) := by
    have h := hgetnext i
    rw [hy] at h
    exact Option.some.inj h
  subst x; subst y
  exact transition_perm _ _ _ ht
