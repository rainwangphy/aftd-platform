import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FactorPath

/-!
# op874_factor_path_cyclic_index_transfer

Topic: graphs   Node: 084ec8d8e14e

Provenance: helper lemma. List-to-cyclic-index transfer for the OP-874 single-defect reduction.

A proper bounded factor path covering the successive nondefect demands, with compatible closing color and an interior occurrence of the specified color, yields the corresponding cyclic factor-edge word with the prescribed boundary colors.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

def PathForward : Nat → List (Fin 4) → List Nat → Nat → Prop
  | b, [], [], last => last = b
  | b, d :: ds, c :: cs, last =>
      c < 4 ∧ c ≠ b ∧ (d.val = b ∨ d.val = c) ∧ PathForward c ds cs last
  | _, _, _, _ => False

theorem forward_append (b last c : Nat) (ds : List (Fin 4)) (cs : List Nat)
    (h : PathForward b ds cs last) (d : Fin 4) (hc : c < 4)
    (hproper : c ≠ last) (hd : d.val = last ∨ d.val = c) :
    PathForward b (ds ++ [d]) (cs ++ [c]) c := by
  induction ds generalizing b cs with
  | nil =>
    cases cs with
    | nil =>
      simp only [PathForward] at h
      simp only [List.nil_append, PathForward]
      subst last
      exact ⟨hc, hproper, hd, trivial⟩
    | cons x xs => simp [PathForward] at h
  | cons x xs ih =>
    cases cs with
    | nil => simp [PathForward] at h
    | cons y ys =>
      rcases h with ⟨hy, hyb, hxy, hrest⟩
      simp only [List.cons_append, PathForward]
      exact ⟨hy, hyb, hxy, ih y ys hrest⟩

theorem factor_path_forward {b last : Nat} {ds : List (Fin 4)} {cs : List Nat}
    (h : FactorPath b ds cs last) : PathForward b ds cs last := by
  induction h with
  | base => rfl
  | @extend ds cs prev path d c hproper hbound hd ih =>
    exact forward_append _ _ _ ds cs ih d hbound hproper hd

theorem forward_length {b last : Nat} {ds : List (Fin 4)} {cs : List Nat}
    (h : PathForward b ds cs last) : ds.length = cs.length := by
  induction ds generalizing b cs with
  | nil => cases cs <;> simp_all [PathForward]
  | cons d ds ih =>
    cases cs with
    | nil => simp [PathForward] at h
    | cons c cs =>
      simp only [PathForward] at h
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih h.2.2.2)

theorem forward_colors_bounded {b last : Nat} {ds : List (Fin 4)} {cs : List Nat}
    (h : PathForward b ds cs last) : ∀ c ∈ cs, c < 4 := by
  induction ds generalizing b cs with
  | nil => cases cs <;> simp_all [PathForward]
  | cons d ds ih =>
    cases cs with
    | nil => simp [PathForward] at h
    | cons c cs =>
      rcases h with ⟨hc, _, _, ht⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hc
      · exact ih ht x hx
end In1051Cert
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1051Cert

theorem forward_index {b last : Nat} {ds : List (Fin 4)} {cs : List Nat}
    (h : PathForward b ds cs last) (i : Nat) (d : Fin 4) (hget : ds[i]? = some d) :
    ∃ prev curr, (b :: cs)[i]? = some prev ∧ cs[i]? = some curr ∧
      curr < 4 ∧ curr ≠ prev ∧ (d.val = prev ∨ d.val = curr) := by
  induction ds generalizing b cs i with
  | nil => simp at hget
  | cons x xs ih =>
    cases cs with
    | nil => simp [PathForward] at h
    | cons y ys =>
      rcases h with ⟨hy, hyb, hxy, ht⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst d
        exact ⟨b, y, rfl, rfl, hy, hyb, hxy⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hget
        obtain ⟨prev, curr, hp, hc, hbnd, hneq, hd⟩ := ih ht i hget
        exact ⟨prev, curr, by simpa using hp, by simpa using hc, hbnd, hneq, hd⟩

theorem forward_last {b last : Nat} {ds : List (Fin 4)} {cs : List Nat}
    (h : PathForward b ds cs last) : (b :: cs)[ds.length]? = some last := by
  induction ds generalizing b cs with
  | nil =>
    cases cs with
    | nil => simpa [PathForward] using h.symm
    | cons c cs => simp [PathForward] at h
  | cons d ds ih =>
    cases cs with
    | nil => simp [PathForward] at h
    | cons c cs =>
      rcases h with ⟨_, _, _, ht⟩
      simpa using ih ht
end In1051Cert
open In1051Cert

theorem op874_factor_path_cyclic_index_transfer
  (n : ℕ) [NeZero n] (hn : 3 ≤ n) (d : Fin n → Fin 4)
    (a b u : Fin 4) (last firstC : ℕ) (rest : List ℕ)
    (hab : a ≠ b) (hlast : last < 4) (hlastneq : last ≠ a.val)
    (hfirst : firstC ≠ a.val) (hu : u.val ∈ firstC :: rest)
    (hpath : op874_factor_path b.val (List.ofFn fun i : Fin (n-2) => d (Fin.ofNat n (i.val+1)))
      (firstC :: rest) last)
    (hfinal : (d (-1)).val = last ∨ d (-1) = a) : ∃ c : Fin n → Fin 4,
      c (-1) = a ∧ c 0 = b ∧
      (∀ i, c (i-1) ≠ c i) ∧
      (∀ i, i ≠ 0 → d i = c (i-1) ∨ d i = c i) ∧
      c 1 ≠ a ∧ (∃ i, i ≠ 0 ∧ i+1 ≠ 0 ∧ c i = u) := by
  let ds : List (Fin 4) := List.ofFn fun i : Fin (n-2) => d (Fin.ofNat n (i.val+1))
  let cs : List ℕ := firstC :: rest
  have hforw : PathForward b.val ds cs last := factor_path_forward hpath
  have hds : ds.length = n-2 := by simp [ds]
  have hcs : cs.length = n-2 := by have h := forward_length hforw; omega
  have hbnd : ∀ x ∈ cs, x < 4 := forward_colors_bounded hforw
  let word : List ℕ := (b.val :: cs) ++ [a.val]
  have hword : word.length = n := by simp [word, hcs]; omega
  have hword_bnd : ∀ x ∈ word, x < 4 := by
    intro x hx
    simp only [word, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | h) | rfl
    · exact b.isLt
    · exact hbnd x h
    · exact a.isLt
  let c : Fin n → Fin 4 := fun i => by
    have hi : i.val < word.length := by simpa [hword] using i.isLt
    exact ⟨word[i.val], hword_bnd _ (List.getElem_mem hi)⟩
  have hcget (i : Fin n) : word[i.val]? = some (c i).val := by
    have hi : i.val < word.length := by simpa [hword] using i.isLt
    simpa [c] using (List.getElem?_eq_getElem hi)
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hneg : (-1 : Fin n).val = n-1 := by
    rw [Fin.val_neg', hone, Nat.mod_eq_of_lt (by omega)]
  have hc0 : c 0 = b := by
    apply Fin.ext
    have h := hcget 0
    simpa [word] using h.symm
  have hclast : c (-1) = a := by
    apply Fin.ext
    have hget : word[(n-2)+1]? = some a.val := by
      dsimp only [word]
      rw [List.getElem?_append_right (by simp [hcs] <;> omega)]
      simp [hcs]
    have h := hcget (-1)
    rw [hneg] at h
    have hnidx : n-1 = (n-2)+1 := by omega
    rw [hnidx, hget] at h
    exact (Option.some.inj h).symm
  have hcfirst : c 1 ≠ a := by
    intro heq
    have hv := congrArg Fin.val heq
    have h := hcget 1
    rw [hone] at h
    have hget : word[1]? = some firstC := by simp [word, cs]
    rw [hget] at h
    have : (c 1).val = firstC := (Option.some.inj h).symm
    exact hfirst (this.symm.trans hv)
  have hsub (i : Fin n) (hi : i ≠ 0) : (i-1).val = i.val-1 := by
    have hi0 : 0 < i.val := by
      by_contra h
      apply hi
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    rw [Fin.val_sub, hone]
    have heq : n - 1 + i.val = (i.val-1) + n := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hlastprev : word[n-2]? = some last := by
    dsimp only [word]
    rw [List.getElem?_append_left (by simp [hcs] <;> omega)]
    simpa [hds] using forward_last hforw
  have hlastne (i : Fin n) (hi : i.val = n-1) : i = -1 := by
    apply Fin.ext
    simpa [hneg] using hi
  have hstep (i : Fin n) (hi : i ≠ 0) :
      c (i-1) ≠ c i ∧ (d i = c (i-1) ∨ d i = c i) := by
    have hi0 : 0 < i.val := by
      by_contra h
      apply hi
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    by_cases hlastidx : i.val = n-1
    · have hieq : i = -1 := hlastne i hlastidx
      subst i
      have hpre : (c ((-1 : Fin n)-1)).val = last := by
        have hh := hcget ((-1 : Fin n)-1)
        rw [hsub _ (by intro h; have := congrArg Fin.val h; simp [hneg] at this; omega), hneg] at hh
        have heq : n - 1 - 1 = n-2 := by omega
        rw [heq, hlastprev] at hh
        exact (Option.some.inj hh).symm
      constructor
      · intro heq
        apply hlastneq
        have hv := congrArg Fin.val heq
        rw [hpre, hclast] at hv
        exact hv
      · rcases hfinal with h | h
        · left; apply Fin.ext; simpa [hpre] using h
        · right; simpa [hclast] using h
    · let j : Nat := i.val-1
      have hj : j < ds.length := by dsimp [j]; rw [hds]; have := i.isLt; omega
      have hdget : ds[j]? = some (d i) := by
        rw [List.getElem?_eq_getElem hj]
        simp only [ds, List.getElem_ofFn]
        have heq : Fin.ofNat n (j+1) = i := by
          apply Fin.ext
          simp only [Fin.val_ofNat]
          rw [Nat.mod_eq_of_lt (by dsimp [j]; have := i.isLt; omega)]
          dsimp [j]
          omega
        exact congrArg some (congrArg d heq)
      obtain ⟨prev, curr, hp, hc, hbnd', hne, hdem⟩ := forward_index hforw j (d i) hdget
      have hprevWord : word[j]? = some prev := by
        dsimp only [word]
        rw [List.getElem?_append_left (by simp [hcs]; dsimp [j]; have := i.isLt; omega)]
        exact hp
      have hcurrWord : word[j+1]? = some curr := by
        dsimp only [word]
        rw [List.getElem?_append_left (by simp [hcs]; dsimp [j]; have := i.isLt; omega)]
        simpa using hc
      have hpre : (c (i-1)).val = prev := by
        have h := hcget (i-1)
        rw [hsub i hi] at h
        change word[j]? = some (c (i-1)).val at h
        rw [hprevWord] at h
        exact (Option.some.inj h).symm
      have hcur : (c i).val = curr := by
        have h := hcget i
        have heq : i.val = j+1 := by dsimp [j]; omega
        rw [heq, hcurrWord] at h
        exact (Option.some.inj h).symm
      constructor
      · intro heq
        apply hne
        have hv := congrArg Fin.val heq
        rw [hpre, hcur] at hv
        exact hv.symm
      · rcases hdem with h | h
        · left; apply Fin.ext; simpa [hpre] using h
        · right; apply Fin.ext; simpa [hcur] using h
  refine ⟨c, hclast, hc0, ?_, ?_, hcfirst, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simpa [hclast, hc0] using hab
    · exact (hstep i hi).1
  · intro i hi
    exact (hstep i hi).2
  · obtain ⟨j, hj, huj⟩ := List.mem_iff_getElem.mp hu
    have hj' : j < cs.length := by simpa [cs] using hj
    have hjn : j+1 < n := by rw [hcs] at hj'; omega
    let i : Fin n := ⟨j+1, hjn⟩
    have hi0 : i ≠ 0 := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [i] at hh
      omega
    have hip : i+1 ≠ 0 := by
      intro h
      have hh := congrArg Fin.val h
      rw [Fin.val_add, hone] at hh
      have hlt : i.val + 1 < n := by dsimp [i]; rw [hcs] at hj'; omega
      rw [Nat.mod_eq_of_lt hlt] at hh
      simp only [Fin.val_zero] at hh
      omega
    refine ⟨i, hi0, hip, ?_⟩
    apply Fin.ext
    have hg : word[j+1]? = some u.val := by
      dsimp only [word]
      rw [List.getElem?_append_left (by simp [hcs] <;> omega)]
      simp only [List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem hj']
      simpa [cs] using congrArg some huj
    have h := hcget i
    change word[j+1]? = some (c i).val at h
    rw [hg] at h
    exact (Option.some.inj h).symm
