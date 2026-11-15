import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2PolyOutputSize
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# op75_tm2_inhabited_comp

Topic: np_completeness   Node: 514720b6268a

Provenance: helper lemma. OP-75: generalization of op75_tm2_bool_comp to inhabited finite intermediate alphabets

Polynomial-time finite stack machines compose whenever their intermediate alphabet is inhabited; the input and output alphabets are arbitrary.
-/

open Turing Turing.TM2

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

abbrev Stacks := Sum A.tm.K (Sum B.tm.K Unit)
abbrev Labels := Sum A.tm.Λ (Sum B.tm.Λ Bool)
abbrev State := A.tm.σ × B.tm.σ × Option Γ₁

abbrev Alphabet : Stacks A B → Type
  | .inl k => A.tm.Γ k
  | .inr (.inl k) => B.tm.Γ k
  | .inr (.inr _) => Γ₁

def liftFirst : Turing.TM2.Stmt A.tm.Γ A.tm.Λ A.tm.σ →
    Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B)
  | .push k h q => .push (.inl k) (fun v => h v.1) (liftFirst q)
  | .peek k h q => .peek (.inl k) (fun v x => (h v.1 x, v.2)) (liftFirst q)
  | .pop k h q => .pop (.inl k) (fun v x => (h v.1 x, v.2)) (liftFirst q)
  | .load h q => .load (fun v => (h v.1, v.2)) (liftFirst q)
  | .branch h q r => .branch (fun v => h v.1) (liftFirst q) (liftFirst r)
  | .goto h => .goto (fun v => .inl (h v.1))
  | .halt => .goto (fun _ => .inr (.inr false))

def liftSecond : Turing.TM2.Stmt B.tm.Γ B.tm.Λ B.tm.σ →
    Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B)
  | .push k h q => .push (.inr (.inl k)) (fun v => h v.2.1) (liftSecond q)
  | .peek k h q => .peek (.inr (.inl k)) (fun v x => (v.1, h v.2.1 x, v.2.2)) (liftSecond q)
  | .pop k h q => .pop (.inr (.inl k)) (fun v x => (v.1, h v.2.1 x, v.2.2)) (liftSecond q)
  | .load h q => .load (fun v => (v.1, h v.2.1, v.2.2)) (liftSecond q)
  | .branch h q r => .branch (fun v => h v.2.1) (liftSecond q) (liftSecond r)
  | .goto h => .goto (fun v => .inr (.inl (h v.2.1)))
  | .halt => .halt

def copyFirst : Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B) :=
  .pop (.inl A.tm.k₁) (fun v x => (v.1, v.2.1, x.map A.outputAlphabet))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inr ())) (fun v => v.2.2.getD default) (.goto (fun _ => .inr (.inr false))))
      (.goto (fun _ => .inr (.inr true))))

def copySecond : Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B) :=
  .pop (.inr (.inr ())) (fun v x => (v.1, v.2.1, x))
    (.branch (fun v => v.2.2.isSome)
      (.push (.inr (.inl B.tm.k₀)) (fun v => B.inputAlphabet.invFun (v.2.2.getD default))
        (.goto (fun _ => .inr (.inr true))))
      (.goto (fun _ => .inr (.inl B.tm.main))))

noncomputable def machine : Turing.FinTM2 := by
  letI : DecidableEq A.tm.K := A.tm.kDecidableEq
  letI : DecidableEq B.tm.K := B.tm.kDecidableEq
  letI : Fintype A.tm.K := A.tm.kFin
  letI : Fintype B.tm.K := B.tm.kFin
  letI : Fintype A.tm.Λ := A.tm.ΛFin
  letI : Fintype B.tm.Λ := B.tm.ΛFin
  letI : Fintype (B.tm.Γ B.tm.k₀) := B.tm.Γk₀Fin
  letI : Fintype Γ₁ := Fintype.ofEquiv (B.tm.Γ B.tm.k₀) B.inputAlphabet
  letI : Fintype A.tm.σ := A.tm.σFin
  letI : Fintype B.tm.σ := B.tm.σFin
  letI : Fintype (Alphabet A B (.inl A.tm.k₀)) := A.tm.Γk₀Fin
  exact {
    K := Stacks A B
    k₀ := .inl A.tm.k₀
    k₁ := .inr (.inl B.tm.k₁)
    Γ := Alphabet A B
    Λ := Labels A B
    main := .inl A.tm.main
    σ := State A B
    initialState := (A.tm.initialState, B.tm.initialState, none)
    m := fun l => match l with
      | .inl a => liftFirst A B (A.tm.m a)
      | .inr (.inl b) => liftSecond A B (B.tm.m b)
      | .inr (.inr false) => copyFirst A B
      | .inr (.inr true) => copySecond A B }

end Op75GeneralComposition

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

def firstStacks (S : ∀ k, List (A.tm.Γ k)) : ∀ k, List (Alphabet A B k)
  | .inl k => S k
  | .inr _ => []

theorem firstStacks_update (S : ∀ k, List (A.tm.Γ k)) (k : A.tm.K) (xs : List (A.tm.Γ k)) :
    firstStacks A B (Function.update S k xs) =
      Function.update (firstStacks A B S) (.inl k) xs := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j
        simp [Function.update, firstStacks] <;> rfl
      · simp [Function.update, firstStacks, h] <;> rfl
  | inr j => simp [Function.update, firstStacks]

def firstCfg (v : A.tm.σ) (S : ∀ k, List (A.tm.Γ k)) (l : Option A.tm.Λ) :
    (machine A B).Cfg where
  l := match l with
    | some x => some (.inl x)
    | none => some (.inr (.inr false))
  var := (v, B.tm.initialState, none)
  stk := firstStacks A B S

theorem liftFirst_stepAux (q : Turing.TM2.Stmt A.tm.Γ A.tm.Λ A.tm.σ)
    (v : A.tm.σ) (S : ∀ k, List (A.tm.Γ k)) :
    Turing.TM2.stepAux (liftFirst A B q) (v, B.tm.initialState, none) (firstStacks A B S) =
      firstCfg A B (Turing.TM2.stepAux q v S).var (Turing.TM2.stepAux q v S).stk
        (Turing.TM2.stepAux q v S).l := by
  classical
  induction q generalizing v S with
  | push k h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux]
      have hh := ih v (Function.update S k (h v :: S k))
      simp only [firstStacks_update] at hh
      convert hh using 1 <;> rfl
  | peek k h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks]
      exact ih _ _
  | pop k h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks]
      have hh := ih (h v (S k).head?) (Function.update S k (S k).tail)
      simp only [firstStacks_update] at hh
      exact hh
  | load h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux]
      exact ih _ _
  | branch h q r ihq ihr =>
      simp only [liftFirst, Turing.TM2.stepAux]
      cases hv : h v <;> simp only [hv, Bool.false_eq_true, cond_false, cond_true] <;> first | exact ihq v S | exact ihr v S
  | goto h => rfl
  | halt => rfl

end Op75GeneralComposition

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

def secondStacks (S : ∀ k, List (B.tm.Γ k)) : ∀ k, List (Alphabet A B k)
  | .inl _ => []
  | .inr (.inl k) => S k
  | .inr (.inr _) => []

theorem secondStacks_update (S : ∀ k, List (B.tm.Γ k)) (k : B.tm.K) (xs : List (B.tm.Γ k)) :
    secondStacks A B (Function.update S k xs) =
      Function.update (secondStacks A B S) (.inr (.inl k)) xs := by
  classical
  funext j
  cases j with
  | inl j => simp [Function.update, secondStacks]
  | inr j =>
      cases j with
      | inl j =>
          by_cases h : j = k
          · subst j
            simp [Function.update, secondStacks] <;> rfl
          · simp [Function.update, secondStacks, h] <;> rfl
      | inr j => simp [Function.update, secondStacks]

def secondCfg (v : B.tm.σ) (S : ∀ k, List (B.tm.Γ k)) (l : Option B.tm.Λ) :
    (machine A B).Cfg where
  l := l.map (fun x => .inr (.inl x))
  var := (A.tm.initialState, v, none)
  stk := secondStacks A B S

theorem liftSecond_stepAux (q : Turing.TM2.Stmt B.tm.Γ B.tm.Λ B.tm.σ)
    (v : B.tm.σ) (S : ∀ k, List (B.tm.Γ k)) :
    Turing.TM2.stepAux (liftSecond A B q) (A.tm.initialState, v, none) (secondStacks A B S) =
      secondCfg A B (Turing.TM2.stepAux q v S).var (Turing.TM2.stepAux q v S).stk
        (Turing.TM2.stepAux q v S).l := by
  classical
  induction q generalizing v S with
  | push k h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux]
      have hh := ih v (Function.update S k (h v :: S k))
      simp only [secondStacks_update] at hh
      convert hh using 1 <;> rfl
  | peek k h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks]
      exact ih _ _
  | pop k h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks]
      have hh := ih (h v (S k).head?) (Function.update S k (S k).tail)
      simp only [secondStacks_update] at hh
      exact hh
  | load h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux]
      exact ih _ _
  | branch h q r ihq ihr =>
      simp only [liftSecond, Turing.TM2.stepAux]
      cases hv : h v <;> simp only [hv, Bool.false_eq_true, cond_false, cond_true] <;> first | exact ihq v S | exact ihr v S
  | goto h => rfl
  | halt => rfl

end Op75GeneralComposition

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

theorem firstMachine_step (l : A.tm.Λ) (v : A.tm.σ) (S : ∀ k, List (A.tm.Γ k)) :
    (machine A B).step (firstCfg A B v S (some l)) =
      some (firstCfg A B (Turing.TM2.stepAux (A.tm.m l) v S).var
        (Turing.TM2.stepAux (A.tm.m l) v S).stk (Turing.TM2.stepAux (A.tm.m l) v S).l) := by
  change some (Turing.TM2.stepAux (liftFirst A B (A.tm.m l)) _ _) = _
  rw [liftFirst_stepAux]
  rfl

theorem secondMachine_step (l : B.tm.Λ) (v : B.tm.σ) (S : ∀ k, List (B.tm.Γ k)) :
    (machine A B).step (secondCfg A B v S (some l)) =
      some (secondCfg A B (Turing.TM2.stepAux (B.tm.m l) v S).var
        (Turing.TM2.stepAux (B.tm.m l) v S).stk (Turing.TM2.stepAux (B.tm.m l) v S).l) := by
  change some (Turing.TM2.stepAux (liftSecond A B (B.tm.m l)) _ _) = _
  rw [liftSecond_stepAux]
  rfl

end Op75GeneralComposition

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

def packFirst (c : A.tm.Cfg) := firstCfg A B c.var c.stk c.l
def packSecond (c : B.tm.Cfg) := secondCfg A B c.var c.stk c.l

theorem packFirst_step (c d : A.tm.Cfg) (h : A.tm.step c = some d) :
    (machine A B).step (packFirst A B c) = some (packFirst A B d) := by
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
      change some (Turing.TM2.stepAux (A.tm.m l) v S) = some d at h
      cases Option.some.inj h
      exact firstMachine_step A B l v S

theorem packSecond_step (c d : B.tm.Cfg) (h : B.tm.step c = some d) :
    (machine A B).step (packSecond A B c) = some (packSecond A B d) := by
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
      change some (Turing.TM2.stepAux (B.tm.m l) v S) = some d at h
      cases Option.some.inj h
      exact secondMachine_step A B l v S

theorem iter_simulation {α β : Type} (f : α → Option α) (g : β → Option β) (e : α → β)
    (hs : ∀ c d, f c = some d → g (e c) = some (e d)) (n : ℕ) (c d : α)
    (h : (fun x : Option α => x.bind f)^[n] (some c) = some d) :
    (fun x : Option β => x.bind g)^[n] (some (e c)) = some (e d) := by
  induction n generalizing d with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at h ⊢
      cases hm : (fun x : Option α => x.bind f)^[n] (some c) with
      | none => simp [hm] at h
      | some m =>
          have he := ih m hm
          simp only [he, Option.bind_some]
          exact hs m d (by simpa [hm] using h)

end Op75GeneralComposition

namespace Op75GeneralComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

noncomputable def transferStacks (xs : List (A.tm.Γ A.tm.k₁)) (ys : List Γ₁)
    (zs : List (B.tm.Γ B.tm.k₀)) : ∀ k, List (Alphabet A B k) := by
  classical
  intro k
  cases k with
  | inl k =>
      exact if h : k = A.tm.k₁ then (by subst k; exact xs) else []
  | inr k =>
      cases k with
      | inl k => exact if h : k = B.tm.k₀ then (by subst k; exact zs) else []
      | inr _ => exact ys

noncomputable def transferCfg (phase : Bool) (x : Option Γ₁)
    (xs : List (A.tm.Γ A.tm.k₁)) (ys : List Γ₁) (zs : List (B.tm.Γ B.tm.k₀)) :
    (machine A B).Cfg where
  l := some (.inr (.inr phase))
  var := (A.tm.initialState, B.tm.initialState, x)
  stk := transferStacks A B xs ys zs

theorem transferFirst_aux (a : A.tm.Γ A.tm.k₁) (xs : List (A.tm.Γ A.tm.k₁))
    (ys : List Γ₁) (x : Option Γ₁) :
    Turing.TM2.stepAux (copyFirst A B) (A.tm.initialState, B.tm.initialState, x)
      (transferStacks A B (a :: xs) ys []) =
      ⟨some (.inr (.inr false)), (A.tm.initialState, B.tm.initialState, some (A.outputAlphabet a)),
        transferStacks A B xs (A.outputAlphabet a :: ys) []⟩ := by
  classical
  simp [copyFirst, Turing.TM2.stepAux, transferStacks, Function.update]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases h : k = A.tm.k₁
      · subst k
        simp [transferStacks, Function.update]
      · simp [transferStacks, Function.update, h]
  | inr k => cases k with
    | inl k => by_cases h : k = B.tm.k₀ <;> simp [transferStacks, Function.update, h] <;> rfl
    | inr k => cases k <;> simp [transferStacks, Function.update] <;> rfl


theorem transferFirst_nil (ys : List Γ₁) (x : Option Γ₁) :
    Turing.TM2.stepAux (copyFirst A B) (A.tm.initialState, B.tm.initialState, x)
      (transferStacks A B [] ys []) =
      ⟨some (.inr (.inr true)), (A.tm.initialState, B.tm.initialState, none),
        transferStacks A B [] ys []⟩ := by
  classical
  simp [copyFirst, Turing.TM2.stepAux, transferStacks, Function.update]

theorem transferSecond_aux (b : Γ₁) (ys : List Γ₁) (zs : List (B.tm.Γ B.tm.k₀)) (x : Option Γ₁) :
    Turing.TM2.stepAux (copySecond A B) (A.tm.initialState, B.tm.initialState, x)
      (transferStacks A B [] (b :: ys) zs) =
      ⟨some (.inr (.inr true)), (A.tm.initialState, B.tm.initialState, some b),
        transferStacks A B [] ys (B.inputAlphabet.invFun b :: zs)⟩ := by
  classical
  simp [copySecond, Turing.TM2.stepAux, transferStacks, Function.update]
  congr 1
  funext k
  cases k with
  | inl k => by_cases h : k = A.tm.k₁ <;> simp [transferStacks, Function.update, h]
  | inr k => cases k with
    | inl k =>
        by_cases h : k = B.tm.k₀
        · subst k
          simp [transferStacks, Function.update]
        · simp [transferStacks, Function.update, h]
    | inr k => cases k <;> simp [transferStacks, Function.update]

theorem transferSecond_nil (zs : List (B.tm.Γ B.tm.k₀)) (x : Option Γ₁) :
    Turing.TM2.stepAux (copySecond A B) (A.tm.initialState, B.tm.initialState, x)
      (transferStacks A B [] [] zs) =
      ⟨some (.inr (.inl B.tm.main)), (A.tm.initialState, B.tm.initialState, none),
        transferStacks A B [] [] zs⟩ := by
  classical
  simp [copySecond, Turing.TM2.stepAux, transferStacks, Function.update]


theorem transferFirst_step (a : A.tm.Γ A.tm.k₁) (xs : List (A.tm.Γ A.tm.k₁))
    (ys : List Γ₁) (x : Option Γ₁) :
    (machine A B).step (transferCfg A B false x (a :: xs) ys []) =
      some (transferCfg A B false (some (A.outputAlphabet a)) xs (A.outputAlphabet a :: ys) []) := by
  change some (Turing.TM2.stepAux (copyFirst A B) _ _) = _
  exact congrArg some (transferFirst_aux A B a xs ys x)

theorem transferFirst_finish (ys : List Γ₁) (x : Option Γ₁) :
    (machine A B).step (transferCfg A B false x [] ys []) =
      some (transferCfg A B true none [] ys []) := by
  change some (Turing.TM2.stepAux (copyFirst A B) _ _) = _
  exact congrArg some (transferFirst_nil A B ys x)

theorem transferSecond_step (b : Γ₁) (ys : List Γ₁) (zs : List (B.tm.Γ B.tm.k₀)) (x : Option Γ₁) :
    (machine A B).step (transferCfg A B true x [] (b :: ys) zs) =
      some (transferCfg A B true (some b) [] ys (B.inputAlphabet.invFun b :: zs)) := by
  change some (Turing.TM2.stepAux (copySecond A B) _ _) = _
  exact congrArg some (transferSecond_aux A B b ys zs x)

theorem transferSecond_finish (zs : List (B.tm.Γ B.tm.k₀)) (x : Option Γ₁) :
    (machine A B).step (transferCfg A B true x [] [] zs) =
      some ⟨some (.inr (.inl B.tm.main)), (A.tm.initialState, B.tm.initialState, none),
        transferStacks A B [] [] zs⟩ := by
  change some (Turing.TM2.stepAux (copySecond A B) _ _) = _
  exact congrArg some (transferSecond_nil A B zs x)


noncomputable def runStep (c : Option (machine A B).Cfg) : Option (machine A B).Cfg := c.bind (machine A B).step

theorem transferFirst_run (xs : List (A.tm.Γ A.tm.k₁)) (ys : List Γ₁) (x : Option Γ₁) :
    (runStep A B)^[xs.length + 1] (some (transferCfg A B false x xs ys [])) =
      some (transferCfg A B true none [] ((xs.map A.outputAlphabet).reverse ++ ys) []) := by
  induction xs generalizing ys x with
  | nil =>
      change (machine A B).step (transferCfg A B false x [] ys []) = _
      exact transferFirst_finish A B ys x
  | cons a xs ih =>
      change (runStep A B)^[Nat.succ (xs.length + 1)] _ = _
      rw [Function.iterate_succ_apply]
      simp only [runStep, Option.bind_some, transferFirst_step]
      simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (A.outputAlphabet a :: ys) (some (A.outputAlphabet a))

theorem transferSecond_run (ys : List Γ₁) (zs : List (B.tm.Γ B.tm.k₀)) (x : Option Γ₁) :
    (runStep A B)^[ys.length + 1] (some (transferCfg A B true x [] ys zs)) =
      some ⟨some (.inr (.inl B.tm.main)), (A.tm.initialState, B.tm.initialState, none),
        transferStacks A B [] [] ((ys.map B.inputAlphabet.invFun).reverse ++ zs)⟩ := by
  induction ys generalizing zs x with
  | nil =>
      change (machine A B).step (transferCfg A B true x [] [] zs) = _
      exact transferSecond_finish A B zs x
  | cons b ys ih =>
      change (runStep A B)^[Nat.succ (ys.length + 1)] _ = _
      rw [Function.iterate_succ_apply]
      simp only [runStep, Option.bind_some, transferSecond_step]
      simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (B.inputAlphabet.invFun b :: zs) (some b)


theorem packFirst_init (xs : List (A.tm.Γ A.tm.k₀)) :
    packFirst A B (Turing.initList A.tm xs) = Turing.initList (machine A B) xs := by
  classical
  simp [packFirst, firstCfg, firstStacks, Turing.initList, machine]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases h : k = A.tm.k₀
      · subst k
        simp [firstStacks, Turing.initList]
        rfl
      · simp [firstStacks, Turing.initList, h]
  | inr k => simp [firstStacks, Turing.initList]

theorem packFirst_halt (xs : List (A.tm.Γ A.tm.k₁)) :
    packFirst A B (Turing.haltList A.tm xs) = transferCfg A B false none xs [] [] := by
  classical
  simp [packFirst, firstCfg, firstStacks, Turing.haltList, transferCfg, transferStacks]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases h : k = A.tm.k₁
      · subst k
        simp [firstStacks, Turing.haltList, transferStacks]
      · simp [firstStacks, Turing.haltList, transferStacks, h]
  | inr k => cases k with
    | inl k =>
        by_cases h : k = B.tm.k₀
        · subst k
          simp [firstStacks, transferStacks]
        · simp [firstStacks, transferStacks, h]
    | inr k => cases k <;> simp [firstStacks, transferStacks]

theorem packSecond_init (zs : List (B.tm.Γ B.tm.k₀)) :
    packSecond A B (Turing.initList B.tm zs) =
      ⟨some (.inr (.inl B.tm.main)), (A.tm.initialState, B.tm.initialState, none),
        transferStacks A B [] [] zs⟩ := by
  classical
  simp [packSecond, secondCfg, secondStacks, Turing.initList, transferStacks]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases h : k = A.tm.k₁
      · subst k
        simp [secondStacks, Turing.initList, transferStacks]
      · simp [secondStacks, Turing.initList, transferStacks, h]
  | inr k => cases k with
    | inl k =>
        by_cases h : k = B.tm.k₀
        · subst k
          simp [secondStacks, Turing.initList, transferStacks]
        · simp [secondStacks, Turing.initList, transferStacks, h]
    | inr k => cases k <;> simp [secondStacks, Turing.initList, transferStacks]

theorem packSecond_halt (zs : List (B.tm.Γ B.tm.k₁)) :
    packSecond A B (Turing.haltList B.tm zs) = Turing.haltList (machine A B) zs := by
  classical
  simp [packSecond, secondCfg, secondStacks, Turing.haltList, machine]
  congr 1
  funext k
  cases k with
  | inl k => simp [secondStacks, Turing.haltList]
  | inr k => cases k with
    | inl k =>
        by_cases h : k = B.tm.k₁
        · subst k
          simp [secondStacks, Turing.haltList]
          rfl
        · simp [secondStacks, Turing.haltList, h]
    | inr k => cases k <;> simp [secondStacks, Turing.haltList]


theorem transfer_both (xs : List (A.tm.Γ A.tm.k₁)) :
    (runStep A B)^[(xs.length + 1) + (xs.length + 1)]
      (some (transferCfg A B false none xs [] [])) =
      some (packSecond A B (Turing.initList B.tm ((xs.map A.outputAlphabet).map B.inputAlphabet.invFun))) := by
  rw [Function.iterate_add_apply, transferFirst_run]
  have h := transferSecond_run A B ((xs.map A.outputAlphabet).reverse) [] none
  rw [packSecond_init]
  simpa [List.map_reverse, List.reverse_reverse] using h


noncomputable def composed_run (a : List Γ₀) :
    Turing.TM2OutputsInTime (machine A B) (a.map A.inputAlphabet.invFun)
      (some ((g (f a)).map B.outputAlphabet.invFun))
      ((B.outputsFun (f a)).steps + ((f a).length + 1) + ((f a).length + 1) + (A.outputsFun a).steps) := by
  let u := a.map A.inputAlphabet.invFun
  let v := (f a).map A.outputAlphabet.invFun
  let w := (g (f a)).map B.outputAlphabet.invFun
  have hA := iter_simulation A.tm.step (machine A B).step (packFirst A B)
    (packFirst_step A B) (A.outputsFun a).steps (Turing.initList A.tm u) (Turing.haltList A.tm v)
    (A.outputsFun a).evals_in_steps
  rw [packFirst_init, packFirst_halt] at hA
  change (runStep A B)^[(A.outputsFun a).steps] (some (Turing.initList (machine A B) u)) = _ at hA
  have hB := iter_simulation B.tm.step (machine A B).step (packSecond A B)
    (packSecond_step A B) (B.outputsFun (f a)).steps
    (Turing.initList B.tm ((f a).map B.inputAlphabet.invFun)) (Turing.haltList B.tm w)
    (B.outputsFun (f a)).evals_in_steps
  rw [packSecond_halt] at hB
  change (runStep A B)^[(B.outputsFun (f a)).steps] (some (packSecond A B (Turing.initList B.tm ((f a).map B.inputAlphabet.invFun)))) = _ at hB
  have hcopy := transfer_both A B v
  have hconvert : (v.map A.outputAlphabet).map B.inputAlphabet.invFun = (f a).map B.inputAlphabet.invFun := by
    simp [v, List.map_map]
  rw [hconvert] at hcopy
  have hlen : v.length = (f a).length := by simp [v]
  rw [hlen] at hcopy
  refine ⟨⟨(B.outputsFun (f a)).steps + ((f a).length + 1) + ((f a).length + 1) + (A.outputsFun a).steps, ?_⟩, le_rfl⟩
  change (runStep A B)^[_] (some (Turing.initList (machine A B) u)) = some (Turing.haltList (machine A B) w)
  rw [Function.iterate_add_apply, hA, Nat.add_assoc, Function.iterate_add_apply, hcopy, hB]


theorem poly_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      change p.eval a ≤ p.eval b at hp
      change q.eval a ≤ q.eval b at hq
      exact Nat.add_le_add hp hq
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

noncomputable def composePoly : Turing.TM2ComputableInPolyTime
    (id : List Γ₀ → List Γ₀) (id : List Γ₂ → List Γ₂) (g ∘ f) := by
  classical
  let q := Classical.choose (op75_tm2_poly_output_size A)
  have hq : ∀ a, (f a).length ≤ q.eval a.length := Classical.choose_spec (op75_tm2_poly_output_size A)
  refine { tm := machine A B
           inputAlphabet := A.inputAlphabet
           outputAlphabet := B.outputAlphabet
           time := B.time.comp q + (q + 1) + (q + 1) + A.time
           outputsFun := ?_ }
  intro a
  let run := composed_run A B a
  refine ⟨run.toEvalsTo, ?_⟩
  have hA := (A.outputsFun a).steps_le_m
  have hB := (B.outputsFun (f a)).steps_le_m
  have hm := poly_eval_mono B.time (hq a)
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
  change (B.outputsFun (f a)).steps + ((f a).length + 1) + ((f a).length + 1) +
    (A.outputsFun a).steps ≤ B.time.eval (q.eval a.length) + (q.eval a.length + 1) + (q.eval a.length + 1) + A.time.eval a.length
  change B.time.eval (f a).length ≤ B.time.eval (q.eval a.length) at hm
  have hs := hq a
  simp only [id_eq] at hA hB
  omega

end Op75GeneralComposition

theorem op75_tm2_inhabited_comp {Γ₀ Γ₁ Γ₂ : Type} [Inhabited Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂} :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f) →
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g) →
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₂ → List Γ₂) (g ∘ f)) := by
  rintro ⟨A⟩ ⟨B⟩
  exact ⟨Op75GeneralComposition.composePoly A B⟩
