import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2BoolComp
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# op75_tm2_empty_comp

Topic: np_completeness   Node: 85e6d50d7cb1

Provenance: helper lemma. OP-75: the empty-intermediate-alphabet case of machine composition

Polynomial-time finite stack machines compose when their intermediate alphabet is empty, for arbitrary input and output alphabets.
-/

open Turing Turing.TM2

namespace Op75EmptyComposition

variable {Γ₀ Γ₁ Γ₂ : Type} [IsEmpty Γ₁]
variable {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂}
variable (A : Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f)
variable (B : Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g)

abbrev Stacks := Sum A.tm.K B.tm.K
abbrev Labels := Sum A.tm.Λ B.tm.Λ
abbrev State := A.tm.σ × B.tm.σ
abbrev Alphabet : Stacks A B → Type := Sum.elim A.tm.Γ B.tm.Γ

def liftFirst : Turing.TM2.Stmt A.tm.Γ A.tm.Λ A.tm.σ →
    Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B)
  | .push k h q => .push (.inl k) (fun v => h v.1) (liftFirst q)
  | .peek k h q => .peek (.inl k) (fun v x => (h v.1 x, v.2)) (liftFirst q)
  | .pop k h q => .pop (.inl k) (fun v x => (h v.1 x, v.2)) (liftFirst q)
  | .load h q => .load (fun v => (h v.1, v.2)) (liftFirst q)
  | .branch h q r => .branch (fun v => h v.1) (liftFirst q) (liftFirst r)
  | .goto h => .goto (fun v => .inl (h v.1))
  | .halt => .goto (fun _ => .inr B.tm.main)

def liftSecond : Turing.TM2.Stmt B.tm.Γ B.tm.Λ B.tm.σ →
    Turing.TM2.Stmt (Alphabet A B) (Labels A B) (State A B)
  | .push k h q => .push (.inr k) (fun v => h v.2) (liftSecond q)
  | .peek k h q => .peek (.inr k) (fun v x => (v.1, h v.2 x)) (liftSecond q)
  | .pop k h q => .pop (.inr k) (fun v x => (v.1, h v.2 x)) (liftSecond q)
  | .load h q => .load (fun v => (v.1, h v.2)) (liftSecond q)
  | .branch h q r => .branch (fun v => h v.2) (liftSecond q) (liftSecond r)
  | .goto h => .goto (fun v => .inr (h v.2))
  | .halt => .halt

noncomputable def machine : Turing.FinTM2 := by
  letI : DecidableEq A.tm.K := A.tm.kDecidableEq
  letI : DecidableEq B.tm.K := B.tm.kDecidableEq
  letI : Fintype A.tm.K := A.tm.kFin
  letI : Fintype B.tm.K := B.tm.kFin
  letI : Fintype A.tm.Λ := A.tm.ΛFin
  letI : Fintype B.tm.Λ := B.tm.ΛFin
  letI : Fintype A.tm.σ := A.tm.σFin
  letI : Fintype B.tm.σ := B.tm.σFin
  letI : Fintype (Alphabet A B (.inl A.tm.k₀)) := A.tm.Γk₀Fin
  exact {
    K := Stacks A B
    k₀ := .inl A.tm.k₀
    k₁ := .inr B.tm.k₁
    Γ := Alphabet A B
    Λ := Labels A B
    main := .inl A.tm.main
    σ := State A B
    initialState := (A.tm.initialState, B.tm.initialState)
    m := fun l => match l with
      | .inl a => liftFirst A B (A.tm.m a)
      | .inr b => liftSecond A B (B.tm.m b) }

def firstStacks (S : ∀ k, List (A.tm.Γ k)) : ∀ k, List (Alphabet A B k)
  | .inl k => S k
  | .inr _ => []

theorem firstStacks_update (S : ∀ k, List (A.tm.Γ k)) (k : A.tm.K) (xs : List (A.tm.Γ k)) :
    firstStacks A B (Function.update S k xs) = Function.update (firstStacks A B S) (.inl k) xs := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j; simp [Function.update, firstStacks] <;> rfl
      · simp [Function.update, firstStacks, h] <;> rfl
  | inr j => simp [Function.update, firstStacks]

def firstCfg (v : A.tm.σ) (S : ∀ k, List (A.tm.Γ k)) (l : Option A.tm.Λ) :
    (machine A B).Cfg where
  l := match l with
    | some x => some (.inl x)
    | none => some (.inr B.tm.main)
  var := (v, B.tm.initialState)
  stk := firstStacks A B S

theorem liftFirst_stepAux (q : Turing.TM2.Stmt A.tm.Γ A.tm.Λ A.tm.σ)
    (v : A.tm.σ) (S : ∀ k, List (A.tm.Γ k)) :
    Turing.TM2.stepAux (liftFirst A B q) (v, B.tm.initialState) (firstStacks A B S) =
      firstCfg A B (Turing.TM2.stepAux q v S).var (Turing.TM2.stepAux q v S).stk
        (Turing.TM2.stepAux q v S).l := by
  classical
  induction q generalizing v S with
  | push k h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux]
      have hh := ih v (Function.update S k (h v :: S k))
      simp only [firstStacks_update] at hh
      convert hh using 1 <;> rfl
  | peek k h q ih => simp only [liftFirst, Turing.TM2.stepAux, firstStacks]; exact ih _ _
  | pop k h q ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks]
      have hh := ih (h v (S k).head?) (Function.update S k (S k).tail)
      simp only [firstStacks_update] at hh
      exact hh
  | load h q ih => simp only [liftFirst, Turing.TM2.stepAux]; exact ih _ _
  | branch h q r ihq ihr =>
      simp only [liftFirst, Turing.TM2.stepAux]
      cases hv : h v <;> simp only [hv, Bool.false_eq_true, cond_false, cond_true] <;> first | exact ihq v S | exact ihr v S
  | goto h => rfl
  | halt => rfl

def secondStacks (S : ∀ k, List (B.tm.Γ k)) : ∀ k, List (Alphabet A B k)
  | .inl _ => []
  | .inr k => S k

theorem secondStacks_update (S : ∀ k, List (B.tm.Γ k)) (k : B.tm.K) (xs : List (B.tm.Γ k)) :
    secondStacks A B (Function.update S k xs) = Function.update (secondStacks A B S) (.inr k) xs := by
  classical
  funext j
  cases j with
  | inl j => simp [Function.update, secondStacks]
  | inr j =>
      by_cases h : j = k
      · subst j; simp [Function.update, secondStacks] <;> rfl
      · simp [Function.update, secondStacks, h] <;> rfl

def secondCfg (v : B.tm.σ) (S : ∀ k, List (B.tm.Γ k)) (l : Option B.tm.Λ) :
    (machine A B).Cfg where
  l := l.map Sum.inr
  var := (A.tm.initialState, v)
  stk := secondStacks A B S

theorem liftSecond_stepAux (q : Turing.TM2.Stmt B.tm.Γ B.tm.Λ B.tm.σ)
    (v : B.tm.σ) (S : ∀ k, List (B.tm.Γ k)) :
    Turing.TM2.stepAux (liftSecond A B q) (A.tm.initialState, v) (secondStacks A B S) =
      secondCfg A B (Turing.TM2.stepAux q v S).var (Turing.TM2.stepAux q v S).stk
        (Turing.TM2.stepAux q v S).l := by
  classical
  induction q generalizing v S with
  | push k h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux]
      have hh := ih v (Function.update S k (h v :: S k))
      simp only [secondStacks_update] at hh
      convert hh using 1 <;> rfl
  | peek k h q ih => simp only [liftSecond, Turing.TM2.stepAux, secondStacks]; exact ih _ _
  | pop k h q ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks]
      have hh := ih (h v (S k).head?) (Function.update S k (S k).tail)
      simp only [secondStacks_update] at hh
      exact hh
  | load h q ih => simp only [liftSecond, Turing.TM2.stepAux]; exact ih _ _
  | branch h q r ihq ihr =>
      simp only [liftSecond, Turing.TM2.stepAux]
      cases hv : h v <;> simp only [hv, Bool.false_eq_true, cond_false, cond_true] <;> first | exact ihq v S | exact ihr v S
  | goto h => rfl
  | halt => rfl

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
      change some (Turing.TM2.stepAux (liftFirst A B (A.tm.m l)) _ _) = _
      exact congrArg some (liftFirst_stepAux A B (A.tm.m l) v S)

theorem packSecond_step (c d : B.tm.Cfg) (h : B.tm.step c = some d) :
    (machine A B).step (packSecond A B c) = some (packSecond A B d) := by
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
      change some (Turing.TM2.stepAux (B.tm.m l) v S) = some d at h
      cases Option.some.inj h
      change some (Turing.TM2.stepAux (liftSecond A B (B.tm.m l)) _ _) = _
      exact congrArg some (liftSecond_stepAux A B (B.tm.m l) v S)

theorem packFirst_init (xs : List (A.tm.Γ A.tm.k₀)) :
    packFirst A B (Turing.initList A.tm xs) = Turing.initList (machine A B) xs := by
  classical
  simp [packFirst, firstCfg, firstStacks, Turing.initList, machine]
  congr 1
  funext k
  cases k with
  | inl k => by_cases h : k = A.tm.k₀ <;> simp [firstStacks, Turing.initList, h] <;> rfl
  | inr k => simp [firstStacks, Turing.initList]

theorem empty_transition :
    packFirst A B (Turing.haltList A.tm []) = packSecond A B (Turing.initList B.tm []) := by
  classical
  simp [packFirst, packSecond, firstCfg, secondCfg, firstStacks, secondStacks,
    Turing.haltList, Turing.initList]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases h : k = A.tm.k₁
      · subst k; simp [firstStacks, secondStacks, Turing.haltList, Turing.initList]
      · simp [firstStacks, secondStacks, Turing.haltList, Turing.initList, h]
  | inr k =>
      by_cases h : k = B.tm.k₀
      · subst k; simp [firstStacks, secondStacks, Turing.haltList, Turing.initList]
      · simp [firstStacks, secondStacks, Turing.haltList, Turing.initList, h]

theorem packSecond_halt (zs : List (B.tm.Γ B.tm.k₁)) :
    packSecond A B (Turing.haltList B.tm zs) = Turing.haltList (machine A B) zs := by
  classical
  simp [packSecond, secondCfg, secondStacks, Turing.haltList, machine]
  congr 1
  funext k
  cases k with
  | inl k => simp [secondStacks, Turing.haltList]
  | inr k => by_cases h : k = B.tm.k₁ <;> simp [secondStacks, Turing.haltList, h] <;> rfl

theorem output_nil (a : List Γ₀) : f a = [] := by
  cases h : f a with
  | nil => rfl
  | cons x xs => exact isEmptyElim x

noncomputable def composed_run (a : List Γ₀) :
    Turing.TM2OutputsInTime (machine A B) (a.map A.inputAlphabet.invFun)
      (some ((g (f a)).map B.outputAlphabet.invFun))
      ((B.outputsFun (f a)).steps + (A.outputsFun a).steps) := by
  let u := a.map A.inputAlphabet.invFun
  let w := (g (f a)).map B.outputAlphabet.invFun
  have hA := Op75BoolComposition.iter_simulation A.tm.step (machine A B).step (packFirst A B)
    (packFirst_step A B) (A.outputsFun a).steps (Turing.initList A.tm u)
    (Turing.haltList A.tm ((f a).map A.outputAlphabet.invFun)) (A.outputsFun a).evals_in_steps
  simp only [output_nil (f := f) a, List.map_nil] at hA
  rw [packFirst_init, empty_transition] at hA
  have hB := Op75BoolComposition.iter_simulation B.tm.step (machine A B).step (packSecond A B)
    (packSecond_step A B) (B.outputsFun (f a)).steps
    (Turing.initList B.tm ((f a).map B.inputAlphabet.invFun)) (Turing.haltList B.tm w)
    (B.outputsFun (f a)).evals_in_steps
  simp only [output_nil (f := f) a, List.map_nil] at hB
  rw [packSecond_halt] at hB
  refine ⟨⟨(B.outputsFun (f a)).steps + (A.outputsFun a).steps, ?_⟩, le_rfl⟩
  change (fun x : Option (machine A B).Cfg => x.bind (machine A B).step)^[_]
    (some (Turing.initList (machine A B) u)) = some (Turing.haltList (machine A B) w)
  rw [Function.iterate_add_apply, hA, hB]

noncomputable def composePoly : Turing.TM2ComputableInPolyTime
    (id : List Γ₀ → List Γ₀) (id : List Γ₂ → List Γ₂) (g ∘ f) := by
  classical
  refine { tm := machine A B
           inputAlphabet := A.inputAlphabet
           outputAlphabet := B.outputAlphabet
           time := A.time + Polynomial.C (B.time.eval 0)
           outputsFun := ?_ }
  intro a
  let run := composed_run A B a
  refine ⟨run.toEvalsTo, ?_⟩
  have hA := (A.outputsFun a).steps_le_m
  have hB := (B.outputsFun (f a)).steps_le_m
  have hflen : (f a).length = 0 := by rw [output_nil (f := f) a]; rfl
  simp only [id_eq, hflen] at hA hB
  simp only [Polynomial.eval_add, Polynomial.eval_C, id_eq]
  change (B.outputsFun (f a)).steps + (A.outputsFun a).steps ≤
    A.time.eval a.length + B.time.eval 0
  omega

end Op75EmptyComposition

theorem op75_tm2_empty_comp {Γ₀ Γ₁ Γ₂ : Type} [IsEmpty Γ₁] {f : List Γ₀ → List Γ₁} {g : List Γ₁ → List Γ₂} :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₁ → List Γ₁) f) →
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) g) →
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Γ₀ → List Γ₀) (id : List Γ₂ → List Γ₂) (g ∘ f)) := by
  rintro ⟨A⟩ ⟨B⟩
  exact ⟨Op75EmptyComposition.composePoly A B⟩
