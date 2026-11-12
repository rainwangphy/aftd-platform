import AFTD.Prelude
import AFTD.Kb.Tcs.G

/-!
# op_193_k3_m10_at_least_85_vertices

Topic: graphs   Node: ace4aeeff548

Provenance: helper lemma. Explicit finite enumeration for OP-193; experiment 23347.

The stable triple graph of the ten-cycle plus an isolated vertex has at least 85 vertices.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
namespace Inbox777M10

instance : DecidableRel (((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)).Adj) := by
  intro a b
  cases a <;> cases b <;> dsimp [SimpleGraph.sum] <;> infer_instance

def verts : Fin 85 → Finset (Fin 10 ⊕ Unit) := ![{Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inl (5 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (2 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (3 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (4 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (5 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (0 : Fin 10), Sum.inl (6 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (0 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (3 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (4 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (5 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (6 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (1 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (1 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (4 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (5 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (6 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (2 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (2 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (5 : Fin 10), Sum.inr ()},
  {Sum.inl (3 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (6 : Fin 10), Sum.inr ()},
  {Sum.inl (3 : Fin 10), Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (3 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (3 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (3 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10)},
  {Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (4 : Fin 10), Sum.inl (6 : Fin 10), Sum.inr ()},
  {Sum.inl (4 : Fin 10), Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (4 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (4 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (4 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10)},
  {Sum.inl (5 : Fin 10), Sum.inl (7 : Fin 10), Sum.inr ()},
  {Sum.inl (5 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (5 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (6 : Fin 10), Sum.inl (8 : Fin 10), Sum.inr ()},
  {Sum.inl (6 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()},
  {Sum.inl (7 : Fin 10), Sum.inl (9 : Fin 10), Sum.inr ()}]

def vertex (i : ℕ) : Finset (Fin 10 ⊕ Unit) :=
  verts ⟨i % 85, Nat.mod_lt _ (by decide)⟩

theorem verts_valid : ∀ i : Fin 85,
    ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)).IsNIndepSet 3 (verts i) := by
  decide

def normalization (a b c d : Fin 6) : Equiv.Perm (Fin 6) :=
  let e0 := Equiv.swap a 0
  let e1 := Equiv.swap (e0 b) 1
  let e2 := Equiv.swap (e1 (e0 c)) 2
  let d' := e2 (e1 (e0 d))
  let e3 := if d' = 2 then Equiv.refl _ else Equiv.swap d' 3
  ((e0.trans e1).trans e2).trans e3

theorem normalization_spec : ∀ a b c d : Fin 6,
    a ≠ b → a ≠ c → b ≠ c → a ≠ d → b ≠ d →
    normalization a b c d a = 0 ∧ normalization a b c d b = 1 ∧
    normalization a b c d c = 2 ∧
    (normalization a b c d d = 2 ∨ normalization a b c d d = 3) := by
  decide

def valuation (c : Fin 85 → Fin 6) : Sat.Valuation :=
  fun n => (c ⟨(n / 6) % 85, Nat.mod_lt _ (by decide)⟩).val = n % 6

def clauseOK (units : List ℕ) : Sat.Clause → Bool
  | [.pos a, .pos b, .pos c, .pos d, .pos e, .pos f] =>
      a % 6 == 0 && b == a+1 && c == a+2 && d == a+3 && e == a+4 && f == a+5
  | [.neg a, .neg b] =>
      a % 6 == b % 6 && decide (Disjoint (vertex (a/6)) (vertex (b/6)))
  | [.pos a] => units.contains a
  | _ => false

theorem clauseOK_sound (c : Fin 85 → Fin 6)
    (hproper : ∀ i j, Disjoint (verts i) (verts j) → c i ≠ c j)
    (units : List ℕ) (hunits : ∀ n ∈ units, valuation c n)
    (cl : Sat.Clause) (h : clauseOK units cl = true) : (valuation c).satisfies cl := by
  rcases cl with _ | ⟨l, rest⟩
  · simp [clauseOK] at h
  rcases rest with _ | ⟨l2, rest⟩
  · cases l with
    | neg a => simp [clauseOK] at h
    | pos a =>
      have hm : a ∈ units := by simpa [clauseOK] using h
      simpa [Sat.Valuation.satisfies, Sat.Valuation.neg] using hunits a hm
  rcases rest with _ | ⟨l3, rest⟩
  · cases l <;> cases l2 <;> simp only [clauseOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.false_eq_true] at h
    next a b =>
      rcases h with ⟨hab, hd⟩
      have hn := hproper ⟨(a/6)%85, Nat.mod_lt _ (by decide)⟩
        ⟨(b/6)%85, Nat.mod_lt _ (by decide)⟩ hd
      intro ha hb
      apply hn
      apply Fin.ext
      dsimp [valuation, Sat.Valuation.neg] at ha hb
      omega
  rcases rest with _ | ⟨l4, rest⟩
  · cases l <;> cases l2 <;> cases l3 <;> simp [clauseOK] at h
  rcases rest with _ | ⟨l5, rest⟩
  · cases l <;> cases l2 <;> cases l3 <;> cases l4 <;> simp [clauseOK] at h
  rcases rest with _ | ⟨l6, rest⟩
  · cases l <;> cases l2 <;> cases l3 <;> cases l4 <;> cases l5 <;> simp [clauseOK] at h
  rcases rest with _ | ⟨l7, rest⟩
  · cases l <;> cases l2 <;> cases l3 <;> cases l4 <;> cases l5 <;> cases l6 <;>
      simp only [clauseOK, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    next a b d e f g =>
      rcases h with ⟨⟨⟨⟨⟨ha, hb⟩, hd⟩, he⟩, hf⟩, hg⟩
      subst b; subst d; subst e; subst f; subst g
      have hdiv1 : (a+1)/6 = a/6 := by omega
      have hdiv2 : (a+2)/6 = a/6 := by omega
      have hdiv3 : (a+3)/6 = a/6 := by omega
      have hdiv4 : (a+4)/6 = a/6 := by omega
      have hdiv5 : (a+5)/6 = a/6 := by omega
      have hmod1 : (a+1)%6 = 1 := by omega
      have hmod2 : (a+2)%6 = 2 := by omega
      have hmod3 : (a+3)%6 = 3 := by omega
      have hmod4 : (a+4)%6 = 4 := by omega
      have hmod5 : (a+5)%6 = 5 := by omega
      have bound := (c ⟨(a/6)%85, Nat.mod_lt _ (by decide)⟩).isLt
      simp only [Sat.Valuation.satisfies, Sat.Valuation.neg, valuation,
        hdiv1, hdiv2, hdiv3, hdiv4, hdiv5, ha, hmod1, hmod2, hmod3, hmod4, hmod5]
      omega
  cases l <;> cases l2 <;> cases l3 <;> cases l4 <;> cases l5 <;>
    cases l6 <;> cases l7 <;> simp [clauseOK] at h

end Inbox777M10

theorem op_193_k3_m10_at_least_85_vertices :
    ∃ f : Fin 85 → {S : Finset (Fin 10 ⊕ Unit) //
      ((SimpleGraph.cycleGraph 10).sum (⊥ : SimpleGraph Unit)).IsNIndepSet 3 S},
      Function.Injective f := by
  refine ⟨fun i => ⟨Inbox777M10.verts i, Inbox777M10.verts_valid i⟩, ?_⟩
  have hv : Function.Injective Inbox777M10.verts := by decide
  intro i j h
  exact hv (congrArg Subtype.val h)
