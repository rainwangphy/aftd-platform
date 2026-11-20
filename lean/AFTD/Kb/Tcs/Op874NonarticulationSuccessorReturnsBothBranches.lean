import AFTD.Prelude
import AFTD.Kb.Tcs.Op874BalancedTrapEntersOnlyAtSuccessor

/-!
# op874_nonarticulation_successor_returns_both_branches

Topic: graphs   Node: e86b4c95a356

Provenance: helper lemma. Balanced directed cut reduction from branch failure to an articulation point.

In a finite loopless two-in/two-out directed multigraph, if a root successor is not an articulation vertex of the underlying undirected graph, both its outgoing branches can reach the root without that successor.
-/

theorem op874_nonarticulation_successor_returns_both_branches {X : Type*} [Fintype X] [DecidableEq X] (p q : Equiv.Perm X) (hfixed : ∀ x, p x ≠ x ∧ q x ≠ x) (r x : X) (harc : p r = x ∨ q r = x) (hweak : ∀ u v, u ≠ x → v ≠ x → Relation.ReflTransGen (fun a b => a ≠ x ∧ b ≠ x ∧ (p a = b ∨ q a = b ∨ p b = a ∨ q b = a)) u v) : Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (p x) r ∧ Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (q x) r := by
  classical
  let R : X → X → Prop := fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)
  let U : X → X → Prop := fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v ∨ p v = u ∨ q v = u)
  have hrx : r ≠ x := by
    rcases harc with hp | hq
    · intro heq; exact (hfixed r).1 (hp.trans heq.symm)
    · intro heq; exact (hfixed r).2 (hq.trans heq.symm)
  let S : Finset X := Finset.univ.filter (fun u => u ≠ x ∧ ¬ Relation.ReflTransGen R u r)
  have hmem (u : X) : u ∈ S ↔ u ≠ x ∧ ¬ Relation.ReflTransGen R u r := by simp [S]
  have hr : r ∉ S := by
    intro h
    exact ((hmem r).mp h).2 Relation.ReflTransGen.refl
  have hx : x ∉ S := by simp [hmem]
  have hclosure (u v : X) (hu : u ∈ S) (hv : v ≠ x) (huv : p u = v ∨ q u = v) : v ∈ S := by
    rw [hmem] at hu ⊢
    refine ⟨hv, ?_⟩
    intro hvR
    exact hu.2 (Relation.ReflTransGen.head ⟨hu.1, hv, huv⟩ hvR)
  have hc (u : X) (hu : u ∈ S) : (p u ∈ S ∨ p u = x) ∧ (q u ∈ S ∨ q u = x) := by
    constructor
    · by_cases he : p u = x
      · exact Or.inr he
      · exact Or.inl (hclosure u (p u) hu he (Or.inl rfl))
    · by_cases he : q u = x
      · exact Or.inr he
      · exact Or.inl (hclosure u (q u) hu he (Or.inr rfl))
  by_contra hh
  have hent : ∃ v ∈ S, p x = v ∨ q x = v := by
    by_cases hp : Relation.ReflTransGen R (p x) r
    · have hq : ¬ Relation.ReflTransGen R (q x) r := fun h => hh ⟨hp, h⟩
      exact ⟨q x, (hmem _).2 ⟨(hfixed x).2, hq⟩, Or.inr rfl⟩
    · exact ⟨p x, (hmem _).2 ⟨(hfixed x).1, hp⟩, Or.inl rfl⟩
  have hnoentry := op874_balanced_trap_enters_only_at_successor p q S r x hr hx harc hc hent
  have hpres (a b : X) (he : U a b) (ha : a ∈ S) : b ∈ S := by
    rcases he with ⟨hax, hbx, hp | hq | hp | hq⟩
    · exact hclosure a b ha hbx (Or.inl hp)
    · exact hclosure a b ha hbx (Or.inr hq)
    · by_contra hb
      exact (hnoentry b hb hbx).1 (hp ▸ ha)
    · by_contra hb
      exact (hnoentry b hb hbx).2 (hq ▸ ha)
  have hpath (a b : X) (hp : Relation.ReflTransGen U a b) : a ∈ S → b ∈ S := by
    induction hp with
    | refl => exact id
    | tail _ he ih => intro ha; exact hpres _ _ he (ih ha)
  obtain ⟨v, hv, _⟩ := hent
  have hvx : v ≠ x := (hmem v).mp hv |>.1
  exact hr (hpath v r (hweak v r hvx hrx) hv)
