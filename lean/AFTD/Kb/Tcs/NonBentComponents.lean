import AFTD.Prelude
import AFTD.Kb.Tcs.IsFieldBent
import AFTD.Kb.Tcs.ApnFamilyFa

/-!
# non_bent_components

Topic: cryptography   Node: 76aecfd58a1a

Provenance: formalization of a published result. Source: arXiv:2611.10269 Sec. 7

For a finite field $E$ of characteristic 2 (equipped with an algebra structure over $\mathbb{Z}/2\mathbb{Z}$), a natural number $m$, and an element $a \in E$, the set of non-bent components of $F_a$ with parameter $m$ is the set of all nonzero $\beta \in E$ such that the Boolean function $x \mapsto \mathrm{Tr}(\beta F_a(x))$ is not field-bent with parameter $m$.
-/

/-- The set N_{F_a} of nonzero field elements β whose component function under F_a is non-bent. -/
def non_bent_components (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E] (m : ℕ) (a : E) : Set E := {β : E | β ≠ 0 ∧ ¬ is_field_bent E m (fun x => Algebra.trace (ZMod 2) E (β * apn_family_fa E a x))}
