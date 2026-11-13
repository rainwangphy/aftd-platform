import AFTD.Prelude

/-!
# poset_braid_map

Topic: combinatorics   Node: 471570f9340f

Provenance: formalization of a published result. Source: scout/2611-15540-solutions-of-the-set-theoretic-quantum-yang-baxter-equation.md:488

For a partially ordered set P with decidable order, the bipartite map poset_braid_map on (P ⊕ (P × ZMod 2)) × (P ⊕ (P × ZMod 2)) fixes pairs from P × P and (P × ZMod 2) × (P × ZMod 2), and for x in P and (y, ε) in P × ZMod 2 swaps the components while adding 1 to ε if y ≤ x.
-/

/-- The involutive poset solution D_P of the braid equation on P ⊕ (P × ZMod 2). -/
def poset_braid_map {P : Type*} [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)]
    (p : (P ⊕ (P × ZMod 2)) × (P ⊕ (P × ZMod 2))) : (P ⊕ (P × ZMod 2)) × (P ⊕ (P × ZMod 2)) :=
  match p with
  | (.inl x, .inl x') => (.inl x, .inl x')
  | (.inr z, .inr z') => (.inr z, .inr z')
  | (.inl x, .inr (y, ε)) =>
    let ε' := if y ≤ x then ε + 1 else ε
    (.inr (y, ε'), .inl x)
  | (.inr (y, ε), .inl x) =>
    let ε' := if y ≤ x then ε + 1 else ε
    (.inl x, .inr (y, ε'))
