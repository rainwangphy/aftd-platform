import AFTD.Prelude

/-!
# op309_is_matching

Topic: graphs   Node: c8e0c6328dde

Provenance: helper lemma. step towards op309_paired_cubic_ports_nonmono_exists

A matching on ports in a cubic port graph: closed under the port involution p and containing at most one port at each vertex.
-/

/-- A matching on ports in a cubic port graph: closed under the port involution p and with at most one port at each vertex. -/
def op309_is_matching {B : Type*} [DecidableEq B]
    (p : B × Fin 3 → B × Fin 3) (M : Finset (B × Fin 3)) : Prop :=
  (∀ v ∈ M, p v ∈ M) ∧
  (∀ b : B, ∀ i j : Fin 3, (b, i) ∈ M → (b, j) ∈ M → i = j)
