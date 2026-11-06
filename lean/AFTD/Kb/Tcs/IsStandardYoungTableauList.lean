import AFTD.Prelude

/-!
# is_standard_young_tableau_list

Topic: combinatorics   Node: e3671dcfc603

Provenance: formalization of a published result. Source: arXiv:2611.07715, Section 2.1 and Lemma 3.12

A list $l$ of cells in $\mathbb{N} \times \mathbb{N}$ represents a standard Young tableau on a finite diagram $D$ (`is_standard_young_tableau_list D l`) if $l$ has no duplicate elements (`l.Nodup`), the set of elements in $l$ equals $D$ (`l.toFinset = D`), and whenever $u, v \in D$ satisfy $u.1 \le v.1$ and $u.2 \le v.2$, $u$ appears before or at $v$ in $l$ ($l.idxOf u \le l.idxOf v$).
-/

/-- A list of cells is a standard Young tableau on D if it lists all cells of D without duplicates in an order extending the componentwise product order. -/
def is_standard_young_tableau_list (D : Finset (ℕ × ℕ)) (l : List (ℕ × ℕ)) : Prop := l.Nodup ∧ l.toFinset = D ∧ ∀ u v : ℕ × ℕ, u ∈ D → v ∈ D → u.1 ≤ v.1 → u.2 ≤ v.2 → l.idxOf u ≤ l.idxOf v
