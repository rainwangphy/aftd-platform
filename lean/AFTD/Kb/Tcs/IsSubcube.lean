import AFTD.Prelude

/-!
# is_subcube

Topic: combinatorics   Node: 36cb129d0a4e

Provenance: formalization of a published result. Source: arXiv:2610.40486 Sec. 1

For an implicit dimension $n$, a dimension $d : \mathbb{N}$, and a finite subset $F : \mathrm{Finset} (\mathrm{Fin}\ n \to \mathrm{Bool})$, `is_subcube d F` holds if there exist a subset of coordinates $S : \mathrm{Finset} (\mathrm{Fin}\ n)$ and a pattern $c : \mathrm{Fin}\ n \to \mathrm{Bool}$ such that $|S| + d = n$ and $F$ consists of all $x : \mathrm{Fin}\ n \to \mathrm{Bool}$ that satisfy $x(i) = c(i)$ for all $i \in S$.
-/

/-- A subset `F` of the Boolean hypercube `Fin n → Bool` is a `d`-dimensional subcube if `n - d` coordinates are fixed to values in `c`. -/
def is_subcube {n : ℕ} (d : ℕ) (F : Finset (Fin n → Bool)) : Prop := ∃ (S : Finset (Fin n)) (c : Fin n → Bool),
    S.card + d = n ∧ F = Finset.univ.filter (fun x => ∀ i ∈ S, x i = c i)
