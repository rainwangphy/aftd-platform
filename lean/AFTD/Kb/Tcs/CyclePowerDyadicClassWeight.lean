import AFTD.Prelude

/-!
# cycle_power_dyadic_class_weight

Topic: combinatorics   Node: a18770b4aec6

Provenance: helper lemma. Uniform route for OP-205 and RT-1, arXiv:2610.15635 Section 3. Existing k=3,7,15 weight certificates suggest this dyadic tree. The sparse distance graph is obtained recursively by attaching one leaf to every vertex; tight classes are connected subtrees containing the distinguished endpoint edge.

The weighted number of pairs in a dyadic arc: the endpoint pair has weight two, and distances 2^m-2^j for 1≤j<m have weight one.
-/

def cycle_power_dyadic_class_weight (m : ℕ) (b : ℕ → Bool) : ℕ := 2 * (b 0 && b (2 ^ m - 1)).toNat +
  (Finset.range m).sum (fun j => if j = 0 then 0 else
    (Finset.range (2 ^ j)).sum (fun i => (b i && b (i + 2 ^ m - 2 ^ j)).toNat))
