import AFTD.Prelude
import AFTD.Kb.Tcs.GroupPrimeCompositionSeries
import AFTD.Kb.Tcs.FlagRepresentatives

/-!
# flag_hash_offset

Topic: data_structures   Node: 89ee5afb404c

Provenance: formalization of a published result. Source: arXiv:2610.31363: A Sharp Analysis of Fixed Offset Hash Tables

Given a group G, a natural number k, prime quotient orders p : Fin k → ℕ, a prime composition series series : GroupPrimeCompositionSeries G k p, flag representatives reps : FlagRepresentatives series, and an index j : Fin (∏ i : Fin k, p i), flag_hash_offset reps j is the product in G in reverse order (from k - 1 down to 0) of reps.g i (d i) for i : Fin k, where each digit d i : Fin (p i) has value (j.val / ∏ a ∈ Finset.univ.filter (fun a : Fin k => a < i), p a) % p i.
-/

/-- The offset sequence element in a solvable group flag hash table defined by mixed-radix digits. -/
def flag_hash_offset {G : Type*} [Group G] {k : ℕ} {p : Fin k → ℕ}
    {series : GroupPrimeCompositionSeries G k p} (reps : FlagRepresentatives series)
    (j : Fin (∏ i : Fin k, p i)) : G :=
  let d (i : Fin k) : Fin (p i) :=
    ⟨(j.val / ∏ a ∈ Finset.univ.filter (fun (a : Fin k) => a < i), p a) % p i,
     Nat.mod_lt _ (series.prime i).pos⟩
  (List.ofFn (fun i : Fin k => reps.g i (d i))).reverse.prod
