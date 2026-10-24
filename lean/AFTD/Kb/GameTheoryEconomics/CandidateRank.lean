import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# candidate_rank

Topic: social_choice   Node: 83d6452e29cf

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 2

Given a finite candidate type C with decidable equality, a linear order ord on C, and a candidate c in C, candidate_rank ord c is the 0-based index of c in Fin (Fintype.card C), defined as the number of candidates strictly greater than c under ord.
-/

/-- The 0-based rank of candidate c in a linear order on candidates C, given by the number of candidates strictly preferred to c. -/
def candidate_rank {C : Type*} [Fintype C] [DecidableEq C]
    (ord : LinearOrder C) (c : C) : Fin (Fintype.card C) :=
  letI := ord
  have h_not : c ∉ Finset.filter (fun c' => c < c') Finset.univ := by simp
  have h_ssubset : Finset.filter (fun c' => c < c') Finset.univ ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro h_all
    have : c ∈ Finset.filter (fun c' => c < c') Finset.univ := by rw [h_all]; exact Finset.mem_univ c
    exact h_not this
  ⟨(Finset.filter (fun c' => c < c') Finset.univ).card, Finset.card_lt_card h_ssubset⟩
