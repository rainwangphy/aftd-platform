import AFTD.Prelude

/-!
# pmms3c_cost

Topic: fair_division   Node: cc1c6046afc4

Integer costs of three agents for nine chores: agent 0 (21,38,28,24,20,35,29,41,18), agent 1 (15,41,27,25,23,26,28,35,21), agent 2 (16,41,38,26,21,29,39,40,20). They are 101 minus the values in the three-agent, nine-good instance of Table 2 of arXiv:2609.10493.
-/

/-- Costs of the three-agent, nine-chore instance: 101 minus the values of the goods instance in Table 2 of arXiv:2609.10493. -/
def pmms3c_cost : Fin 3 → Fin 9 → ℕ :=
  ![![21, 38, 28, 24, 20, 35, 29, 41, 18],
    ![15, 41, 27, 25, 23, 26, 28, 35, 21],
    ![16, 41, 38, 26, 21, 29, 39, 40, 20]]
