import AFTD.Prelude

/-!
# CopsCanWinFrom

Topic: graphs   Node: fa94765fe0a5

Provenance: formalization of a published result. Source: arXiv:2610.20129 Sec. 1

Cops can force capture from cop positions C and robber position R in the cops and robber game with c cops on G if the robber is already captured, can be captured in the next cop turn, or for some legal cop move, cops can win from every legal subsequent robber response.
-/

/-- Inductive predicate asserting that cops can force capture of the robber from a given position. -/
inductive CopsCanWinFrom {V : Type*} (G : SimpleGraph V) (c : ℕ) : (Fin c → V) → V → Prop where
  | capture (C : Fin c → V) (R : V) (h : ∃ i, C i = R) : CopsCanWinFrom G c C R
  | step_capture (C : Fin c → V) (R : V) (C' : Fin c → V)
      (hC : ∀ i, C' i = C i ∨ G.Adj (C i) (C' i))
      (hcap : ∃ i, C' i = R) :
      CopsCanWinFrom G c C R
  | step (C : Fin c → V) (R : V) (C' : Fin c → V)
      (hC : ∀ i, C' i = C i ∨ G.Adj (C i) (C' i))
      (hR : ∀ R', (R' = R ∨ G.Adj R R') → CopsCanWinFrom G c C' R') :
      CopsCanWinFrom G c C R
