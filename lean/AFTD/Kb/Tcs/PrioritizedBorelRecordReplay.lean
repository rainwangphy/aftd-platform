import AFTD.Prelude

/-!
# prioritized_borel_record_replay

Topic: automata   Node: 01f30f5ec417

Provenance: helper lemma. Strategy reconstruction for arXiv:2611.10136, Conjecture 19.

A compatible finite history can be reconstructed from its length and the sequence of choices at opponent-controlled branching positions.
-/

def op1385Compatible {A : Type} (own branch : List A → Bool)
    (policy forced : List A → A) : List A → List A → Prop
  | _, [] => True
  | hist, a :: rest =>
    (if own hist then a = policy hist else if branch hist then True else a = forced hist) ∧
      op1385Compatible own branch policy forced (hist ++ [a]) rest

def op1385Record {A : Type} (own branch : List A → Bool) : List A → List A → List A
  | _, [] => []
  | hist, a :: rest =>
    if !own hist && branch hist then
      a :: op1385Record own branch (hist ++ [a]) rest
    else op1385Record own branch (hist ++ [a]) rest

def op1385Replay {A : Type} (own branch : List A → Bool)
    (policy forced : List A → A) : List A → List A → ℕ → Option (List A × List A)
  | hist, record, 0 => some (hist, record)
  | hist, record, n + 1 =>
    if own hist then
      op1385Replay own branch policy forced (hist ++ [policy hist]) record n
    else if branch hist then
      match record with
      | [] => none
      | a :: tail => op1385Replay own branch policy forced (hist ++ [a]) tail n
    else op1385Replay own branch policy forced (hist ++ [forced hist]) record n

theorem prioritized_borel_record_replay {A : Type} (own branch : List A → Bool)
    (policy forced : List A → A) (hist xs : List A)
    (h : op1385Compatible own branch policy forced hist xs) :
    op1385Replay own branch policy forced hist (op1385Record own branch hist xs) xs.length =
      some (hist ++ xs, []) := by
  induction xs generalizing hist with
  | nil => simp [op1385Record, op1385Replay]
  | cons a xs ih =>
    simp only [op1385Compatible] at h
    cases ho : own hist <;> cases hb : branch hist
    · have ha : a = forced hist := by simpa [ho, hb] using h.1
      subst a
      simpa [op1385Record, op1385Replay, ho, hb, List.append_assoc] using ih (hist ++ [forced hist]) h.2
    · simpa [op1385Record, op1385Replay, ho, hb, List.append_assoc] using ih (hist ++ [a]) h.2
    · have ha : a = policy hist := by simpa [ho, hb] using h.1
      subst a
      simpa [op1385Record, op1385Replay, ho, hb, List.append_assoc] using ih (hist ++ [policy hist]) h.2
    · have ha : a = policy hist := by simpa [ho, hb] using h.1
      subst a
      simpa [op1385Record, op1385Replay, ho, hb, List.append_assoc] using ih (hist ++ [policy hist]) h.2
