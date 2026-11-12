import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# prioritized_borel_eventual_hidden_shadow

Topic: automata   Node: 2433c9b1f4c6

Provenance: helper lemma. Hidden-choice strategy compression related to arXiv:2611.10136, Conjecture 19.

Compatible finite histories whose hidden-choice records eventually do not increase and whose extensions add no hidden choices eventually form one nested history.
-/

def op1385HiddenStep {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) (hist : List A) (a : A) : Prop :=
  if own hist then a = policy hist
  else if hidden hist (vis a) then True else a = forced hist (vis a)

def op1385HiddenCompatible {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) : List A → List A → Prop
  | _, [] => True
  | hist, a :: rest =>
    op1385HiddenStep vis own hidden policy forced hist a ∧
      op1385HiddenCompatible vis own hidden policy forced (hist ++ [a]) rest

def op1385HiddenRecord {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) : List A → List A → List A
  | _, [] => []
  | hist, a :: rest =>
    if !own hist && hidden hist (vis a) then
      a :: op1385HiddenRecord vis own hidden (hist ++ [a]) rest
    else op1385HiddenRecord vis own hidden (hist ++ [a]) rest

def op1385HiddenReplay {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) : List A → List Bool → List A → Option (List A × List A)
  | hist, [], record => some (hist, record)
  | hist, b :: bs, record =>
    if own hist then
      let a := policy hist
      if vis a = b then op1385HiddenReplay vis own hidden policy forced (hist ++ [a]) bs record
      else none
    else if hidden hist b then
      match record with
      | [] => none
      | a :: tail =>
        if vis a = b then op1385HiddenReplay vis own hidden policy forced (hist ++ [a]) bs tail
        else none
    else
      let a := forced hist b
      if vis a = b then op1385HiddenReplay vis own hidden policy forced (hist ++ [a]) bs record
      else none

theorem op1385_hidden_replay_recovers {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) (hist xs : List A)
    (h : op1385HiddenCompatible vis own hidden policy forced hist xs) :
    op1385HiddenReplay vis own hidden policy forced hist (xs.map vis)
      (op1385HiddenRecord vis own hidden hist xs) = some (hist ++ xs, []) := by
  induction xs generalizing hist with
  | nil => simp [op1385HiddenRecord, op1385HiddenReplay]
  | cons a xs ih =>
    simp only [op1385HiddenCompatible] at h
    cases ho : own hist <;> cases hb : hidden hist (vis a)
    · have ha' : a = forced hist (vis a) := by simpa [op1385HiddenStep, ho, hb] using h.1
      have ha : forced hist (vis a) = a := ha'.symm
      simpa [op1385HiddenRecord, op1385HiddenReplay, ho, hb, ha, List.append_assoc] using
        ih (hist ++ [a]) h.2
    · simpa [op1385HiddenRecord, op1385HiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [a]) h.2
    · have ha : a = policy hist := by simpa [op1385HiddenStep, ho, hb] using h.1
      subst a
      simpa [op1385HiddenRecord, op1385HiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [policy hist]) h.2
    · have ha : a = policy hist := by simpa [op1385HiddenStep, ho, hb] using h.1
      subst a
      simpa [op1385HiddenRecord, op1385HiddenReplay, ho, hb, List.append_assoc] using
        ih (hist ++ [policy hist]) h.2

theorem op1385_hidden_record_injective {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) (hist xs ys : List A)
    (hx : op1385HiddenCompatible vis own hidden policy forced hist xs)
    (hy : op1385HiddenCompatible vis own hidden policy forced hist ys)
    (hvis : xs.map vis = ys.map vis)
    (hrecord : op1385HiddenRecord vis own hidden hist xs =
      op1385HiddenRecord vis own hidden hist ys) : xs = ys := by
  have hx' := op1385_hidden_replay_recovers vis own hidden policy forced hist xs hx
  have hy' := op1385_hidden_replay_recovers vis own hidden policy forced hist ys hy
  rw [hvis, hrecord] at hx'
  have h := hx'.symm.trans hy'
  exact List.append_cancel_left (congrArg Prod.fst (Option.some.inj h))

theorem op1385_hidden_compatible_snoc {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) (hist xs : List A) (a : A) :
    op1385HiddenCompatible vis own hidden policy forced hist (xs ++ [a]) ↔
      op1385HiddenCompatible vis own hidden policy forced hist xs ∧
      op1385HiddenStep vis own hidden policy forced (hist ++ xs) a := by
  induction xs generalizing hist with
  | nil => simp [op1385HiddenCompatible]
  | cons x xs ih =>
    simp [op1385HiddenCompatible, ih, List.append_assoc, and_assoc]

theorem op1385_hidden_record_snoc {A : Type} (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (hist xs : List A) (a : A) :
    op1385HiddenRecord vis own hidden hist (xs ++ [a]) =
      op1385HiddenRecord vis own hidden hist xs ++
        (if !own (hist ++ xs) && hidden (hist ++ xs) (vis a) then [a] else []) := by
  induction xs generalizing hist with
  | nil => simp [op1385HiddenRecord]
  | cons x xs ih =>
    cases hb : (!own hist && hidden hist (vis x)) <;>
      simp [op1385HiddenRecord, hb, ih, List.append_assoc]

theorem op1385_eventually_antitone_well_order_stabilizes
    {α : Type} [PartialOrder α] [WellFoundedLT α] (r : ℕ → α) (N : ℕ)
    (hstep : ∀ n ≥ N, r (n+1) ≤ r n) :
    ∃ K ≥ N, ∀ n ≥ K, r n = r K := by
  let f : ℕ → α := fun n => r (N+n)
  have hmono : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    have h := hstep (N+n) (by omega)
    simpa [f, Nat.add_assoc] using h
  obtain ⟨K, hK⟩ := WellFoundedLT.antitone_chain_condition hmono
  refine ⟨N+K, by omega, ?_⟩
  intro n hn
  have hstart : N ≤ n := by omega
  have hi : K ≤ n-N := by omega
  have h := hK (n-N) hi
  change r (N+K) = r (N+(n-N)) at h
  simpa only [Nat.add_sub_of_le hstart] using h.symm

theorem prioritized_borel_eventual_hidden_shadow {A : Type} [LinearOrder (List A)]
    [WellFoundedLT (List A)] (vis : A → Bool) (own : List A → Bool)
    (hidden : List A → Bool → Bool) (policy : List A → A)
    (forced : List A → Bool → A) (histories : ℕ → List A) (actual : ℕ → A)
    (N : ℕ)
    (hcompat : ∀ n, op1385HiddenCompatible vis own hidden policy forced [] (histories n))
    (hdir : ∀ n, (histories (n+1)).map vis = (histories n).map vis ++ [vis (actual n)])
    (hext : ∀ n ≥ N, op1385HiddenCompatible vis own hidden policy forced []
      (histories n ++ [actual n]))
    (hrecord : ∀ n ≥ N, op1385HiddenRecord vis own hidden [] (histories n ++ [actual n]) =
      op1385HiddenRecord vis own hidden [] (histories n))
    (hstep : ∀ n ≥ N, op1385HiddenRecord vis own hidden [] (histories (n+1)) ≤
      op1385HiddenRecord vis own hidden [] (histories n)) :
    ∃ K ≥ N, ∀ n ≥ K, histories (n+1) = histories n ++ [actual n] := by
  let rank : ℕ → List A := fun n => op1385HiddenRecord vis own hidden [] (histories n)
  obtain ⟨K, hKN, hstable⟩ := op1385_eventually_antitone_well_order_stabilizes rank N hstep
  refine ⟨K, hKN, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans hKN hn
  have hrec : op1385HiddenRecord vis own hidden [] (histories (n+1)) =
      op1385HiddenRecord vis own hidden [] (histories n ++ [actual n]) := by
    rw [hrecord n hnN]
    exact (hstable (n+1) (by omega)).trans (hstable n hn).symm
  apply op1385_hidden_record_injective vis own hidden policy forced []
    (histories (n+1)) (histories n ++ [actual n]) (hcompat (n+1)) (hext n hnN)
  · simpa using hdir n
  · exact hrec
