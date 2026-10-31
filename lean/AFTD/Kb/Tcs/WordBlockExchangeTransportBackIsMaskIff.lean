import AFTD.Prelude
import AFTD.Kb.Tcs.WordBlockExchangeTransportBack
import AFTD.Kb.Tcs.IsWordMask
import AFTD.Kb.Tcs.WordBlockExchangeAfter
import AFTD.Kb.Tcs.WordBlockExchange
import AFTD.Kb.Tcs.WordBlockExchangeIsCommuting
import AFTD.Kb.Tcs.WordProj
import AFTD.Kb.Tcs.WordBlockExchangeBefore

/-!
# word_block_exchange_transport_back_is_mask_iff

Topic: automata   Node: ec3a15a11867

Provenance: formalization of a published result. Source: arXiv:2610.39941, Lemma 2

For an exchange E and a mask N satisfying is_word_mask u v (word_block_exchange_after E) N, the backward-transported mask word_block_exchange_transport_back E N is a valid mask of word_block_exchange_before E for sources u and v if and only if N commutes for E: is_word_mask u v (word_block_exchange_before E) (word_block_exchange_transport_back E N) ↔ word_block_exchange_is_commuting E N.
-/

lemma word_block_exchange_transport_back_is_mask_iff_word_proj_append {α : Type*} (b : Bool)
    (w1 w2 : List α) (m1 m2 : List Bool) (h : m1.length = w1.length) :
    word_proj b (w1 ++ w2) (m1 ++ m2) = word_proj b w1 m1 ++ word_proj b w2 m2 := by
  induction' w1 with x xs ih generalizing m1
  · cases m1
    · simp [word_proj]
    · cases h
  · cases m1
    · cases h
    · simp only [List.length_cons] at h
      injection h with h'
      dsimp [word_proj]
      split_ifs with heq
      · simp [ih _ h']
      · exact ih _ h'

lemma word_block_exchange_transport_back_is_mask_iff_word_proj_four {α : Type*} (b : Bool)
    (w1 w2 w3 w4 : List α) (m1 m2 m3 m4 : List Bool)
    (h1 : m1.length = w1.length) (h2 : m2.length = w2.length)
    (h3 : m3.length = w3.length) :
    word_proj b (w1 ++ w2 ++ w3 ++ w4) (m1 ++ m2 ++ m3 ++ m4) =
      word_proj b w1 m1 ++ word_proj b w2 m2 ++ word_proj b w3 m3 ++ word_proj b w4 m4 := by
  have l12 : (m1 ++ m2).length = (w1 ++ w2).length := by simp [h1, h2]
  have l123 : (m1 ++ m2 ++ m3).length = (w1 ++ w2 ++ w3).length := by
    repeat rw [List.length_append]
    omega
  rw [word_block_exchange_transport_back_is_mask_iff_word_proj_append b (w1 ++ w2 ++ w3) w4 (m1 ++ m2 ++ m3) m4 l123]
  rw [word_block_exchange_transport_back_is_mask_iff_word_proj_append b (w1 ++ w2) w3 (m1 ++ m2) m3 l12]
  rw [word_block_exchange_transport_back_is_mask_iff_word_proj_append b w1 w2 m1 m2 h1]

lemma word_block_exchange_transport_back_is_mask_iff_append_four_cancel {α : Type*} (x a b y : List α) :
    x ++ a ++ b ++ y = x ++ b ++ a ++ y ↔ a ++ b = b ++ a := by
  constructor
  · intro h
    have h1 := List.append_cancel_right h
    rw [List.append_assoc, List.append_assoc] at h1
    exact List.append_cancel_left h1
  · intro h
    congr 1
    rw [List.append_assoc, h, ← List.append_assoc]

lemma word_block_exchange_transport_back_is_mask_iff_list_split_four {α : Type*} (l : List α) (n1 n2 n3 n4 : ℕ)
    (h : l.length = n1 + n2 + n3 + n4) :
    let p1 := l.take n1
    let p2 := (l.drop n1).take n2
    let p3 := (l.drop (n1 + n2)).take n3
    let p4 := l.drop (n1 + n2 + n3)
    p1.length = n1 ∧ p2.length = n2 ∧ p3.length = n3 ∧ p4.length = n4 ∧
    l = p1 ++ p2 ++ p3 ++ p4 := by
  dsimp
  have h1 : (l.take n1).length = n1 := by
    rw [List.length_take]
    omega
  have h2 : ((l.drop n1).take n2).length = n2 := by
    rw [List.length_take, List.length_drop]
    omega
  have h3 : ((l.drop (n1 + n2)).take n3).length = n3 := by
    rw [List.length_take, List.length_drop]
    omega
  have h4 : (l.drop (n1 + n2 + n3)).length = n4 := by
    rw [List.length_drop]
    omega
  refine ⟨h1, h2, h3, h4, ?_⟩
  have eq1 : l = l.take n1 ++ l.drop n1 := (List.take_append_drop n1 l).symm
  have eq2 : l.drop n1 = (l.drop n1).take n2 ++ (l.drop n1).drop n2 :=
    (List.take_append_drop n2 (l.drop n1)).symm
  have eq3 : (l.drop (n1 + n2)) = (l.drop (n1 + n2)).take n3 ++ (l.drop (n1 + n2)).drop n3 :=
    (List.take_append_drop n3 (l.drop (n1 + n2))).symm
  rw [List.drop_drop] at eq2
  rw [eq3] at eq2
  rw [List.drop_drop] at eq2
  rw [eq2] at eq1
  rw [List.append_assoc, List.append_assoc]
  exact eq1

/-- Lemma 2: Transporting a mask N of XBAY back to XABY preserves source projections iff N commutes. -/
theorem word_block_exchange_transport_back_is_mask_iff {α : Type*}
    (E : WordBlockExchange α) (u v : List α) (N : List Bool)
    (hN : is_word_mask u v (word_block_exchange_after E) N) :
    is_word_mask u v (word_block_exchange_before E) (word_block_exchange_transport_back E N) ↔
      word_block_exchange_is_commuting E N := by
  rcases hN with ⟨hlenN, huN, hvN⟩
  have hlenN' : N.length = E.X.length + E.B.length + E.A.length + E.Y.length := by
    rw [hlenN]
    dsimp [word_block_exchange_after]
    repeat rw [List.length_append]
  have hsplit := word_block_exchange_transport_back_is_mask_iff_list_split_four N E.X.length E.B.length E.A.length E.Y.length hlenN'
  rcases hsplit with ⟨h1, h2, h3, h4, hN_eq⟩
  set p1 := N.take E.X.length
  set p2 := (N.drop E.X.length).take E.B.length
  set p3 := (N.drop (E.X.length + E.B.length)).take E.A.length
  set p4 := N.drop (E.X.length + E.B.length + E.A.length)
  have htb_len : (word_block_exchange_transport_back E N).length =
      (word_block_exchange_before E).length := by
    change (p1 ++ p3 ++ p2 ++ p4).length = (E.X ++ E.A ++ E.B ++ E.Y).length
    repeat rw [List.length_append]
    omega
  have hu_proj : word_proj true (word_block_exchange_after E) N =
      word_proj true E.X p1 ++ word_proj true E.B p2 ++ word_proj true E.A p3 ++ word_proj true E.Y p4 := by
    have : word_block_exchange_after E = E.X ++ E.B ++ E.A ++ E.Y := rfl
    rw [this, hN_eq]
    exact word_block_exchange_transport_back_is_mask_iff_word_proj_four true E.X E.B E.A E.Y p1 p2 p3 p4 h1 h2 h3
  have hv_proj : word_proj false (word_block_exchange_after E) N =
      word_proj false E.X p1 ++ word_proj false E.B p2 ++ word_proj false E.A p3 ++ word_proj false E.Y p4 := by
    have : word_block_exchange_after E = E.X ++ E.B ++ E.A ++ E.Y := rfl
    rw [this, hN_eq]
    exact word_block_exchange_transport_back_is_mask_iff_word_proj_four false E.X E.B E.A E.Y p1 p2 p3 p4 h1 h2 h3
  have hu_tb : word_proj true (word_block_exchange_before E) (word_block_exchange_transport_back E N) =
      word_proj true E.X p1 ++ word_proj true E.A p3 ++ word_proj true E.B p2 ++ word_proj true E.Y p4 := by
    have : word_block_exchange_before E = E.X ++ E.A ++ E.B ++ E.Y := rfl
    have htb_eq : word_block_exchange_transport_back E N = p1 ++ p3 ++ p2 ++ p4 := rfl
    rw [this, htb_eq]
    exact word_block_exchange_transport_back_is_mask_iff_word_proj_four true E.X E.A E.B E.Y p1 p3 p2 p4 h1 h3 h2
  have hv_tb : word_proj false (word_block_exchange_before E) (word_block_exchange_transport_back E N) =
      word_proj false E.X p1 ++ word_proj false E.A p3 ++ word_proj false E.B p2 ++ word_proj false E.Y p4 := by
    have : word_block_exchange_before E = E.X ++ E.A ++ E.B ++ E.Y := rfl
    have htb_eq : word_block_exchange_transport_back E N = p1 ++ p3 ++ p2 ++ p4 := rfl
    rw [this, htb_eq]
    exact word_block_exchange_transport_back_is_mask_iff_word_proj_four false E.X E.A E.B E.Y p1 p3 p2 p4 h1 h3 h2
  rw [huN] at hu_proj
  rw [hvN] at hv_proj
  dsimp [is_word_mask, word_block_exchange_is_commuting]
  simp only [htb_len, true_and]
  rw [hu_tb, hv_tb]
  rw [hu_proj, hv_proj]
  rw [word_block_exchange_transport_back_is_mask_iff_append_four_cancel,
      word_block_exchange_transport_back_is_mask_iff_append_four_cancel]
