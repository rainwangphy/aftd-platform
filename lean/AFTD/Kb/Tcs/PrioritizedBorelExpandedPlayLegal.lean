import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385ExpandedPlay
import AFTD.Kb.Tcs.PrioritizedBorelEncodingStateCodeLength
import AFTD.Kb.Tcs.PrioritizedBorelEncodingDecodeState
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_expanded_play_legal

Topic: automata   Node: 71c364386fec

Provenance: helper lemma. Infinite-play encoding for arXiv:2611.10136, Conjecture 19.

The encoded sequence of any legal original play is a legal play of the phase-state arena, with the correct initial position and consecutive edge endpoints.
-/

lemma prioritized_borel_expanded_play_legal_block_length {Q : Type} [Fintype Q] (e : TreeGameEdge Q 3) :
    (enc1385Block e).length = Fintype.card Q + 1 := by
  simp [enc1385Block, prioritized_borel_encoding_state_code_length]

lemma prioritized_borel_expanded_play_legal_take_succ_getD {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) (d : α) :
    l.take i ++ [l.getD i d] = l.take (i + 1) := by
  rw [List.getD_eq_getElem l d hi, ← List.take_succ_eq_append_getElem hi]

lemma prioritized_borel_expanded_play_legal_div_mod_cases (n L : ℕ) (hL : 0 < L) :
    (n % L + 1 < L ∧ (n + 1) / L = n / L ∧ (n + 1) % L = n % L + 1) ∨
    (n % L + 1 = L ∧ (n + 1) / L = n / L + 1 ∧ (n + 1) % L = 0) := by
  set k := n / L
  set r := n % L
  have hr : r < L := Nat.mod_lt n hL
  have hn : n = k * L + r := (Nat.div_add_mod' n L).symm
  by_cases h : r + 1 < L
  · left
    have hn1 : n + 1 = k * L + (r + 1) := by omega
    refine ⟨h, ?_, ?_⟩
    · rw [hn1]
      have : (k * L + (r + 1)) / L = k := by
        rw [Nat.add_comm (k * L), Nat.add_mul_div_right (r + 1) k hL]
        rw [Nat.div_eq_of_lt h, Nat.zero_add]
      exact this
    · rw [hn1]
      rw [Nat.add_comm (k * L), Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt h
  · right
    have hr1 : r + 1 = L := by omega
    have hn1 : n + 1 = (k + 1) * L := by
      calc n + 1 = k * L + (r + 1) := by omega
      _ = k * L + L := by rw [hr1]
      _ = (k + 1) * L := by ring
    refine ⟨hr1, ?_, ?_⟩
    · rw [hn1, Nat.mul_div_left (k + 1) hL]
    · rw [hn1, Nat.mul_mod_left (k + 1) L]

lemma prioritized_borel_expanded_play_legal_is_real {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (π : ℕ → TreeGameEdge Q 3)
    (hlegal : ∀ n, π n ∈ G.edges) (n : ℕ) :
    enc1385Real G (enc1385ExpandedPlay G π n).source_state (enc1385ExpandedPlay G π n).dir (enc1385ExpandedPlay G π n).prio := by
  dsimp [enc1385ExpandedPlay]
  set L := Fintype.card Q + 1
  set e := π (n / L)
  set i := n % L
  have hLpos : 0 < L := Nat.succ_pos _
  have hi : i < L := Nat.mod_lt n hLpos
  have hlen : (enc1385Block e).length = L := prioritized_borel_expanded_play_legal_block_length e
  have hi_len : i < (enc1385Block e).length := by rw [hlen]; exact hi
  have htake : (enc1385Block e).take i ++ [(enc1385Block e).getD i false] = (enc1385Block e).take (i + 1) :=
    prioritized_borel_expanded_play_legal_take_succ_getD (enc1385Block e) i hi_len false
  refine ⟨e, hlegal (n / L), rfl, rfl, ?_, ?_⟩
  · rw [htake]
    exact List.take_prefix (i + 1) (enc1385Block e)
  · rw [htake]
    rw [List.length_take]
    rw [hlen]
    have hmin : min (i + 1) L = i + 1 := min_eq_left (Nat.succ_le_of_lt hi)
    rw [hmin]
    have heq : (i + 1 = L) ↔ (i = Fintype.card Q) := by
      dsimp [L]
      omega
    by_cases h : i = Fintype.card Q
    · rw [if_pos (heq.mpr h), if_pos h]
    · rw [if_neg (mt heq.mp h), if_neg h]

lemma prioritized_borel_expanded_play_legal_source_state_next {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (π : ℕ → TreeGameEdge Q 3)
    (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state)
    (n : ℕ) :
    (enc1385ExpandedPlay G π (n + 1)).source_state = (enc1385ExpandedPlay G π n).target_state := by
  dsimp [enc1385ExpandedPlay]
  set L := Fintype.card Q + 1
  set e := π (n / L)
  set i := n % L
  have hLpos : 0 < L := Nat.succ_pos _
  have hi : i < L := Nat.mod_lt n hLpos
  have hlen : (enc1385Block e).length = L := prioritized_borel_expanded_play_legal_block_length e
  have hi_len : i < (enc1385Block e).length := by rw [hlen]; exact hi
  have htake : (enc1385Block e).take i ++ [(enc1385Block e).getD i false] = (enc1385Block e).take (i + 1) :=
    prioritized_borel_expanded_play_legal_take_succ_getD (enc1385Block e) i hi_len false
  dsimp [enc1385Step]
  rw [htake]
  rcases prioritized_borel_expanded_play_legal_div_mod_cases n L hLpos with (⟨h1, hdiv, hmod⟩ | ⟨h2, hdiv, hmod⟩)
  · rw [hdiv, hmod]
    have hlen_take : ((enc1385Block e).take (i + 1)).length = i + 1 := by
      rw [List.length_take, hlen, min_eq_left (Nat.succ_le_of_lt hi)]
    have hcond : ¬((enc1385Block e).take (i + 1)).length = Fintype.card Q + 1 := by
      rw [hlen_take]
      intro h
      have : i + 1 = L := h
      omega
    rw [if_neg hcond]
  · rw [hdiv, hmod]
    have hlen_take : ((enc1385Block e).take (i + 1)).length = L := by
      rw [List.length_take, hlen, h2, min_self]
    have hcond : ((enc1385Block e).take (i + 1)).length = Fintype.card Q + 1 := hlen_take
    rw [if_pos hcond]
    have htake_all : (enc1385Block e).take (i + 1) = enc1385Block e := by
      rw [h2, ← hlen, List.take_length]
    rw [htake_all]
    have hhead : (enc1385Block e).headD false = e.dir := rfl
    have htail : (enc1385Block e).tail = enc1385StateCode e.target_state := rfl
    rw [hhead, htail]
    rw [prioritized_borel_encoding_decode_state]
    have hnxt := hnext (n / L)
    have htake0 : List.take 0 (enc1385Block (π (n / L + 1))) = [] := List.take_zero
    rw [htake0]
    rw [hnxt.1, hnxt.2]

theorem prioritized_borel_expanded_play_legal {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (π : ℕ → TreeGameEdge Q 3) (hlegal : ∀ n, π n ∈ G.edges) (hinit : (π 0).source_node = [] ∧ (π 0).source_state = G.init_state) (hnext : ∀ n, (π (n+1)).source_node = (π n).source_node ++ [(π n).dir] ∧ (π (n+1)).source_state = (π n).target_state) : (∀ n, enc1385ExpandedPlay G π n ∈ (enc1385Game G).edges) ∧ ((enc1385ExpandedPlay G π 0).source_node = [] ∧ (enc1385ExpandedPlay G π 0).source_state = (enc1385Game G).init_state) ∧ ∀ n, (enc1385ExpandedPlay G π (n+1)).source_node = (enc1385ExpandedPlay G π n).source_node ++ [(enc1385ExpandedPlay G π n).dir] ∧ (enc1385ExpandedPlay G π (n+1)).source_state = (enc1385ExpandedPlay G π n).target_state := by
  refine ⟨fun n => ⟨rfl, Or.inl (prioritized_borel_expanded_play_legal_is_real G π hlegal n)⟩, ?_, fun n => ?_⟩
  · dsimp [enc1385ExpandedPlay, enc1385Game]
    refine ⟨rfl, ?_⟩
    simp [hinit.1, hinit.2]
  · refine ⟨?_, prioritized_borel_expanded_play_legal_source_state_next G π hnext n⟩
    dsimp [enc1385ExpandedPlay]
    rw [List.ofFn_succ', List.concat_eq_append]
    rfl
