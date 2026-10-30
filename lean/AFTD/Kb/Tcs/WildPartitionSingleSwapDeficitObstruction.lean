import AFTD.Prelude
import AFTD.Kb.Tcs.WildPartitionSingleSwapObstruction
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# wild_partition_single_swap_deficit_obstruction

Topic: graphs   Node: b50e294de671

Provenance: helper lemma. IN-385 / OP-306 campaign10,2026-10-30. Internal structural-route diagnostic for https://arxiv.org/html/2610.22142v1 Sections3.3/6. Targeted SAT experiment9745 and independent NetworkX audit9751 found and checked this explicit array; the proof uses kernel-checked finite cut/path certificates and ordinary connected-component cardinal arguments. This is not a published-paper erratum, a main conjecture refutation, a new wild-number case, or a research advance.

For the explicit normalized15 array and valid consecutive triple partition of wild_partition_single_swap_obstruction, the sum over colors of the number of connected components in the color quotient graph minus1 is exactly1. It is at least1 after every vertex transposition and equals0 at the displayed repair partition. Thus strict one-step vertex-swap descent fails. Equal-deficit plateau moves and the general wild-number conjecture are not refuted.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem in385_trap_repair_good :
    (∀ b : Fin 5,(univ.filter fun v => in385_trap_repair_block v=b).card=3) ∧
    (∀ i : Fin 15,¬wild_joint_bad_relation 5 in385_trap_repair_block
      (fun x y => x≠y ∧ in385_trap_array x y=i)) := by
  unfold wild_joint_bad_relation
  decide +kernel


def in385_trap_graph (p : Fin 15 → Fin 5) (i : Fin 15) : SimpleGraph (Fin 5) where
  Adj b d := b≠d ∧ ∃ x : Fin 15,p x=b ∧ p (in385_trap_mate i x)=d
  symm := ⟨by
    rintro b d ⟨hbd,x,hx,hy⟩
    refine ⟨hbd.symm,in385_trap_mate i x,hy,?_⟩
    rw [in385_trap_mate_involution]
    exact hx⟩
  loopless := ⟨by intro b; simp⟩

theorem in385_trap_graph_adj_iff (p : Fin 15 → Fin 5) (i : Fin 15) (b d : Fin 5) :
    (in385_trap_graph p i).Adj b d ↔
      b≠d ∧ ∃ x y : Fin 15,p x=b ∧ p y=d ∧ x≠y ∧ in385_trap_array x y=i := by
  constructor
  · rintro ⟨hbd,x,hx,hy⟩
    refine ⟨hbd,x,in385_trap_mate i x,hx,hy,?_,in385_trap_mate_color i x⟩
    intro h
    exact hbd (hx.symm.trans ((congrArg p h).trans hy))
  · rintro ⟨hbd,x,y,hx,hy,_,hA⟩
    have he : y=in385_trap_mate i x :=
      in385_trap_normalized.2.2 x (hA.trans (in385_trap_mate_color i x).symm)
    exact ⟨hbd,x,hx,he ▸ hy⟩

instance in385_trap_graph_decidable (p : Fin 15 → Fin 5) (i : Fin 15) :
    DecidableRel (in385_trap_graph p i).Adj := by
  unfold in385_trap_graph
  infer_instance

def in385_trap_deficit (p : Fin 15 → Fin 5) : ℕ :=
  ∑ i : Fin 15,(Fintype.card (in385_trap_graph p i).ConnectedComponent-1)


def in385_trap_compact_rows (repair : Bool) : Fin 15 → Fin 5 → ℕ :=
  if repair then ![![12,4,11,21,8],
  ![18,13,26,22,13],
  ![24,24,16,3,7],
  ![4,20,19,16,14],
  ![12,24,9,7,2],
  ![26,17,16,1,7],
  ![10,5,18,17,12],
  ![26,9,16,3,5],
  ![14,21,11,5,2],
  ![18,13,26,6,5],
  ![20,16,9,4,3],
  ![28,4,11,21,9],
  ![4,24,9,22,10],
  ![14,21,19,1,6],
  ![2,13,2,18,8]]
  else ![![24,4,2,17,9],
  ![18,5,10,20,9],
  ![12,24,17,3,6],
  ![4,16,25,4,6],
  ![12,24,17,19,14],
  ![14,17,1,1,2],
  ![10,17,24,21,14],
  ![14,9,17,3,4],
  ![14,25,9,7,2],
  ![18,5,10,20,9],
  ![20,8,1,18,9],
  ![24,4,26,5,5],
  ![4,24,9,6,2],
  ![26,13,26,7,5],
  ![2,5,18,16,12]]

theorem in385_trap_compact_symm : ∀ (flag : Bool) (i : Fin 15) (b d : Fin 5),
    (in385_trap_compact_rows flag i b).testBit d.val =
      (in385_trap_compact_rows flag i d).testBit b.val := by
  decide +kernel

theorem in385_trap_compact_irrefl : ∀ (flag : Bool) (i : Fin 15) (b : Fin 5),
    (in385_trap_compact_rows flag i b).testBit b.val=false := by
  decide +kernel

def in385_trap_compact_graph (flag : Bool) (i : Fin 15) : SimpleGraph (Fin 5) where
  Adj b d := (in385_trap_compact_rows flag i b).testBit d.val=true
  symm := ⟨by intro b d h; rwa [in385_trap_compact_symm] at h⟩
  loopless := ⟨by intro b; rw [in385_trap_compact_irrefl]; decide⟩

instance in385_trap_compact_graph_decidable (flag : Bool) (i : Fin 15) :
    DecidableRel (in385_trap_compact_graph flag i).Adj := by
  unfold in385_trap_compact_graph
  infer_instance

theorem in385_trap_compact_certificate : ∀ (flag : Bool) (i : Fin 15) (b d : Fin 5),
    (in385_trap_graph (if flag then in385_trap_repair_block else in385_trap_block) i).Adj b d ↔
      (in385_trap_compact_rows flag i b).testBit d.val=true := by
  decide +kernel

theorem in385_trap_compact_eq (flag : Bool) (i : Fin 15) :
    in385_trap_graph (if flag then in385_trap_repair_block else in385_trap_block) i =
      in385_trap_compact_graph flag i := by
  ext b d
  exact in385_trap_compact_certificate flag i b d

lemma wild_graph_components_gt_one_of_closed_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V)
    (hB : B.Nonempty) (hBu : B≠univ)
    (hclosed : ∀ x y,G.Adj x y → (x∈B ↔ y∈B)) :
    1 < Fintype.card G.ConnectedComponent := by
  classical
  obtain ⟨b,hb⟩ := hB
  have hex : ∃ c : V,c∉B := by
    by_contra h
    push_neg at h
    exact hBu (eq_univ_of_forall h)
  obtain ⟨c,hc⟩ := hex
  have hr : ∀ x y,G.Reachable x y → (x∈B ↔ y∈B) := by
    rintro x y ⟨p⟩
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hclosed _ _ h).trans ih
  have hne : G.connectedComponentMk b ≠ G.connectedComponentMk c := by
    intro h
    exact hc ((hr b c (SimpleGraph.ConnectedComponent.exact h)).mp hb)
  exact Fintype.one_lt_card_iff.mpr ⟨_,_,hne⟩


def in385_trap_path_root (flag : Bool) (i : Fin 15) (b : Fin 5) : Fin 5 :=
  if flag=false ∧ i=0 ∧ (b=1 ∨ b=2) then 1 else 0

def in385_trap_path1 (flag : Bool) : Fin 15 → Fin 5 → Fin 5 :=
  if flag then ![![0,2,2,3,3],
  ![0,1,1,1,4],
  ![0,3,4,3,4],
  ![0,2,2,2,2],
  ![0,3,2,3,3],
  ![0,1,4,3,4],
  ![0,1,1,3,3],
  ![0,1,4,3,4],
  ![0,1,2,3,1],
  ![0,1,1,1,4],
  ![0,4,2,2,4],
  ![0,2,2,3,4],
  ![0,2,2,2,2],
  ![0,1,2,3,1],
  ![0,1,1,1,1]]
  else ![![0,1,2,3,4],
  ![0,1,1,4,4],
  ![0,3,2,3,2],
  ![0,2,2,2,2],
  ![0,3,2,3,2],
  ![0,1,2,3,1],
  ![0,1,3,3,1],
  ![0,1,2,3,2],
  ![0,1,2,3,1],
  ![0,1,1,4,4],
  ![0,4,2,4,4],
  ![0,3,3,3,4],
  ![0,2,2,2,2],
  ![0,1,1,3,4],
  ![0,1,1,1,1]]

def in385_trap_path2 (flag : Bool) : Fin 15 → Fin 5 → Fin 5 :=
  if flag then ![![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,4,4],
  ![0,1,2,3,1],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,3,2,3,3],
  ![0,1,2,3,4],
  ![0,1,2,3,3]]
  else ![![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,4,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,3,2,3,4],
  ![0,2,2,3,4],
  ![0,3,2,3,3],
  ![0,1,2,3,4],
  ![0,1,2,2,2]]

def in385_trap_path3 (flag : Bool) : Fin 15 → Fin 5 → Fin 5 :=
  if flag then ![![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4]]
  else ![![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,1],
  ![0,1,2,3,4],
  ![0,1,2,4,4]]

theorem in385_trap_path_certificate : ∀ (flag : Bool) (i : Fin 15) (b : Fin 5),
    (in385_trap_path_root flag i b=in385_trap_path1 flag i b ∨
      (in385_trap_compact_graph flag i).Adj (in385_trap_path_root flag i b) (in385_trap_path1 flag i b)) ∧
    (in385_trap_path1 flag i b=in385_trap_path2 flag i b ∨
      (in385_trap_compact_graph flag i).Adj (in385_trap_path1 flag i b) (in385_trap_path2 flag i b)) ∧
    (in385_trap_path2 flag i b=in385_trap_path3 flag i b ∨
      (in385_trap_compact_graph flag i).Adj (in385_trap_path2 flag i b) (in385_trap_path3 flag i b)) ∧
    (in385_trap_path3 flag i b=b ∨
      (in385_trap_compact_graph flag i).Adj (in385_trap_path3 flag i b) b) := by
  decide +kernel

theorem in385_trap_path_reachable (flag : Bool) (i : Fin 15) (b : Fin 5) :
    (in385_trap_compact_graph flag i).Reachable (in385_trap_path_root flag i b) b := by
  have step {a d : Fin 5} (h : a=d ∨ (in385_trap_compact_graph flag i).Adj a d) :
      (in385_trap_compact_graph flag i).Reachable a d := by
    rcases h with rfl|h
    · exact SimpleGraph.Reachable.refl _
    · exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil⟩
  exact (step (in385_trap_path_certificate flag i b).1).trans
    ((step (in385_trap_path_certificate flag i b).2.1).trans
      ((step (in385_trap_path_certificate flag i b).2.2.1).trans
        (step (in385_trap_path_certificate flag i b).2.2.2)))

theorem in385_trap_compact_connected_card (flag : Bool) (i : Fin 15)
    (h : flag=true ∨ i≠0) :
    Fintype.card (in385_trap_compact_graph flag i).ConnectedComponent=1 := by
  have hr (b : Fin 5) : (in385_trap_compact_graph flag i).Reachable 0 b := by
    have hh := in385_trap_path_reachable flag i b
    have he : in385_trap_path_root flag i b=0 := by
      rcases h with h|h <;> simp [in385_trap_path_root,h]
    rwa [he] at hh
  have hp : (in385_trap_compact_graph flag i).Preconnected :=
    fun a b => (hr a).symm.trans (hr b)
  letI := hp.subsingleton_connectedComponent
  exact Fintype.card_eq_one_of_forall_eq
    (i := (in385_trap_compact_graph flag i).connectedComponentMk 0)
    (fun j => Subsingleton.elim j _)

theorem in385_trap_compact_zero_card :
    Fintype.card (in385_trap_compact_graph false 0).ConnectedComponent=2 := by
  let G := in385_trap_compact_graph false 0
  have hclosed : ∀ b d : Fin 5,G.Adj b d →
      (b∈({1,2} : Finset (Fin 5)) ↔ d∈({1,2} : Finset (Fin 5))) := by
    decide +kernel
  have hlo : 1<Fintype.card G.ConnectedComponent :=
    wild_graph_components_gt_one_of_closed_cut G {1,2} (by simp) (by decide) hclosed
  let f : Bool → G.ConnectedComponent := fun t => G.connectedComponentMk (if t then 1 else 0)
  have hf : Function.Surjective f := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      by_cases hv : v=1 ∨ v=2
      · refine ⟨true,?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        simpa [G,in385_trap_path_root,hv] using in385_trap_path_reachable false 0 v
      · refine ⟨false,?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        simpa [G,in385_trap_path_root,hv] using in385_trap_path_reachable false 0 v
  have hhi := Fintype.card_le_of_surjective f hf
  exact Nat.le_antisymm (by simpa only [Fintype.card_bool] using hhi) hlo

theorem in385_trap_base_deficit : in385_trap_deficit in385_trap_block=1 := by
  unfold in385_trap_deficit
  have he (i : Fin 15) : in385_trap_graph in385_trap_block i = in385_trap_compact_graph false i :=
    in385_trap_compact_eq false i
  simp_rw [he]
  have hc (i : Fin 15) : Fintype.card (in385_trap_compact_graph false i).ConnectedComponent=
      if i=0 then 2 else 1 := by
    by_cases hi : i=0
    · subst i; simpa using in385_trap_compact_zero_card
    · simp [hi,in385_trap_compact_connected_card false i (Or.inr hi)]
  simp_rw [hc]
  decide +kernel


lemma in385_trap_deficit_pos_of_bad (p : Fin 15 → Fin 5) (i : Fin 15)
    (h : wild_joint_bad_relation 5 p (fun x y => x≠y ∧ in385_trap_array x y=i)) :
    1 ≤ in385_trap_deficit p := by
  rcases h with ⟨B,hB,hBu,hcl⟩
  have hc : 1 < Fintype.card (in385_trap_graph p i).ConnectedComponent := by
    apply wild_graph_components_gt_one_of_closed_cut (in385_trap_graph p i) B hB hBu
    rintro b d ⟨hbd,x,rfl,rfl⟩
    have hxy : x≠in385_trap_mate i x := fun h => hbd (congrArg p h)
    exact hcl x (in385_trap_mate i x) ⟨hxy,in385_trap_mate_color i x⟩
  have hs : Fintype.card (in385_trap_graph p i).ConnectedComponent-1 ≤
      in385_trap_deficit p := by
    exact single_le_sum (f := fun j : Fin 15 =>
      Fintype.card (in385_trap_graph p j).ConnectedComponent-1)
      (fun j _ => Nat.zero_le _) (mem_univ i)
  exact (Nat.le_sub_one_of_lt hc).trans hs

theorem wild_partition_single_swap_deficit_obstruction :
    in385_trap_deficit in385_trap_block=1 ∧
    (∀ a b : Fin 15,1 ≤ in385_trap_deficit (in385_trap_swap_block a b)) ∧
    in385_trap_deficit in385_trap_repair_block=0 := by
  refine ⟨in385_trap_base_deficit,?_,?_⟩
  · intro a b
    obtain ⟨i,hi⟩ := wild_partition_single_swap_obstruction.2.2.2.2.2 a b
    exact in385_trap_deficit_pos_of_bad _ i hi
  · unfold in385_trap_deficit
    have he (i : Fin 15) : in385_trap_graph in385_trap_repair_block i = in385_trap_compact_graph true i :=
      in385_trap_compact_eq true i
    simp_rw [he,in385_trap_compact_connected_card true _ (Or.inl rfl)]
    simp
