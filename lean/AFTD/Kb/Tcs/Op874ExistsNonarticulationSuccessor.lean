import AFTD.Prelude

/-!
# op874_exists_nonarticulation_successor

Topic: graphs   Node: 3bbacca5bbe4

Provenance: helper lemma. Finite connected undirected graph has a non-articulation vertex; choose a predecessor.

Every nonempty finite strongly connected loopless two-in/two-out directed multigraph has an arc to a vertex whose deletion leaves the underlying undirected graph connected.
-/

theorem op874_exists_nonarticulation_successor {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p q : Equiv.Perm X) (hfixed : ∀ x, p x ≠ x ∧ q x ≠ x)
    (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v) :
    ∃ r x : X, (p r = x ∨ q r = x) ∧
      (∀ u v, u ≠ x → v ≠ x → Relation.ReflTransGen
        (fun a b => a ≠ x ∧ b ≠ x ∧ (p a = b ∨ q a = b ∨ p b = a ∨ q b = a)) u v) := by
  classical
  let G : SimpleGraph X := {
    Adj := fun u v => p u = v ∨ q u = v ∨ p v = u ∨ q v = u
    symm := ⟨by intro u v h; tauto⟩
    loopless := ⟨by intro u h; rcases h with h | h | h | h <;> exact (by first | exact (hfixed u).1 h | exact (hfixed u).2 h)⟩
  }
  have walk (u : X) (w : List Bool) : Relation.ReflTransGen G.Adj u (w.foldl (fun x bit => if bit then p x else q x) u) := by
    induction w generalizing u with
    | nil => exact Relation.ReflTransGen.refl
    | cons b w ih =>
      simp only [List.foldl_cons]
      apply Relation.ReflTransGen.head _ (ih _)
      cases b <;> simp [G]
  have hg : G.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
    obtain ⟨u⟩ := ‹Nonempty X›
    refine ⟨u, ?_⟩
    intro v
    obtain ⟨w, hw⟩ := hstrong u v
    apply (SimpleGraph.reachable_iff_reflTransGen u v).mpr
    simpa [hw] using walk u w
  obtain ⟨u⟩ := ‹Nonempty X›
  letI : Nontrivial X := ⟨⟨p u, u, (hfixed u).1⟩⟩
  obtain ⟨x, hx⟩ := hg.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨p.symm x, x, Or.inl (p.apply_symm_apply x), ?_⟩
  intro a b ha hb
  let a' : {z // z ∈ ({x} : Set X)ᶜ} := ⟨a, by simpa using ha⟩
  let b' : {z // z ∈ ({x} : Set X)ᶜ} := ⟨b, by simpa using hb⟩
  have hwalk : Relation.ReflTransGen (G.induce ({x} : Set X)ᶜ).Adj a' b' :=
    (SimpleGraph.reachable_iff_reflTransGen a' b').mp (hx a' b')
  apply Relation.ReflTransGen.lift (fun z : {z // z ∈ ({x} : Set X)ᶜ} => z.val)
    (p := fun a b => a ≠ x ∧ b ≠ x ∧ (p a = b ∨ q a = b ∨ p b = a ∨ q b = a)) ?_ a' b' hwalk
  intro u v huv
  have hu : (u : X) ∉ ({x} : Set X) := u.property
  have hv : (v : X) ∉ ({x} : Set X) := v.property
  exact ⟨fun h => hu (Set.mem_singleton_iff.mpr h),
    fun h => hv (Set.mem_singleton_iff.mpr h), by simpa [G] using huv⟩
