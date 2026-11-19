import AFTD.Prelude

/-!
# required_edges_exhaust_low_ports

Topic: graphs   Node: 2fadb1cd6909

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

If a finite vertex set chooses one incident unordered pair per vertex and covers a set of required unordered pairs whose cardinality equals the number of vertices, every chosen pair is required.
-/

theorem required_edges_exhaust_low_ports
    {V : Type*} [Fintype V] [DecidableEq V]
    (required : Finset (Sym2 V)) (low : V → V)
    (hcard : required.card = Fintype.card V)
    (hcover : ∀ e ∈ required, ∃ v : V, s(v, low v) = e) :
    ∀ v : V, s(v, low v) ∈ required := by
  classical
  let selected : Finset (Sym2 V) := Finset.univ.image (fun v : V => s(v, low v))
  have hsub : required ⊆ selected := by
    intro e he
    obtain ⟨v, hv⟩ := hcover e he
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩
  have hsize : selected.card ≤ required.card := by
    calc
      selected.card ≤ (Finset.univ : Finset V).card := Finset.card_image_le
      _ = Fintype.card V := Finset.card_univ
      _ = required.card := hcard.symm
  have heq : required = selected := Finset.eq_of_subset_of_card_le hsub hsize
  intro v
  rw [heq]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
