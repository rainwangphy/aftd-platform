import AFTD.Prelude
import AFTD.Kb.Tcs.IsThreeUniform
import AFTD.Kb.Tcs.IsFanoFree
import AFTD.Kb.Tcs.FanoPlane

/-!
# fano_free_local_forbidden

Topic: combinatorics   Node: 8d5836f45ea1

Provenance: formalization of a published result. Source: arXiv:2610.01084 Lemma 3.1 inequality (3.1)

In any 3-uniform Fano-free hypergraph H : Finset (Finset V), if {x, y, z} is an edge of H, then for all vertices a, b, c, d in V, the six triples {x, a, b}, {x, c, d}, {y, a, c}, {y, b, d}, {z, a, d}, and {z, b, c} cannot all belong to H.
-/

private lemma fano_free_local_forbidden_card_three {V : Type*} [DecidableEq V] {p q r : V}
    (h : ({p,q,r} : Finset V).card = 3) : p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have he : ({p,q,r} : Finset V) = {p,r} := by rw [heq]; simp
    have h1 : ({p,r} : Finset V).card = 3 := he ▸ h
    have h2 : ({p,r} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  · intro heq
    have he : ({p,q,r} : Finset V) = {q,r} := by rw [heq]; simp
    have h1 : ({q,r} : Finset V).card = 3 := he ▸ h
    have h2 : ({q,r} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  · intro heq
    have he : ({p,q,r} : Finset V) = {p,q} := by rw [heq]; simp
    have h1 : ({p,q} : Finset V).card = 3 := he ▸ h
    have h2 : ({p,q} : Finset V).card ≤ 2 := Finset.card_le_two
    omega

private lemma fano_free_local_forbidden_injective {V : Type*} [DecidableEq V]
    (x y z a b c d : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) (hcd : c ≠ d)
    (hya : y ≠ a) (hyc : y ≠ c) (hac : a ≠ c)
    (hyb : y ≠ b) (hyd : y ≠ d) (hbd : b ≠ d)
    (hza : z ≠ a) (hzd : z ≠ d) (had : a ≠ d)
    (hzb : z ≠ b) (hzc : z ≠ c) (hbc : b ≠ c) :
    Function.Injective (![x, y, z, a, b, c, d] : Fin 7 → V) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin.ext_iff]

private lemma fano_free_local_forbidden_map_012 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({0,1,2} : Finset (Fin 7)) = ({x,y,z} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_034 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({0,3,4} : Finset (Fin 7)) = ({x,a,b} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_056 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({0,5,6} : Finset (Fin 7)) = ({x,c,d} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_135 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({1,3,5} : Finset (Fin 7)) = ({y,a,c} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_146 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({1,4,6} : Finset (Fin 7)) = ({y,b,d} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_236 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({2,3,6} : Finset (Fin 7)) = ({z,a,d} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

private lemma fano_free_local_forbidden_map_245 {V : Type*} [DecidableEq V] (x y z a b c d : V)
    (h : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V)) :
    Finset.map ⟨![x,y,z,a,b,c,d], h⟩ ({2,4,5} : Finset (Fin 7)) = ({z,b,c} : Finset V) := by
  rw [Finset.map_eq_image]; simp [Finset.image]

/-- Local forbidden constraint for Fano-free 3-graphs: no edge {x,y,z} can have six companion edges forming a Fano plane. -/
theorem fano_free_local_forbidden {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (hunif : is_three_uniform H) (hfree : is_fano_free H)
    (x y z a b c d : V) (hxyz : {x, y, z} ∈ H) :
    ¬ ({x, a, b} ∈ H ∧ {x, c, d} ∈ H ∧ {y, a, c} ∈ H ∧ {y, b, d} ∈ H ∧ {z, a, d} ∈ H ∧ {z, b, c} ∈ H) := by
  rintro ⟨hxab, hxcd, hyac, hybd, hzad, hzbc⟩
  obtain ⟨hxy, hxz, hyz⟩ := fano_free_local_forbidden_card_three (hunif {x,y,z} hxyz)
  obtain ⟨hxa, hxb, hab⟩ := fano_free_local_forbidden_card_three (hunif {x,a,b} hxab)
  obtain ⟨hxc, hxd, hcd⟩ := fano_free_local_forbidden_card_three (hunif {x,c,d} hxcd)
  obtain ⟨hya, hyc, hac⟩ := fano_free_local_forbidden_card_three (hunif {y,a,c} hyac)
  obtain ⟨hyb, hyd, hbd⟩ := fano_free_local_forbidden_card_three (hunif {y,b,d} hybd)
  obtain ⟨hza, hzd, had⟩ := fano_free_local_forbidden_card_three (hunif {z,a,d} hzad)
  obtain ⟨hzb, hzc, hbc⟩ := fano_free_local_forbidden_card_three (hunif {z,b,c} hzbc)
  apply hfree
  have hinj : Function.Injective (![x,y,z,a,b,c,d] : Fin 7 → V) :=
    fano_free_local_forbidden_injective x y z a b c d
      hxy hxz hyz hxa hxb hab hxc hxd hcd hya hyc hac hyb hyd hbd hza hzd had hzb hzc hbc
  refine ⟨⟨![x,y,z,a,b,c,d], hinj⟩, ?_⟩
  intro e he
  simp only [fano_plane, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fano_free_local_forbidden_map_012 x y z a b c d hinj]; exact hxyz
  · rw [fano_free_local_forbidden_map_034 x y z a b c d hinj]; exact hxab
  · rw [fano_free_local_forbidden_map_056 x y z a b c d hinj]; exact hxcd
  · rw [fano_free_local_forbidden_map_135 x y z a b c d hinj]; exact hyac
  · rw [fano_free_local_forbidden_map_146 x y z a b c d hinj]; exact hybd
  · rw [fano_free_local_forbidden_map_236 x y z a b c d hinj]; exact hzad
  · rw [fano_free_local_forbidden_map_245 x y z a b c d hinj]; exact hzbc
