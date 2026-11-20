import AFTD.Prelude
import AFTD.Kb.Tcs.Op309EightVertexWeightedPortCatalogKernel

/-!
# op309_eight_vertex_weighted_catalog_complete

Topic: combinatorics   Node: 8aa18093c39e

Provenance: helper lemma. OP-309 weighted incidence peeling obstruction, IN-1099.

The finite block catalog matches all simple two- and three-edge paths and three-edge stars in the displayed graph, and its local pairing options agree with the explicitly computed port templates.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace In1099Weighted
def originalEdges : List (Nat × Nat) :=
  [(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,5),(2,6),(2,7),(3,6),(3,7),(4,7)]

def edgeIndex (a b : Nat) : Option Nat :=
  (List.range 12).find? fun i =>
    let e := originalEdges[i]!
    ((e.1 == a) && (e.2 == b)) || ((e.1 == b) && (e.2 == a))

def pathSignature (vs : List Nat) : Option (List Nat × List Nat × Bool) := do
  if vs.eraseDups.length != vs.length then none else
  match vs with
  | [a,b,c] =>
    if !(a < c) then none else do
      let x ← edgeIndex a b
      let y ← edgeIndex b c
      let es := (List.range 12).filter fun i => i == x || i == y
      some (vs,es,false)
  | [a,b,c,d] =>
    if !(a < d) then none else do
      let x ← edgeIndex a b
      let y ← edgeIndex b c
      let z ← edgeIndex c d
      let es := (List.range 12).filter fun i => i == x || i == y || i == z
      some (vs,es,true)
  | _ => none

def generatedPaths3 : List (List Nat × List Nat × Bool) :=
  (List.range 8).flatMap fun a =>
  (List.range 8).flatMap fun b =>
  (List.range 8).filterMap fun c => pathSignature [a,b,c]

def generatedPaths4 : List (List Nat × List Nat × Bool) :=
  (List.range 8).flatMap fun a =>
  (List.range 8).flatMap fun b =>
  (List.range 8).flatMap fun c =>
  (List.range 8).filterMap fun d => pathSignature [a,b,c,d]

def generatedStars : List (List Nat × List Nat × Bool) :=
  (List.range 8).map fun v =>
    let ns := (List.range 8).filter fun w => (edgeIndex v w).isSome
    let es := incident[v]!
    (v::ns,es,false)

def generatedSignatures : List (List Nat × List Nat × Bool) :=
  generatedPaths3 ++ generatedPaths4 ++ generatedStars

def catalogSignatures : List (List Nat × List Nat × Bool) :=
  catalog.map fun b => (b.vertices,b.edges,b.long)


def ports (b : Block) (v : Nat) : List Nat := (incident[v]!).filter fun e => !(b.edges.contains e)

def expectedOptions (b : Block) : List Opt :=
  match b.vertices with
  | [a,mid,c] =>
    let A := ports b a
    let B := ports b mid
    let C := ports b c
    [⟨[(A[0]!,C[0]!), (A[1]!,C[1]!)], [B[0]!,A[0]!,A[1]!]⟩,
     ⟨[(A[0]!,C[1]!), (A[1]!,C[0]!)], [B[0]!,A[0]!,A[1]!]⟩]
  | [a,mid1,mid2,d] =>
    if b.long then
      let A := ports b a
      let B := ports b mid1
      let C := ports b mid2
      let D := ports b d
      (List.range 2).flatMap fun ai => (List.range 2).map fun di =>
        ⟨[(A[ai]!,C[0]!), (D[di]!,B[0]!)], [B[0]!,C[0]!,A[1-ai]!,D[1-di]!]⟩
    else
      let A := ports b mid1
      let B := ports b mid2
      let C := ports b d
      (List.range 2).flatMap fun rb => (List.range 2).map fun rc =>
        let bb := if rb = 1 then B.reverse else B
        let cc := if rc = 1 then C.reverse else C
        ⟨[(A[0]!,bb[0]!), (A[1]!,bb[1]!), (A[0]!,cc[0]!), (A[1]!,cc[1]!)],A⟩
  | _ => []

theorem incident_correct : (List.range 8).all (fun v => incident[v]! =
    (List.range 12).filter (fun i => let e := originalEdges[i]!; e.1 == v || e.2 == v)) = true := by decide

theorem edge_adj_correct : (List.range 12).all (fun i => edgeAdj[i]! =
    (List.range 12).filter (fun j => i != j &&
      ((incident[(originalEdges[i]!).1]!).contains j || (incident[(originalEdges[i]!).2]!).contains j))) = true := by decide

theorem catalog_sound : catalogSignatures.all (fun s => generatedSignatures.contains s) = true := by decide

theorem catalog_complete : generatedSignatures.all (fun s => catalogSignatures.contains s) = true := by decide

theorem options_correct : catalog.all (fun b => b.options == expectedOptions b) = true := by decide
end In1099Weighted

theorem op309_eight_vertex_weighted_catalog_complete :
  (In1099Weighted.generatedSignatures.all (fun s => In1099Weighted.catalogSignatures.contains s) = true) ∧
  (In1099Weighted.catalogSignatures.all (fun s => In1099Weighted.generatedSignatures.contains s) = true) ∧
  (In1099Weighted.catalog.all (fun b => b.options == In1099Weighted.expectedOptions b) = true) := by exact ⟨In1099Weighted.catalog_complete, In1099Weighted.catalog_sound, In1099Weighted.options_correct⟩
