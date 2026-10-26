import AFTD.Prelude

/-!
# is_distance_hereditary

Topic: graphs   Node: e41b83eb94eb

Provenance: formalization of a published result. Source: Howarka 1977; Brandstädt, Le, Spinrad 1999

A graph F is distance-hereditary if for every induced subgraph and any two vertices reachable within it, their distance in the induced subgraph equals their distance in F.
-/

/-- A graph is distance-hereditary if every connected induced subgraph is isometric. -/
def is_distance_hereditary {α : Type*} (F : SimpleGraph α) : Prop := ∀ (s : Set α) (u v : s), (F.induce s).Reachable u v → (F.induce s).dist u v = F.dist u.1 v.1
