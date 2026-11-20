import AFTD.Prelude
import AFTD.Kb.Tcs.BinTree

/-!
# TreeRotation

Topic: graphs   Node: 280cb52f4842

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The inductive relation TreeRotation on BinTree relating two trees that differ by a single rotation: rotating right at the root replacing ((U, V), W) by (U, (V, W)), rotating left at the root replacing (U, (V, W)) by ((U, V), W), or rotating recursively in the left child or the right child.
-/

/-- Single tree rotation relation on ordered full binary trees. -/
inductive TreeRotation : BinTree → BinTree → Prop | rot_right (U V W : BinTree) :
      TreeRotation (BinTree.node (BinTree.node U V) W) (BinTree.node U (BinTree.node V W))
  | rot_left (U V W : BinTree) :
      TreeRotation (BinTree.node U (BinTree.node V W)) (BinTree.node (BinTree.node U V) W)
  | node_left {l l' r : BinTree} (h : TreeRotation l l') :
      TreeRotation (BinTree.node l r) (BinTree.node l' r)
  | node_right {l r r' : BinTree} (h : TreeRotation r r') :
      TreeRotation (BinTree.node l r) (BinTree.node l r')
