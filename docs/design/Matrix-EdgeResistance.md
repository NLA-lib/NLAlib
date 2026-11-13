# Weighted incidence and edge resistance

The input to resistance sampling is an edge-indexed matrix, including when a
graph is disconnected or the same pair of vertices has several edge records.
`Matrix/Structured/EdgeResistance.lean` therefore takes an orientation of the
edge records of a Mathlib `SimpleGraph V`. Its constructor takes source and
target maps, an adjacency proof for each record, and coverage of each adjacency
in either orientation. The record type can be empty.

The signed incidence row is the difference of the two endpoint indicators.
The weighted row is its multiple by the square root of the edge weight.
Mathlib's `SimpleGraph.incMatrix` is unsigned. Its ordinary Laplacian does
supply the kernel dimension needed for positive weights: the kernel of the
weighted incidence consists of exactly the vectors constant along adjacent pairs.
The proof identifies this kernel with that of `SimpleGraph.lapMatrix`, then
applies rank-nullity. It does not require a new theory of connected components.

For `o : GraphEdgeOrientation G E`, `w : E → ℝ` and `e : E`, the main statements are

```lean
w e * o.edgeResistance w e = leverageScore (o.weightedIncidence w) e
(o.weightedLaplacian w).rank + Nat.card G.ConnectedComponent = Fintype.card V
∑ e, w e * o.edgeResistance w e = ((o.weightedLaplacian w).rank : ℝ)
```

The first equality assumes a nonnegative weight at the chosen edge, and the
last equality assumes all weights are nonnegative. Only the graph rank formula
requires positive weights on all records. This distinguishes the zero-weight and
isolated-vertex cases. The existing Gram-pseudoinverse projector identity and
leverage score range and trace facts supply the matrix parts of the atlas card.
The source is Spielman and Srivastava, *Graph Sparsification by Effective Resistances*,
§2. The original atlas uses its own proof of the kernel dimension and a second
real-matrix projector identity. Neither is needed by the resistance API.

## Explorer entries

The original atlas card `laplacian-resistance-leverage` includes the edgewise equality,
its sum over the edge records, and the rank of the weighted Laplacian. In the explorer
the edgewise equality keeps that ID. Foster’s identity has ID `foster-theorem` and
uses the edgewise equality inside the sum. The connected-component identity has ID
`weighted-laplacian-rank` and assumes strictly positive weights.
