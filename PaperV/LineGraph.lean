/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Tuza–Vizing (line-graph) interface, Tier 1 (v0.9.15 candidate).

The structural, Vizing-free core of the line-graph specialization (see `../ROUTE_TUZA_VIZING.md`).
For a SIMPLE graph `G`, a set of edges is independent in the line graph `L(G)` exactly when its
edges are pairwise vertex-disjoint — i.e. it is a matching. Instantiating the cover-defect corollary
`cover_defect_lower` (Cor 3.2a) at `H := L(G)` then reads the splitting principle in matching /
edge-colouring language: `|E(G)| − 2·(matching size) ≤ oct(L(G))`.

Blocked, hence NOT here (Mathlib gaps, → manuscript): chromatic index `χ'`, Vizing's theorem, and the
multigraph `M_C` with parallel edges (Mathlib's `lineGraph` is for simple graphs). See the route doc.
-/
module

public import PaperV.Core
public import PaperV.CoverDefect
public import PaperV.SplittingQ
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **L1 — independent sets of the line graph are matchings.** A set `S` of edges of `G` is feasible
(independent) in `L(G)` iff its edges are pairwise vertex-disjoint. Immediate from `lineGraph.Adj`
(two distinct edges are adjacent in `L(G)` exactly when they share a vertex). -/
theorem feasible_lineGraph_iff (G : SimpleGraph V) (S : Finset ↑G.edgeSet) :
    Feasible (G.lineGraph) S ↔
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (↑(↑e : Sym2 V) : Set V) ↑(↑f : Sym2 V) := by
  constructor
  · intro h e he f hf hef
    have hna : ¬ (G.lineGraph).Adj e f := h he hf
    have hiff : (G.lineGraph).Adj e f ↔
        e ≠ f ∧ ((↑(↑e : Sym2 V) : Set V) ∩ ↑(↑f : Sym2 V)).Nonempty := Iff.rfl
    rw [hiff] at hna
    push_neg at hna
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hna hef
  · intro h a ha b hb hadj
    have hc : a ≠ b ∧ ((↑(↑a : Sym2 V) : Set V) ∩ ↑(↑b : Sym2 V)).Nonempty := hadj
    obtain ⟨hab, hnon⟩ := hc
    have hdis := h a ha b hb hab
    rw [Set.disjoint_iff_inter_eq_empty] at hdis
    rw [hdis] at hnon
    exact Set.not_nonempty_empty hnon

/-- **L3 — colourings of `L(G)` are proper edge-colourings of `G`.** `L(G)` is `q`-colourable iff `G`
admits a `q`-colouring of its edges in which any two edges sharing a vertex get different colours
(a proper edge-`q`-colouring). Hence `D_q(L(G))` is exactly the edge-colouring defect of `G`. -/
theorem colorable_lineGraph_iff_edge (G : SimpleGraph V) (q : ℕ) :
    (G.lineGraph).Colorable q ↔
      ∃ c : ↑G.edgeSet → Fin q, ∀ e f : ↑G.edgeSet,
        e ≠ f → ((↑(↑e : Sym2 V) : Set V) ∩ ↑(↑f : Sym2 V)).Nonempty → c e ≠ c f := by
  constructor
  · rintro ⟨C⟩
    refine ⟨fun e => C e, fun e f hef hsh => ?_⟩
    exact C.valid (show (G.lineGraph).Adj e f from ⟨hef, hsh⟩)
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c (fun {e f} hadj => hc e f hadj.1 hadj.2)⟩

/-- **L2 — matching form of the cover defect (Cor 3.2a on the line graph).** There is a feasible set
of edges (a matching, by `feasible_lineGraph_iff`) `S` with `|E(G)| − 2|S| ≤ oct(L(G))`. Vizing-free
instance of `cover_defect_lower` at `H := L(G)`: it ties the matching number of `G` to the
odd-cycle-transversal number of its line graph. -/
theorem lineGraph_matching_defect (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset ↑G.edgeSet, Feasible (G.lineGraph) S ∧
      @Fintype.card ↑G.edgeSet G.fintypeEdgeSet - 2 * S.card ≤ oct (G.lineGraph) := by
  classical
  exact cover_defect_lower (G.lineGraph)

/-- **L2′ — `q`-form (ceiling) matching defect.** There is a matching `S` of `G` with
`⌈(|E(G)| − D_q(L(G)))/q⌉ ≤ |S|`, where `D_q(L(G))` is the minimum number of edges to delete from `G`
to make it properly `q`-edge-colourable (the edge-colouring defect). Vizing-free instance of
`SplittingQ.splitting_ceil` at `H := L(G)`. -/
theorem lineGraph_matching_defect_q (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq : 1 ≤ q) :
    ∃ S : Finset ↑G.edgeSet, Feasible (G.lineGraph) S ∧
      (@Fintype.card ↑G.edgeSet G.fintypeEdgeSet - Dq (G.lineGraph) q + (q - 1)) / q ≤ S.card := by
  classical
  exact SplittingQ.splitting_ceil (G.lineGraph) q hq

/-! ### Tier 2 — multigraph line graph (handles parallel edges of `M_C`)

Mathlib's `lineGraph` is defined for simple graphs. The private-witness graph `H[X_C] ≅ L(M_C)` needs
`M_C` to be a MULTIGRAPH on `B = E(G)∖C` (parallel labelled edges). We model a multigraph directly by
its incidence map `ends : E → Sym2 B` (edge labels `E`; a parallel pair is two labels with equal ends)
and define its line graph as a `SimpleGraph E`. This strictly generalises `SimpleGraph.lineGraph`
(`lineGraph_eq_multiLineGraph`), so the matching/edge-colouring corollaries carry over verbatim. -/

section Multigraph
variable {B W : Type*}

/-- Line graph of a MULTIGRAPH given by an incidence map `ends : W → Sym2 B` (edge labels `W`,
parallel edges = distinct labels with equal ends). Two labels are adjacent iff distinct and sharing a
vertex. Generalises `SimpleGraph.lineGraph` (labels = the edge set). -/
def multiLineGraph (ends : W → Sym2 B) : SimpleGraph W where
  Adj e f := e ≠ f ∧ ((↑(ends e) : Set B) ∩ ↑(ends f)).Nonempty
  symm := ⟨fun e f ⟨hef, hnon⟩ => ⟨hef.symm, by rwa [Set.inter_comm]⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

/-- Mathlib's simple-graph line graph is the special case with labels = the edge set. -/
theorem lineGraph_eq_multiLineGraph {V : Type*} (G : SimpleGraph V) :
    G.lineGraph = multiLineGraph (fun e : ↑G.edgeSet => (↑e : Sym2 V)) := rfl

variable [Fintype W] [DecidableEq W]

/-- Independent sets of `L(M)` are matchings of the multigraph `M`: no two chosen edges share a
vertex (parallel edges, sharing both ends, are adjacent, so at most one is chosen). -/
theorem feasible_multiLineGraph_iff (ends : W → Sym2 B) (S : Finset W) :
    Feasible (multiLineGraph ends) S ↔
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (↑(ends e) : Set B) ↑(ends f) := by
  constructor
  · intro h e he f hf hef
    have hna : ¬ (multiLineGraph ends).Adj e f := h he hf
    have hiff : (multiLineGraph ends).Adj e f ↔
        e ≠ f ∧ ((↑(ends e) : Set B) ∩ ↑(ends f)).Nonempty := Iff.rfl
    rw [hiff] at hna
    push_neg at hna
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hna hef
  · intro h a ha b hb hadj
    have hc : a ≠ b ∧ ((↑(ends a) : Set B) ∩ ↑(ends b)).Nonempty := hadj
    obtain ⟨hab, hnon⟩ := hc
    have hdis := h a ha b hb hab
    rw [Set.disjoint_iff_inter_eq_empty] at hdis
    rw [hdis] at hnon
    exact Set.not_nonempty_empty hnon

/-- **Multigraph matching defect (Tier 2, `M_C` case).** `|E(M)| − 2·|matching| ≤ oct(L(M))` for a
multigraph `M = (B, ends)` with parallel edges. Instance of `cover_defect_lower` at `H := L(M)` —
the parallel-edge-aware form of the Tuza–Vizing interface. -/
theorem multiLineGraph_matching_defect (ends : W → Sym2 B) :
    ∃ S : Finset W, Feasible (multiLineGraph ends) S ∧
      Fintype.card W - 2 * S.card ≤ oct (multiLineGraph ends) := by
  classical
  exact cover_defect_lower (multiLineGraph ends)

/-- **Multigraph matching defect, ceiling `q`-form.** `⌈(|E(M)| − D_q(L(M)))/q⌉ ≤ |matching|`, with
`D_q(L(M))` the `q`-edge-colouring defect of the multigraph `M`. Instance of `SplittingQ.splitting_ceil`
at `H := L(M)`. -/
theorem multiLineGraph_matching_defect_q (ends : W → Sym2 B) {q : ℕ} (hq : 1 ≤ q) :
    ∃ S : Finset W, Feasible (multiLineGraph ends) S ∧
      (Fintype.card W - Dq (multiLineGraph ends) q + (q - 1)) / q ≤ S.card := by
  classical
  exact SplittingQ.splitting_ceil (multiLineGraph ends) q hq

end Multigraph

end PaperV
