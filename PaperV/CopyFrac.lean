/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — §4.1, Theorem 4.1 (fractional copy inequality, zero defect). Ledger node L-4.

  ν₃*(G_{v→u}) + ν₃*(G_{u→v}) ≤ 2 ν₃*(G).

ν₃* is the fractional triangle-packing number: max total weight of a nonneg weighting of the
triangles with edge-load ≤ 1 on every edge. Since 2026-09-14 the proof is the instance `P := (· ∈ G.cliqueFinset 3)`,
unit weights, of the generic total-map edge-load argument `FracCopy.copy_fractional_generic`
(`FracCopyGeneric.lean`, shared with the mixed family of Theorem A1). The definitions and the statement of
`copy_fractional` are unchanged.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.FracCopyGeneric

import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge-load of a nonneg triangle-weighting `y` at the (unordered) pair `{a,b}`: the total
weight of triangles that contain both `a` and `b`. -/
noncomputable def edgeLoad (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : (triCS G).O → ℝ) (a b : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : (triCS G).O => a ∈ t.1 ∧ b ∈ t.1), y t

/-- A fractional triangle packing: nonnegative weights with edge-load at most 1 everywhere. -/
def IsFracPacking (G : SimpleGraph V) [DecidableRel G.Adj] (y : (triCS G).O → ℝ) : Prop :=
  (∀ t, 0 ≤ y t) ∧ (∀ a b : V, a ≠ b → edgeLoad G y a b ≤ 1)

/-- The fractional triangle-packing number `ν₃*(G)`. -/
noncomputable def nu3star (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { s : ℝ | ∃ y : (triCS G).O → ℝ, IsFracPacking G y ∧ s = ∑ t, y t }

/-- The triangle family as a predicate. -/
abbrev triP (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V → Prop := fun t => t ∈ G.cliqueFinset 3

theorem edgeLoad_eq (G : SimpleGraph V) [DecidableRel G.Adj] (y : (triCS G).O → ℝ) (a b : V) :
    edgeLoad G y a b = FracCopy.edgeLoad (P := triP G) y a b := by
  unfold edgeLoad FracCopy.edgeLoad
  congr 1
  ext t
  simp

theorem isFracPacking_iff (G : SimpleGraph V) [DecidableRel G.Adj] (y : (triCS G).O → ℝ) :
    IsFracPacking G y ↔ FracCopy.IsFracPacking (P := triP G) y := by
  unfold IsFracPacking FracCopy.IsFracPacking
  simp only [edgeLoad_eq]

/-- `ν₃*` is the generic `W*` of the triangle family with unit weights. -/
theorem nu3star_eq_Wstar (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G = FracCopy.Wstar (triP G) (fun _ => 1) := by
  unfold nu3star FracCopy.Wstar
  congr 1
  ext s
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (isFracPacking_iff G y).mp hy,
      Finset.sum_congr (by ext t; simp) (fun t _ => by simp)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (isFracPacking_iff G y).mpr hy,
      Finset.sum_congr (by ext t; simp) (fun t _ => by simp)⟩

/-- **Theorem 4.1 (fractional copy inequality, zero defect).** -/
theorem copy_fractional (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) :
    nu3star (copyGraph G v u) + nu3star (copyGraph G u v) ≤ 2 * nu3star G := by
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  rw [nu3star_eq_Wstar, nu3star_eq_Wstar, nu3star_eq_Wstar]
  refine FracCopy.copy_fractional_generic v u (fun _ => 1) (fun _ => zero_le_one)
    (fun t ht => copyMap_mem_triangles G v u huv t ht) (fun t ht => copyMap_mem_triangles G u v hvu t ht)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_
  intro t ht
  rw [(SimpleGraph.mem_cliqueFinset_iff.mp ht).2]
  norm_num

end PaperV
