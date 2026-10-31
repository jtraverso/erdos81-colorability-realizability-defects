/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Theorem A, fractional part (A1): weighted fractional copy inequality for the mixed {K₃, K₄} family.

  W*(G_{v→u}) + W*(G_{u→v}) ≤ 2 · W*(G),

where `W*` is the fractional weighted packing number of the mixed system (`mixedCS`: cliques of size 3 or 4,
edge-load ≤ 1 on every pair, objective `Σ gain(|t|) · y(t)`). Since 2026-09-14 the proof is the instance
`P := (· ∈ G.cliqueFinset 3 ∨ · ∈ G.cliqueFinset 4)`, weight `gain ∘ card`, of the generic total-map edge-load
argument `FracCopy.copy_fractional_generic` (`FracCopyGeneric.lean`, shared with Theorem 4.1); the weight is
preserved by the copy relabelling because it preserves the clique size (`card_imgObj`). Together with
`mixed_copy_integral` (A2) this completes Theorem A. Definitions and the statement are unchanged.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.MixedCopy
public import PaperV.FracCopyGeneric

import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum

@[expose] public section

open SimpleGraph Finset

namespace PaperV
namespace Mixed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge-load of a weighting of the mixed cliques at the pair `{a, b}`. -/
noncomputable def edgeLoad (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : (mixedCS G).O → ℝ) (a b : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : (mixedCS G).O => a ∈ t.1 ∧ b ∈ t.1), y t

/-- A fractional mixed packing: nonnegative weights with edge-load at most 1 on every pair. -/
def IsFracPacking (G : SimpleGraph V) [DecidableRel G.Adj] (y : (mixedCS G).O → ℝ) : Prop :=
  (∀ t, 0 ≤ y t) ∧ (∀ a b : V, a ≠ b → edgeLoad G y a b ≤ 1)

/-- The fractional weighted packing number `W*(G)` for the size-dependent gain. -/
noncomputable def Wstar (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ) : ℝ :=
  sSup { s : ℝ | ∃ y : (mixedCS G).O → ℝ, IsFracPacking G y ∧ s = ∑ t, (gain t.1.card : ℝ) * y t }

/-- The mixed family as a predicate. -/
abbrev mixedP (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V → Prop :=
  fun t => t ∈ G.cliqueFinset 3 ∨ t ∈ G.cliqueFinset 4

theorem isFracPacking_iff (G : SimpleGraph V) [DecidableRel G.Adj] (y : (mixedCS G).O → ℝ) :
    IsFracPacking G y ↔ FracCopy.IsFracPacking (P := mixedP G) y := by
  unfold IsFracPacking FracCopy.IsFracPacking edgeLoad FracCopy.edgeLoad
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a b hab => ?_⟩
    convert h2 a b hab using 3 <;> apply Subsingleton.elim
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a b hab => ?_⟩
    convert h2 a b hab using 3 <;> apply Subsingleton.elim

/-- `W*` is the generic `W*` of the mixed family with weight `gain ∘ card`. -/
theorem Wstar_eq (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ) :
    Wstar G gain = FracCopy.Wstar (mixedP G) (fun t => (gain t.card : ℝ)) := by
  unfold Wstar FracCopy.Wstar
  congr 1

theorem card_copyMap_of_mixed (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (t : Finset V) (ht : mixedP (copyGraph G v u) t) : (copyMap v u t).card = t.card := by
  rcases ht with h | h
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2,
      (SimpleGraph.mem_cliqueFinset_iff.mp (copyMap_mem_cliqueFinset G v u huv 3 t h)).2]
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2,
      (SimpleGraph.mem_cliqueFinset_iff.mp (copyMap_mem_cliqueFinset G v u huv 4 t h)).2]

/-- **Theorem A1 (fractional weighted copy inequality for the mixed family).** -/
theorem mixed_copy_fractional (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v)
    (gain : ℕ → ℕ) :
    Wstar (copyGraph G v u) gain + Wstar (copyGraph G u v) gain ≤ 2 * Wstar G gain := by
  have hvu : ¬ G.Adj v u := fun h => huv h.symm
  rw [Wstar_eq, Wstar_eq, Wstar_eq]
  refine FracCopy.copy_fractional_generic v u (fun t => (gain t.card : ℝ))
    (fun t => show (0 : ℝ) ≤ ((gain t.card : ℕ) : ℝ) from Nat.cast_nonneg _)
    (fun t ht => ht.elim (fun h => Or.inl (copyMap_mem_cliqueFinset G v u huv 3 t h))
      (fun h => Or.inr (copyMap_mem_cliqueFinset G v u huv 4 t h)))
    (fun t ht => ht.elim (fun h => Or.inl (copyMap_mem_cliqueFinset G u v hvu 3 t h))
      (fun h => Or.inr (copyMap_mem_cliqueFinset G u v hvu 4 t h)))
    (fun t ht => show ((gain (copyMap v u t).card : ℕ) : ℝ) = gain t.card by
      rw [card_copyMap_of_mixed G v u huv t ht])
    (fun t ht => show ((gain (copyMap u v t).card : ℕ) : ℝ) = gain t.card by
      rw [card_copyMap_of_mixed G u v hvu t ht]) ?_
  intro t ht
  rcases ht with h | h
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2]; norm_num
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2]; norm_num

end Mixed
end PaperV
