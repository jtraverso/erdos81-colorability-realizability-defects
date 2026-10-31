/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Corollary to Theorem 7.3: the integral mixed copy inequality up to the rounding gap.

Theorem 7.3 has an exact fractional half (`Mixed.mixed_copy_fractional`, A1) and an integral half whose
error term is the weighted colorability defect (`mixed_copy_integral`, A2), which is not bounded by an
absolute constant. This file supplies the missing bridge from the fractional statement to the integral
one:

  * `Mixed.wNu_le_Wstar` — an integral mixed packing is a fractional one, so `W ≤ W*` (unconditional);
  * `Mixed.RoundingGap G gain B` — the hypothesis `W*(G) ≤ W(G) + B`, i.e. the integrality gap of the
    mixed packing LP on `G` is at most `B`;
  * `Mixed.mixed_copy_integral_of_roundingGap` — under that hypothesis,

        W(G_{v→u}) + W(G_{u→v}) ≤ 2 W(G) + 2 B.

The hypothesis is exactly what an `o(n²)` rounding theorem for the mixed `{K₃, K₄}` packing LP delivers
(with `B = ε n²`); nothing else about it is used here, so the corollary is an implication with no axiom
and no unproved premise inside this development.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.MixedCopyFrac

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open SimpleGraph Finset

namespace PaperV
namespace Mixed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `0/1` weighting of an integral packing. -/
noncomputable def indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (mixedCS G).O) : (mixedCS G).O → ℝ :=
  fun t => if t ∈ P then 1 else 0

/-- Two distinct members of a feasible mixed packing cannot both contain the pair `{a, b}`. -/
theorem unique_of_csFeasible (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (mixedCS G).O} (hP : CSFeasible (mixedCS G) P) {a b : V} (hab : a ≠ b) :
    ((Finset.univ.filter (fun t : (mixedCS G).O => a ∈ t.1 ∧ b ∈ t.1)).filter
      (fun t => t ∈ P)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro s hs t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  by_contra hne
  refine hP hs.2 ht.2 ⟨fun h => hne (Subtype.ext h), ?_⟩
  have hsub : ({a, b} : Finset V) ⊆ s.1 ∩ t.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hs.1.1, ht.1.1⟩
    · exact Finset.mem_inter.mpr ⟨hs.1.2, ht.1.2⟩
  have hcard : ({a, b} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
  calc 2 = ({a, b} : Finset V).card := hcard.symm
    _ ≤ (s.1 ∩ t.1).card := Finset.card_le_card hsub

/-- **An integral mixed packing is a fractional one.** -/
theorem isFracPacking_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (mixedCS G).O} (hP : CSFeasible (mixedCS G) P) :
    IsFracPacking G (indicator G P) := by
  classical
  refine ⟨fun t => by unfold indicator; split_ifs <;> norm_num, fun a b hab => ?_⟩
  unfold edgeLoad indicator
  rw [Finset.sum_boole]
  exact_mod_cast unique_of_csFeasible G hP hab

/-- The value of the indicator weighting is the gain of the packing. -/
theorem sum_indicator (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ)
    (P : Finset (mixedCS G).O) :
    ∑ t, (gain t.1.card : ℝ) * indicator G P t = ((packGain G gain P : ℕ) : ℝ) := by
  classical
  have h : ∀ t : (mixedCS G).O,
      (gain t.1.card : ℝ) * indicator G P t = if t ∈ P then (gain t.1.card : ℝ) else 0 := by
    intro t; unfold indicator; split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, packGain]
  push_cast
  rfl

/-- Mixed objects have at least two vertices. -/
theorem two_le_card_of_mixedP (G : SimpleGraph V) [DecidableRel G.Adj] (t : Finset V)
    (ht : mixedP G t) : 2 ≤ t.card := by
  rcases ht with h | h
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2]; norm_num
  · rw [(SimpleGraph.mem_cliqueFinset_iff.mp h).2]; norm_num

/-- **Integral is at most fractional:** `W(G) ≤ W*(G)` for the mixed system. -/
theorem wNu_le_Wstar (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ) :
    ((wNu (mixedCS G) (mixedWeight G gain) : ℕ) : ℝ) ≤ Wstar G gain := by
  classical
  obtain ⟨P, hP, hval⟩ := exists_wNu_witness (mixedCS G) (mixedWeight G gain)
  have hgain : ((packGain G gain P : ℕ) : ℝ) = ((wNu (mixedCS G) (mixedWeight G gain) : ℕ) : ℝ) := by
    have : packGain G gain P = ∑ o ∈ P, mixedWeight G gain o := rfl
    rw [this, hval]
  rw [← hgain, ← sum_indicator G gain P, Wstar_eq]
  exact FracCopy.total_le_Wstar (PG := mixedP G) (fun t => (gain t.card : ℝ))
    (fun t => Nat.cast_nonneg _) (two_le_card_of_mixedP G)
    (indicator G P) ((isFracPacking_iff G _).mp (isFracPacking_indicator G hP))

/-- **Rounding gap hypothesis.** The integrality gap of the mixed packing LP on `G` is at most `B`. -/
def RoundingGap (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ) (B : ℝ) : Prop :=
  Wstar G gain ≤ ((wNu (mixedCS G) (mixedWeight G gain) : ℕ) : ℝ) + B

/-- **Corollary to Theorem 7.3.** If the mixed packing LP on `G` has integrality gap at most `B`, the
integral mixed copy inequality holds with additive error `2B`:

  `W(G_{v→u}) + W(G_{u→v}) ≤ 2 W(G) + 2 B`.

For `B = ε n²` this is the asymptotic zero-defect form of the mixed copy inequality. -/
theorem mixed_copy_integral_of_roundingGap (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (gain : ℕ → ℕ) (B : ℝ) (hB : RoundingGap G gain B) :
    ((wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gain) : ℕ) : ℝ)
        + ((wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gain) : ℕ) : ℝ)
      ≤ 2 * ((wNu (mixedCS G) (mixedWeight G gain) : ℕ) : ℝ) + 2 * B := by
  have h1 := wNu_le_Wstar (copyGraph G v u) gain
  have h2 := wNu_le_Wstar (copyGraph G u v) gain
  have h3 := mixed_copy_fractional G v u huv gain
  unfold RoundingGap at hB
  linarith

/-- The zero-gap case: an exact integral mixed copy inequality on graphs whose mixed packing LP is
integral. -/
theorem mixed_copy_integral_of_integral_lp (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (huv : ¬ G.Adj u v) (gain : ℕ → ℕ) (hB : RoundingGap G gain 0) :
    ((wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gain) : ℕ) : ℝ)
        + ((wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gain) : ℕ) : ℝ)
      ≤ 2 * ((wNu (mixedCS G) (mixedWeight G gain) : ℕ) : ℝ) := by
  have h := mixed_copy_integral_of_roundingGap G v u huv gain 0 hB
  linarith

end Mixed
end PaperV
