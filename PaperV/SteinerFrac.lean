/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Remark C1r, layer 4: optimality in the FULL fractional LP (real weights).

`frac_packing_bound`: for any weighting `x : triangles → K` (K an ordered field) with edge-load
`Σ_{t ∋ e} x t ≤ 1` on every edge, `3 · Σ_t x t ≤ C(n,2)`, i.e. `Σ x ≤ |E|/3`. No sign condition is
needed for the upper bound. `steinerX_half_optimal`: `x = X/2` attains it, so the Steiner
representation is an optimal fractional triangle packing of `K_n` among ALL real fractional packings,
not only among half-integral ones. `exists_quadratic_defect_frac` restates C1r with this clause.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.AffineK4

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open SimpleGraph Finset

namespace PaperV

namespace Steiner

variable {V : Type*} [Fintype V] [DecidableEq V]

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Fractional edge load of a weighting `x` at a 2-set `e`. -/
def fracLoad (x : (triTop V).O → K) (e : Finset V) : K :=
  ∑ t ∈ Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1), x t

/-- Double counting: `Σ_e fracLoad x e = 3 · Σ_t x t` (every triangle has three edges). -/
theorem sum_fracLoad (x : (triTop V).O → K) :
    ∑ e ∈ (Finset.univ : Finset V).powersetCard 2, fracLoad x e = 3 * ∑ t, x t := by
  classical
  unfold fracLoad
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun t : (triTop V).O => t.1.powersetCard 2)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_const, Finset.card_powersetCard, (mem_cliqueFinset_top_iff t.1).mp t.2]
    simp [nsmul_eq_mul]
  · intro e t
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_filter,
      Finset.mem_univ]
    tauto

/-- **Universal fractional bound.** Any weighting with edge-load ≤ 1 has `3 · Σ x ≤ C(n,2)`
(`Σ x ≤ |E|/3`). -/
theorem frac_packing_bound (x : (triTop V).O → K)
    (hload : ∀ e ∈ (Finset.univ : Finset V).powersetCard 2, fracLoad x e ≤ 1) :
    3 * ∑ t, x t ≤ ((Finset.univ : Finset V).card.choose 2 : K) := by
  rw [← sum_fracLoad]
  calc ∑ e ∈ (Finset.univ : Finset V).powersetCard 2, fracLoad x e
      ≤ ∑ _e ∈ (Finset.univ : Finset V).powersetCard 2, (1 : K) := Finset.sum_le_sum hload
    _ = ((Finset.univ : Finset V).card.choose 2 : K) := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one]

/-- `x = X/2` is a fractional packing: its edge load is exactly `1` on every edge. -/
theorem fracLoad_half_steinerX {L : Finset (Finset V)} (hL : IsSteinerK4 L) (e : Finset V)
    (he : e.card = 2) : fracLoad (fun t => (steinerX L t : K) / 2) e = 1 := by
  unfold fracLoad
  rw [← Finset.sum_div]
  have h : (∑ t ∈ Finset.univ.filter (fun t : (triTop V).O => e ⊆ t.1), (steinerX L t : K)) = 2 := by
    have := load_steinerX hL e he
    unfold edgeLoad at this
    exact_mod_cast this
  rw [h]; norm_num

/-- `x = X/2` attains the universal bound: `3 · Σ x = C(n,2)`, i.e. `Σ x = |E|/3`. -/
theorem steinerX_half_optimal {L : Finset (Finset V)} (hL : IsSteinerK4 L) :
    3 * ∑ t, ((steinerX L t : K) / 2) = ((Finset.univ : Finset V).card.choose 2 : K) := by
  rw [← Finset.sum_div]
  have h : (∑ t, (steinerX L t : K)) = (multSize (triTop V) (steinerX L) : K) := by
    unfold multSize; push_cast; rfl
  rw [h]
  have h3 := steinerX_optimal hL
  have : (3 * multSize (triTop V) (steinerX L) : K) = (2 * (Finset.univ : Finset V).card.choose 2 : K) := by
    exact_mod_cast h3
  linear_combination this / 2

/-- **Optimality in the full fractional LP.** Every real fractional triangle packing of `K_n`
(edge-load ≤ 1) has total weight at most that of `X/2`. -/
theorem half_steinerX_ge_frac {L : Finset (Finset V)} (hL : IsSteinerK4 L) (x : (triTop V).O → K)
    (hload : ∀ e ∈ (Finset.univ : Finset V).powersetCard 2, fracLoad x e ≤ 1) :
    ∑ t, x t ≤ ∑ t, ((steinerX L t : K) / 2) := by
  have h1 := frac_packing_bound x hload
  have h2 := steinerX_half_optimal (K := K) hL
  linarith

end OrderedField

/-- **Remark C1r (existence form, full-LP optimality).** For every `d` there is an `n = 4^d`-point
complete graph and a triangle multiset `X` of multiplicity ≤ 1 such that `x = X/2` has edge-load
exactly `1`, is optimal among ALL real fractional triangle packings (`Σ x ≤ Σ X/2` for every
load-≤1 `x`), attains `3·Σ x = C(n,2)`, and `3·oct(H[X]) = C(n,2)`. -/
theorem exists_quadratic_defect_frac (d : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (L : Finset (Finset V)),
      Fintype.card V = 4 ^ d ∧ IsSteinerK4 L ∧
      (∀ t, steinerX L t ≤ 1) ∧
      (∀ e ∈ (Finset.univ : Finset V).powersetCard 2,
        fracLoad (fun t => (steinerX L t : ℝ) / 2) e = 1) ∧
      (∀ x : (triTop V).O → ℝ, (∀ e ∈ (Finset.univ : Finset V).powersetCard 2, fracLoad x e ≤ 1) →
        ∑ t, x t ≤ ∑ t, ((steinerX L t : ℝ) / 2)) ∧
      3 * ∑ t, ((steinerX L t : ℝ) / 2) = ((4 ^ d).choose 2 : ℝ) ∧
      3 * oct (HX L) = (4 ^ d).choose 2 := by
  obtain ⟨F, _, _, _, hF⟩ := exists_field_card_four
  have hn : Fintype.card (Pt F d) = 4 ^ d := by rw [card_Pt, hF]
  have hL := affine_isSteinerK4 (d := d) hF
  obtain ⟨_, _, _, _, h4⟩ := quadratic_defect_affine (F := F) hF d
  refine ⟨Pt F d, inferInstance, inferInstance, affineLines F d, hn, hL, fun t => steinerX_le_one t,
    ?_, fun x hx => half_steinerX_ge_frac hL x hx, ?_, h4⟩
  · intro e he
    rw [Finset.mem_powersetCard] at he
    exact fracLoad_half_steinerX hL e he.2
  · have := steinerX_half_optimal (K := ℝ) hL
    rwa [Finset.card_univ, hn] at this

end Steiner

end PaperV
