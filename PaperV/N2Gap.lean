/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — N2′: a GENUINE (tight) ⅓ integrality gap for the host-clique matching LP.

N2 (`PaperV.PureProfile.hostClique_gap_le_third`) is vacuous in the pure-profile model because
the odd-set (blossom) inequalities in `MasterFeasible` force `μ*_mat = ν` (`hostClique_gap_zero`).

This file isolates the role of those constraints.  Dropping the odd-set inequalities yields the
weaker *degree-only* LP `MasterFeasibleDeg` with optimum `muMatDeg ≥ muMat`.  On the smallest odd
instance — one host with palette `Fin 3`, whose three pairs `{0,1},{0,2},{1,2}` form a triangle in
the conflict graph — this LP has a real gap:

    ν(1,3) = 1,     μ*_deg(1,3) = 3/2,     so   μ*_deg − ν = 1/2 = μ*_deg / 3,   and   μ*_deg > ν.

Hence the ⅓ bound is TIGHT and the gap is genuinely positive once the blossom constraints are
removed — the a-priori content N2 was meant to capture.  Layer E (unconditional).
-/
module

public import PaperV.PureProfile

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV.PureProfile

variable (m s : ℕ)

/-- The **degree-only** master matching LP: nonnegativity, per-host degree ≤ 1, and per-pair
capacity ≤ 1 — i.e. `MasterFeasible` WITHOUT the odd-set (blossom) inequalities. -/
def MasterFeasibleDeg (x : Obj m s → ℝ) : Prop :=
  (∀ o, 0 ≤ x o) ∧
  (∀ (j : Fin m) (a : Fin s), (∑ o ∈ univ.filter (fun o => o.1 = j ∧ a ∈ o.2.1), x o) ≤ 1) ∧
  (∀ e : {e : Finset (Fin s) // e.card = 2},
      (∑ o ∈ univ.filter (fun o => o.2 = e), x o) ≤ 1)

/-- Optimum of the degree-only LP. -/
noncomputable def muMatDeg : ℝ :=
  sSup { v : ℝ | ∃ x : Obj m s → ℝ, MasterFeasibleDeg m s x ∧ v = ∑ o, x o }

/-- Dropping the odd-set constraints only enlarges the feasible region, so the degree-only
optimum dominates the full master optimum: `μ*_mat ≤ μ*_deg`. -/
theorem muMat_le_muMatDeg : muMat m s ≤ muMatDeg m s := by
  have h_sub : ∀ x : Obj m s → ℝ, MasterFeasible m s x → MasterFeasibleDeg m s x := by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.2⟩
  apply csSup_le
  · use 0
    use fun _ => 0
    refine ⟨?_, by simp⟩
    simp [MasterFeasible]
    intro j S hodd hcard
    apply div_nonneg
    · linarith [show (S.card : ℝ) ≥ 3 by exact_mod_cast hcard]
    · norm_num
  · intro v hv
    obtain ⟨x, hxMF, rfl⟩ := hv
    apply le_csSup
    · refine ⟨(↑(s.choose 2) : ℝ), ?_⟩
      rintro v ⟨x, hx, rfl⟩
      obtain ⟨_, _, hpair⟩ := hx
      rw [← Finset.sum_fiberwise univ (fun o : Obj m s => o.2) x]
      calc ∑ e : {e : Finset (Fin s) // e.card = 2},
              (∑ o ∈ univ.filter (fun o : Obj m s => o.2 = e), x o)
          ≤ ∑ _e : {e : Finset (Fin s) // e.card = 2}, (1:ℝ) :=
              Finset.sum_le_sum (fun e _ => hpair e)
        _ = ↑(s.choose 2) := by simp
    · exact ⟨x, h_sub x hxMF, rfl⟩

/-- Integral packing number of the triangle instance: `ν(1,3) = 1`.  All three pairs of `Fin 3`
pairwise intersect, so at most one fits in a feasible (vertex-disjoint) set at the single host. -/
theorem nu_triangle : nu 1 3 = 1 := by simp [prop43_nu]

/-- Degree-only LP optimum of the triangle instance: `μ*_deg(1,3) = 3/2`.  The uniform half
`x ≡ 1/2` is feasible with value `3/2`; summing the three degree constraints gives
`2·(∑ x) ≤ 3`, i.e. `∑ x ≤ 3/2`. -/
theorem muMatDeg_triangle : muMatDeg 1 3 = 3 / 2 := by
  let V : Set ℝ := {v | ∃ x : Obj 1 3 → ℝ, MasterFeasibleDeg 1 3 x ∧ v = ∑ o, x o}
  have hb : BddAbove V := by
    refine ⟨3, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    obtain ⟨-, -, hp⟩ := hx
    rw [← Finset.sum_fiberwise univ (fun o : Obj 1 3 => o.2) x]
    calc
      _ ≤ ∑ _e : {e : Finset (Fin 3) // e.card = 2}, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => hp e)
      _ = 3 := by simp
  apply le_antisymm
  · unfold muMatDeg
    apply csSup_le
    · refine ⟨0, fun _ => 0, ?_, by simp⟩
      simp [MasterFeasibleDeg]
    · rintro v ⟨x, hx, rfl⟩
      obtain ⟨-, hd, -⟩ := hx
      have hs : ∑ a : Fin 3,
          (∑ o ∈ univ.filter (fun o : Obj 1 3 => o.1 = 0 ∧ a ∈ o.2.1), x o) ≤ 3 := by
        calc
          _ ≤ ∑ _a : Fin 3, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hd 0 a)
          _ = 3 := by simp
      rw [host_degree_double] at hs
      have hu : (univ.filter (fun o : Obj 1 3 => o.1 = (0 : Fin 1))) = univ := by
        ext o
        simp [Subsingleton.elim o.1 0]
      rw [hu] at hs
      linarith
  · unfold muMatDeg
    apply le_csSup hb
    refine ⟨fun _ => (1 / 2 : ℝ), ?_, ?_⟩
    · refine ⟨by norm_num, ?_, ?_⟩
      · intro j a
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [sum_const, nsmul_eq_mul]
        have hc : (univ.filter (fun o : Obj 1 3 => o.1 = 0 ∧ a ∈ o.2.1)).card = 2 := by
          fin_cases a <;> decide
        rw [hc]
        norm_num
      · intro e
        rw [sum_const, nsmul_eq_mul]
        have hc : (univ.filter (fun o : Obj 1 3 => o.2 = e)).card = 1 := by
          apply Finset.card_eq_one.mpr
          refine ⟨(0, e), ?_⟩
          ext o
          simp [Prod.ext_iff, Subsingleton.elim o.1 0]
        rw [hc]
        norm_num
    · rw [sum_const, nsmul_eq_mul]
      norm_num [Fintype.card_prod, card_two_subsets]

/-- **N2′ (genuine tight ⅓-gap).**  Without the odd-set constraints, the triangle host-clique
instance has integrality gap `μ*_deg − ν = μ*_deg/3` (tight), and the gap is strictly positive:
`ν < μ*_deg`.  Contrast `hostClique_gap_zero` (gap `= 0` with the blossom constraints). -/
theorem gap_third_tight :
    muMatDeg 1 3 - (nu 1 3 : ℝ) = muMatDeg 1 3 / 3 ∧ (nu 1 3 : ℝ) < muMatDeg 1 3 := by
  rw [nu_triangle, muMatDeg_triangle]
  norm_num

end PaperV.PureProfile
