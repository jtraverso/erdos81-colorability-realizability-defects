/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Sharpening of the pure-profile comparison (Proposition 7.1a).

`PureProfileGap.lean` proves `μ*_res ≤ min(m·s/2, C(s,2))` and the resulting factor `(s−1)/s`. An exact
sweep of the small profiles (m ≤ 4, s ≤ 6) with independent solvers showed two things the development did
not record, both of which follow from what is already proved once the trivial direction is supplied:

  * `nu_le_muMatDeg` — an integral packing is a feasible point of the degree-only LP, so `ν ≤ μ*_res`;
  * `nu_eq_muMatDeg_of_even` — for an even palette the degree-only relaxation is EXACT: `ν = μ*_res`.

The second one closes the even case of Proposition 7.1a: the loss `(s−1)/s` is a phenomenon of odd
palettes only, and for even `s` the resource relaxation gives nothing away.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.PureProfileGap

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open Finset

namespace PaperV.PureProfile

variable (m s : ℕ)

/-- The `0/1` weighting of an integral packing. -/
noncomputable def indicatorOf (R : Finset (Obj m s)) : Obj m s → ℝ :=
  fun o => if o ∈ R then 1 else 0

/-- **An integral packing is a feasible point of the degree-only LP.** -/
theorem masterFeasibleDeg_indicator {R : Finset (Obj m s)} (hR : Feasible m s R) :
    MasterFeasibleDeg m s (indicatorOf m s R) := by
  classical
  refine ⟨fun o => by unfold indicatorOf; split_ifs <;> norm_num, ?_, ?_⟩
  · -- per-host degree: two packed objects at host `j` through vertex `a` would meet
    intro j a
    unfold indicatorOf
    rw [Finset.sum_boole]
    have hle : ((univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1)).filter
        (fun o => o ∈ R)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      by_contra hne
      have hmeet := hR.1 x hx.2 y hy.2 hne (by rw [hx.1.1, hy.1.1])
      have : a ∈ x.2.1 ∩ y.2.1 := Finset.mem_inter.mpr ⟨hx.1.2, hy.1.2⟩
      rw [hmeet] at this
      exact absurd this (Finset.notMem_empty a)
    exact_mod_cast hle
  · -- per-pair capacity: the same pair forces the same host, hence the same object
    intro e
    unfold indicatorOf
    rw [Finset.sum_boole]
    have hle : ((univ.filter (fun o : Obj m s => o.2 = e)).filter (fun o => o ∈ R)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hpair : x.2.1 = y.2.1 := by rw [hx.1, hy.1]
      have hhost : x.1 = y.1 := hR.2 x hx.2 y hy.2 hpair
      have h2 : x.2 = y.2 := by rw [hx.1, hy.1]
      exact Prod.ext hhost h2
    exact_mod_cast hle

theorem sum_indicatorOf (R : Finset (Obj m s)) :
    ∑ o, indicatorOf m s R o = (R.card : ℝ) := by
  classical
  unfold indicatorOf
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Integral is at most fractional:** `ν ≤ μ*_res` on every pure profile. -/
theorem nu_le_muMatDeg : (nu m s : ℝ) ≤ muMatDeg m s := by
  classical
  obtain ⟨R, hR, hcard⟩ : ∃ R : Finset (Obj m s), Feasible m s R ∧ R.card = nu m s := by
    have hne : (univ.filter (Feasible m s)).Nonempty := by
      refine ⟨∅, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun x hx => absurd hx (Finset.notMem_empty x),
             fun x hx => absurd hx (Finset.notMem_empty x)⟩
    obtain ⟨R, hRmem, hmax⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hRmem
    exact ⟨R, hRmem, hmax.symm⟩
  rw [← hcard, ← sum_indicatorOf m s R]
  apply le_csSup
  · refine ⟨(s.choose 2 : ℝ), ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact sum_le_choose_of_deg m s x hx
  · exact ⟨indicatorOf m s R, masterFeasibleDeg_indicator m s hR, rfl⟩

/-- **The degree-only relaxation is exact on even palettes:** `ν = μ*_res` whenever `s` is even.
The `(s−1)/s` loss of Proposition 7.1a is therefore a phenomenon of odd palettes only. -/
theorem nu_eq_muMatDeg_of_even (hs : Even s) : (nu m s : ℝ) = muMatDeg m s := by
  refine le_antisymm (nu_le_muMatDeg m s) ?_
  have hupper := muMatDeg_le_min m s
  have hhalf : ((s / 2 : ℕ) : ℝ) = (s : ℝ) / 2 := by
    obtain ⟨k, hk⟩ := hs
    subst hk
    have : k + k = 2 * k := by ring
    rw [this, Nat.mul_div_cancel_left k (by norm_num)]
    push_cast
    ring
  rw [prop43_nu]
  push_cast [hhalf]
  have hmul : ((m : ℝ) * s / 2) = (m : ℝ) * ((s : ℝ) / 2) := by ring
  rw [← hmul]
  exact hupper

end PaperV.PureProfile
