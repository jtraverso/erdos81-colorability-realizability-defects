/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Global two-thirds bound for the degree-only (resource) LP on pure profiles.

For every pure profile (`m` hosts, common palette of size `s ≥ 2`):

  `μ*_res ≤ min(m·s/2, C(s,2))`  and  `ν = min(m·⌊s/2⌋, C(s,2))`  (Prop. 4.3),   hence
  `ν ≥ ((s−1)/s)·μ*_res ≥ (2/3)·μ*_res`,

with equality of the `2/3` at the triangle instance `(m, s) = (1, 3)` (`gap_third_tight`). This upgrades the
single-instance statement of Proposition 4.4 to the whole pure-profile family: dropping the odd-set inequalities
never costs more than one third, and exactly one third only at `s = 3`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.N2Gap

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV.PureProfile

variable (m s : ℕ)

/-- Pair capacities bound the degree-only LP by `C(s,2)`. -/
theorem sum_le_choose_of_deg (x : Obj m s → ℝ) (hx : MasterFeasibleDeg m s x) :
    ∑ o, x o ≤ (s.choose 2 : ℝ) := by
  obtain ⟨_, _, hpair⟩ := hx
  rw [← Finset.sum_fiberwise univ (fun o : Obj m s => o.2) x]
  calc ∑ e : {e : Finset (Fin s) // e.card = 2},
          (∑ o ∈ univ.filter (fun o : Obj m s => o.2 = e), x o)
      ≤ ∑ _e : {e : Finset (Fin s) // e.card = 2}, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => hpair e)
    _ = ↑(s.choose 2) := by simp

/-- Degree constraints bound the degree-only LP by `m·s/2`: every pair has two vertices, so
`2·Σ x = Σ_j Σ_a (load of `a` at `j`) ≤ m·s`. -/
theorem two_mul_sum_le_of_deg (x : Obj m s → ℝ) (hx : MasterFeasibleDeg m s x) :
    2 * ∑ o, x o ≤ (m : ℝ) * s := by
  obtain ⟨hnn, hdeg, _⟩ := hx
  -- 2 · x o = Σ_{a ∈ o.2.1} x o since |o.2.1| = 2
  have hcard : ∀ o : Obj m s, ∑ _a ∈ o.2.1, x o = 2 * x o := by
    intro o; rw [Finset.sum_const, o.2.2]; simp [mul_comm]
  have h1 : 2 * ∑ o, x o = ∑ o, ∑ a ∈ o.2.1, x o := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun o _ => (hcard o).symm)
  -- swap: Σ_o Σ_{a ∈ o.2.1} x o = Σ_a Σ_{o : a ∈ o.2.1} x o
  have h2 : ∑ o, ∑ a ∈ o.2.1, x o = ∑ a : Fin s, ∑ o ∈ univ.filter (fun o : Obj m s => a ∈ o.2.1), x o := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun a => univ.filter (fun o : Obj m s => a ∈ o.2.1))]
    intro o a; simp
  -- split each vertex sum by host
  have h3 : ∀ a : Fin s, ∑ o ∈ univ.filter (fun o : Obj m s => a ∈ o.2.1), x o =
      ∑ j : Fin m, ∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o := by
    intro a
    rw [← Finset.sum_fiberwise (univ.filter (fun o : Obj m s => a ∈ o.2.1)) (fun o : Obj m s => o.1) x]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext o; simp [and_comm]
  rw [h1, h2]
  calc ∑ a : Fin s, ∑ o ∈ univ.filter (fun o : Obj m s => a ∈ o.2.1), x o
      = ∑ a : Fin s, ∑ j : Fin m, ∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o :=
        Finset.sum_congr rfl (fun a _ => h3 a)
    _ ≤ ∑ _a : Fin s, ∑ _j : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun j _ => hdeg j a))
    _ = (m : ℝ) * s := by simp [mul_comm]

/-- `μ*_res ≤ min(m·s/2, C(s,2))`. -/
theorem muMatDeg_le_min : muMatDeg m s ≤ min ((m : ℝ) * s / 2) (s.choose 2 : ℝ) := by
  apply csSup_le
  · refine ⟨0, fun _ => 0, ?_, by simp⟩
    refine ⟨fun _ => le_rfl, fun _ _ => by simp, fun _ => by simp⟩
  · rintro v ⟨x, hx, rfl⟩
    refine le_min ?_ (sum_le_choose_of_deg m s x hx)
    have := two_mul_sum_le_of_deg m s x hx
    linarith

/-- `m·⌊s/2⌋ ≥ ((s−1)/s)·(m·s/2)` in the reals, for `s ≥ 1`. -/
theorem floor_half_bound (hs : 1 ≤ s) : ((s : ℝ) - 1) / s * ((m : ℝ) * s / 2) ≤ ((m * (s / 2) : ℕ) : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdiv := Nat.div_add_mod s 2
  have hmod : s % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt s (by norm_num))
  have hfl : ((s : ℝ) - 1) / 2 ≤ ((s / 2 : ℕ) : ℝ) := by
    have h1 : (s : ℝ) = 2 * ((s / 2 : ℕ) : ℝ) + ((s % 2 : ℕ) : ℝ) := by exact_mod_cast hdiv.symm
    have h2 : ((s % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
    linarith
  have : ((s : ℝ) - 1) / s * ((m : ℝ) * s / 2) = (m : ℝ) * (((s : ℝ) - 1) / 2) := by
    field_simp
  rw [this]
  push_cast
  exact mul_le_mul_of_nonneg_left hfl (by exact_mod_cast Nat.zero_le m)

/-- **Global pure-profile bound.** `ν ≥ ((s−1)/s)·μ*_res` for `s ≥ 1`. -/
theorem nu_ge_frac_muMatDeg (hs : 1 ≤ s) :
    ((s : ℝ) - 1) / s * muMatDeg m s ≤ (nu m s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hc : (0 : ℝ) ≤ ((s : ℝ) - 1) / s := div_nonneg (by linarith [show (1 : ℝ) ≤ s by exact_mod_cast hs]) hsR.le
  have hmu := muMatDeg_le_min m s
  rw [prop43_nu]
  have hA := floor_half_bound m s hs
  have hB : ((s : ℝ) - 1) / s * (s.choose 2 : ℝ) ≤ (s.choose 2 : ℝ) := by
    have h1 : ((s : ℝ) - 1) / s ≤ 1 := by rw [div_le_one hsR]; linarith
    exact mul_le_of_le_one_left (by exact_mod_cast Nat.zero_le _) h1
  push_cast
  rcases le_total ((m : ℝ) * s / 2) (s.choose 2 : ℝ) with h | h
  · rw [min_eq_left h] at hmu
    have := mul_le_mul_of_nonneg_left hmu hc
    have hmin : ((m * (s / 2) : ℕ) : ℝ) ≤ (s.choose 2 : ℝ) ∨ (s.choose 2 : ℝ) ≤ ((m * (s / 2) : ℕ) : ℝ) :=
      le_total _ _
    rcases hmin with hm | hm
    · rw [min_eq_left (by exact_mod_cast hm)]; push_cast at hA ⊢; linarith
    · rw [min_eq_right (by exact_mod_cast hm)]; push_cast at hA ⊢; nlinarith
  · rw [min_eq_right h] at hmu
    have := mul_le_mul_of_nonneg_left hmu hc
    rcases le_total ((m * (s / 2) : ℕ) : ℝ) (s.choose 2 : ℝ) with hm | hm
    · rw [min_eq_left (by exact_mod_cast hm)]; push_cast at hA ⊢; nlinarith
    · rw [min_eq_right (by exact_mod_cast hm)]; push_cast at hA ⊢; linarith

/-- **`ν ≥ (2/3)·μ*_res` on every pure profile with `s ≥ 3`** (and trivially for `s = 2`, where
`⌊s/2⌋ = s/2`). Tight at `(m, s) = (1, 3)` by `gap_third_tight`. -/
theorem nu_ge_two_thirds_muMatDeg (hs : 3 ≤ s) : (2 / 3 : ℝ) * muMatDeg m s ≤ (nu m s : ℝ) := by
  have h := nu_ge_frac_muMatDeg m s (by omega)
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hfrac : (2 / 3 : ℝ) ≤ ((s : ℝ) - 1) / s := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hmu0 : 0 ≤ muMatDeg m s := by
    apply le_csSup
    · exact ⟨(s.choose 2 : ℝ), by rintro v ⟨x, hx, rfl⟩; exact sum_le_choose_of_deg m s x hx⟩
    · exact ⟨fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => by simp, fun _ => by simp⟩, by simp⟩
  calc (2 / 3 : ℝ) * muMatDeg m s ≤ ((s : ℝ) - 1) / s * muMatDeg m s :=
        mul_le_mul_of_nonneg_right hfrac hmu0
    _ ≤ nu m s := h

/-- The `s = 2` case: `ν ≥ μ*_res` outright (`⌊s/2⌋ = s/2`). -/
theorem nu_ge_muMatDeg_two : muMatDeg m 2 ≤ (nu m 2 : ℝ) := by
  have hmu := muMatDeg_le_min m 2
  rw [prop43_nu]
  push_cast
  norm_num at hmu ⊢
  exact hmu

end PaperV.PureProfile
