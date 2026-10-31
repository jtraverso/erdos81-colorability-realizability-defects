/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import PaperV.TwoErrorCertificate
public import PaperV.StrongDuality
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.BigOperators

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PaperV.ResourceCertificate
open Finset System
variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
variable (R : System I E)

def realIncidence (o : I) (e : E) : ℝ := (R.incidence o e : ℝ)

/-- Exact embedding of rational primal data into the real resource LP. -/
def primalToReal (p : FiniteLP.PrimalFeasible R.incidence) :
    FiniteLP.PrimalFeasible (realIncidence R) where
  weight o := (p.weight o : ℝ)
  weight_nonneg o := by exact_mod_cast p.weight_nonneg o
  capacity e := by
    have h := p.capacity e
    dsimp only [realIncidence]
    exact_mod_cast h

/-- A rational cover bounds every real feasible point. -/
def dualToReal (w : I → ℚ) (d : FiniteLP.DualFeasible R.incidence w) :
    FiniteLP.DualFeasible (realIncidence R) (fun o => (w o : ℝ)) where
  price e := (d.price e : ℝ)
  price_nonneg e := by exact_mod_cast d.price_nonneg e
  demand o := by
    have h := d.demand o
    dsimp only [realIncidence]
    exact_mod_cast h

theorem primalToReal_value (w : I → ℚ) (p : FiniteLP.PrimalFeasible R.incidence) :
    FiniteLP.primalValue (fun o => (w o : ℝ)) (primalToReal R p) =
      ((FiniteLP.primalValue w p : ℚ) : ℝ) := by
  simp [FiniteLP.primalValue, primalToReal]

theorem dualToReal_value (w : I → ℚ) (d : FiniteLP.DualFeasible R.incidence w) :
    FiniteLP.dualValue (dualToReal R w d) = ((FiniteLP.dualValue d : ℚ) : ℝ) := by
  simp [FiniteLP.dualValue, dualToReal]

/-- Strong duality supplies an actual rational optimum for this resource LP. -/
theorem exists_optimum (w : I → ℚ) :
    ∃ p : FiniteLP.PrimalFeasible R.incidence,
      ∀ z : FiniteLP.PrimalFeasible R.incidence,
        FiniteLP.primalValue w z ≤ FiniteLP.primalValue w p := by
  have hnonneg : ∀ o e, 0 ≤ R.incidence o e := by
    intro o e; unfold incidence; split <;> norm_num
  have hcover : ∀ o, ∃ e, 1 ≤ R.incidence o e := by
    intro o
    obtain ⟨e, he⟩ := R.nonempty o
    exact ⟨e, by simp [incidence, he]⟩
  obtain ⟨p, d, h⟩ := FiniteLP.exists_equal_primal_dual R.incidence w hnonneg hcover
  exact ⟨p, (FiniteLP.optimal_of_equal p d h).1⟩

/-- Rational strong duality also produces a real optimum with the same value. -/
theorem exists_real_optimum (w : I → ℚ) :
    ∃ p : FiniteLP.PrimalFeasible (realIncidence R),
      ∀ z : FiniteLP.PrimalFeasible (realIncidence R),
        FiniteLP.primalValue (fun o => (w o : ℝ)) z ≤
          FiniteLP.primalValue (fun o => (w o : ℝ)) p := by
  have hnonneg : ∀ o e, 0 ≤ R.incidence o e := by
    intro o e; unfold incidence; split <;> norm_num
  have hcover : ∀ o, ∃ e, 1 ≤ R.incidence o e := by
    intro o
    obtain ⟨e, he⟩ := R.nonempty o
    exact ⟨e, by simp [incidence, he]⟩
  obtain ⟨p, d, h⟩ := FiniteLP.exists_equal_primal_dual R.incidence w hnonneg hcover
  refine ⟨primalToReal R p, ?_⟩
  intro z
  have hz := FiniteLP.weak_duality z (dualToReal R w d)
  rw [dualToReal_value] at hz
  rw [primalToReal_value, h]
  exact hz

/-- Corollary 4.6 for the real resource LP with rational input certificates. -/
theorem two_error_real_optimum
    (w : I → ℚ) (p : FiniteLP.PrimalFeasible R.incidence)
    (d : FiniteLP.DualFeasible R.incidence w)
    (pstar : FiniteLP.PrimalFeasible (realIncidence R))
    (hopt : ∀ z : FiniteLP.PrimalFeasible (realIncidence R),
      FiniteLP.primalValue (fun o => (w o : ℝ)) z ≤
        FiniteLP.primalValue (fun o => (w o : ℝ)) pstar)
    {q : ℕ} (hq : 0 < q) {X : I → ℕ}
    (hX : ∀ o, (q : ℚ) * p.weight o = X o)
    (c : Realization R w X q) :
    ∃ i : Fin q,
      R.Packing (c.out i) ∧
      ((FiniteLP.primalValue w p : ℚ) : ℝ) - (c.cost : ℝ) / q ≤ (R.gain w (c.out i) : ℝ) ∧
      0 ≤ FiniteLP.primalValue (fun o => (w o : ℝ)) pstar - (R.gain w (c.out i) : ℝ) ∧
      FiniteLP.primalValue (fun o => (w o : ℝ)) pstar - (R.gain w (c.out i) : ℝ) ≤
        ((FiniteLP.dualValue d : ℚ) : ℝ) - ((FiniteLP.primalValue w p : ℚ) : ℝ) + (c.cost : ℝ) / q := by
  obtain ⟨i, hi, hl, _⟩ := two_error_certificate w p d hq hX c
  have hlR : ((FiniteLP.primalValue w p : ℚ) : ℝ) - (c.cost : ℝ) / q ≤
      (R.gain w (c.out i) : ℝ) := by exact_mod_cast hl
  have hpack := hopt (primalToReal R (R.packingPrimal (c.out i) hi))
  rw [primalToReal_value, packingPrimal_value] at hpack
  have hz := FiniteLP.weak_duality pstar (dualToReal R w d)
  rw [dualToReal_value] at hz
  exact ⟨i, hi, hlR, sub_nonneg.mpr hpack, by linarith⟩

end PaperV.ResourceCertificate
