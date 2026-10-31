/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Realizer combinators and the certificate optimality criterion (wave 2a′).

  subsetRealizer : a class `S` is realized by any independent subclass `T ⊆ S`, with certified loss
                   `w(S ∖ T)` (the "partial repair" realizer: drop copies, pay their weight).
  union          : two realizers of disjoint classes with disjoint, jointly feasible outputs compose,
                   losses add.
  optimality     : a certificate whose cost equals `|X|_w − q·ν_{w_P}(P)` is optimal:
                   `D_{q,ℛ}^w = cost` (the realizability analogue of `optimal_of_equal`).
  lower bound    : `|X|_w − q·ν_{w_P}(P) ≤ D_{q,ℛ}^w` for every `ℛ` with an admissible certificate.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.RealizabilityDefect

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {C P : ConflictSystem}

/-! ### Subset (partial repair) realizer, `P = C` -/

variable (C) in
/-- **Subset realizer.** An independent subclass `T ⊆ S` realizes `S` with loss `w(S ∖ T)`. -/
def subsetRealizer (w : C.O → ℕ) {X : C.O → ℕ} (S T : Finset (Copies C X)) (hTS : T ⊆ S)
    (hT : Feasible (Hgraph C X) T) : ClassRealizer C C w w S where
  out := T.image (objOf (C := C) (X := X))
  feasible := csFeasible_image_objOf C T hT
  loss := ∑ c ∈ S \ T, copyWeight C w c
  bound := by
    rw [sum_copyWeight_image_objOf C T hT, ← Finset.sum_sdiff hTS, Nat.add_comm]

theorem subsetRealizer_loss (w : C.O → ℕ) {X : C.O → ℕ} (S T : Finset (Copies C X)) (hTS : T ⊆ S)
    (hT : Feasible (Hgraph C X) T) :
    (subsetRealizer C w S T hTS hT).loss = ∑ c ∈ S \ T, copyWeight C w c := rfl

/-- On an independent class the subset realizer with `T = S` is the identity realizer (loss `0`). -/
theorem subsetRealizer_self (w : C.O → ℕ) {X : C.O → ℕ} (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) :
    (subsetRealizer C w S S (subset_refl S) hS).loss = 0 := by
  simp [subsetRealizer_loss]

/-! ### Composition -/

/-- **Union of realizers.** Realizers of disjoint classes `S₁, S₂` whose outputs are disjoint and jointly
feasible compose to a realizer of `S₁ ∪ S₂` with loss `r₁ + r₂`. -/
def ClassRealizer.union {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {S₁ S₂ : Finset (Copies C X)}
    (r₁ : ClassRealizer C P w wP S₁) (r₂ : ClassRealizer C P w wP S₂)
    (hS : Disjoint S₁ S₂) (hout : Disjoint r₁.out r₂.out)
    (hfeas : CSFeasible P (r₁.out ∪ r₂.out)) : ClassRealizer C P w wP (S₁ ∪ S₂) where
  out := r₁.out ∪ r₂.out
  feasible := hfeas
  loss := r₁.loss + r₂.loss
  bound := by
    rw [Finset.sum_union hS, Finset.sum_union hout]
    have := r₁.bound; have := r₂.bound
    omega

theorem ClassRealizer.union_loss {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    {S₁ S₂ : Finset (Copies C X)} (r₁ : ClassRealizer C P w wP S₁) (r₂ : ClassRealizer C P w wP S₂)
    (hS : Disjoint S₁ S₂) (hout : Disjoint r₁.out r₂.out) (hfeas : CSFeasible P (r₁.out ∪ r₂.out)) :
    (r₁.union r₂ hS hout hfeas).loss = r₁.loss + r₂.loss := rfl

/-- Exact realizers compose to an exact realizer. -/
theorem ClassRealizer.union_exact {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    {S₁ S₂ : Finset (Copies C X)} (r₁ : ClassRealizer C P w wP S₁) (r₂ : ClassRealizer C P w wP S₂)
    (hS : Disjoint S₁ S₂) (hout : Disjoint r₁.out r₂.out) (hfeas : CSFeasible P (r₁.out ∪ r₂.out))
    (h₁ : r₁.Exact) (h₂ : r₂.Exact) : (r₁.union r₂ hS hout hfeas).Exact := by
  unfold ClassRealizer.Exact at *
  rw [ClassRealizer.union_loss, h₁, h₂]

/-- Weakening: a realizer with loss `r` is also a realizer with any larger certified loss. -/
def ClassRealizer.weaken {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {S : Finset (Copies C X)}
    (r : ClassRealizer C P w wP S) (r' : ℕ) (h : r.loss ≤ r') : ClassRealizer C P w wP S where
  out := r.out
  feasible := r.feasible
  loss := r'
  bound := le_trans r.bound (Nat.add_le_add_left h _)

/-! ### Lower bound and optimality criterion -/

/-- **Lower bound.** `|X|_w − q·ν_{w_P}(P) ≤ D_{q,ℛ}^w` (RDT rearranged). -/
theorem wRDq_ge {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (R : RealizerClass C P w wP X) (hne : ∃ cert : RealCert C P w wP X q, cert.Admissible R) :
    wMultSize C w X - q * wNu P wP ≤ wRDq R q := by
  have := realizability_defect_transfer hq R hne
  omega

/-- **Optimality criterion.** An admissible certificate with `cost + q·ν_{w_P}(P) = |X|_w` attains the
realizability defect: `D_{q,ℛ}^w = cost`. -/
theorem wRDq_eq_of_cost {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (R : RealizerClass C P w wP X) (cert : RealCert C P w wP X q) (hadm : cert.Admissible R)
    (hopt : cert.cost + q * wNu P wP = wMultSize C w X) :
    wRDq R q = cert.cost := by
  apply le_antisymm (wRDq_le_cost R cert hadm)
  have := wRDq_ge hq R ⟨cert, hadm⟩
  omega

/-- Optimality with a *lower bound on the packing side*: if `q·ν_{w_P}(P) ≤ |X|_w − cost` cannot be improved,
i.e. every feasible set of `P` has weight ≤ `(|X|_w − cost)/q`, then the certificate is optimal. -/
theorem wRDq_eq_of_cost_of_nu_le {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (R : RealizerClass C P w wP X) (cert : RealCert C P w wP X q) (hadm : cert.Admissible R)
    (hnu : q * wNu P wP + cert.cost ≤ wMultSize C w X) :
    wRDq R q = cert.cost := by
  apply le_antisymm (wRDq_le_cost R cert hadm)
  have := wRDq_ge hq R ⟨cert, hadm⟩
  omega

end PaperV
