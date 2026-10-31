/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Realizers and the Realizable-Class Transfer (RCT), Part II of the realizability programme.

The weighted transfer `transfer_q_weighted_cert` uses the independence of the colour classes of
`H[X] − Z` exactly once: to pass from a class of copies to a feasible (physical) object set of the
same weight. Here that step is abstracted into a *realizer*: a class `S` of copies of the auxiliary
system `C` is realized by a feasible object set `out` of a (possibly different) physical system `P`
with a certified loss `r`, i.e. `w(S) ≤ w_P(out) + r`.

  RCT : for any deletion set `Z`, any partition of the remaining copies into `q` classes and any
        family of realizers, some class satisfies  `|X|_w ≤ q · w_P(R(C_i)) + w(Z) + Σ_i r_i`,
        hence  `|X|_w ≤ q · ν_{w_P}(P) + w(Z) + Σ_i r_i`.
  RCT0: with exact realizers (all `r_i = 0`) this is `|X|_w ≤ q · ν_{w_P}(P) + w(Z)`.

The classes are NOT required to be independent in `H[X]`; the identity realizer on independent
classes recovers the current engine (see `RealizabilityDefect.lean`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.WeightedTransfer

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable (C P : ConflictSystem)

/-- Any feasible object set of `P` has weight at most `ν_w(P)`. -/
theorem csFeasible_wsum_le_wNu (wP : P.O → ℕ) (T : Finset P.O) (hT : CSFeasible P T) :
    ∑ o ∈ T, wP o ≤ wNu P wP := by
  classical
  unfold wNu
  exact Finset.le_sup (f := fun S => ∑ o ∈ S, wP o) (by simp [hT])

/-- **Realizer of a class.** A class `S` of copies of `X` (auxiliary system `C`) is realized by a
feasible object set `out` of the physical system `P` with certified loss `loss`:
`w(S) ≤ w_P(out) + loss`. -/
structure ClassRealizer (w : C.O → ℕ) (wP : P.O → ℕ) {X : C.O → ℕ}
    (S : Finset (Copies C X)) where
  out : Finset P.O
  feasible : CSFeasible P out
  loss : ℕ
  bound : ∑ c ∈ S, copyWeight C w c ≤ ∑ o ∈ out, wP o + loss

/-- An exact realizer has zero loss. -/
def ClassRealizer.Exact {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {S : Finset (Copies C X)}
    (r : ClassRealizer C P w wP S) : Prop := r.loss = 0

/-- The `i`-th class of a `q`-partition `part` of the copies outside `Z`. -/
def classOf {X : C.O → ℕ} (Z : Finset (Copies C X)) {q : ℕ} (part : Copies C X → Fin q)
    (i : Fin q) : Finset (Copies C X) :=
  Finset.univ.filter (fun c => c ∉ Z ∧ part c = i)

theorem mem_classOf {X : C.O → ℕ} {Z : Finset (Copies C X)} {q : ℕ} {part : Copies C X → Fin q}
    {i : Fin q} {c : Copies C X} : c ∈ classOf C Z part i ↔ c ∉ Z ∧ part c = i := by
  simp [classOf]

/-- The classes partition the copies outside `Z`: sums add up. -/
theorem sum_classOf {X : C.O → ℕ} (Z : Finset (Copies C X)) {q : ℕ} (part : Copies C X → Fin q)
    (f : Copies C X → ℕ) :
    ∑ i : Fin q, ∑ c ∈ classOf C Z part i, f c = ∑ c ∈ Finset.univ \ Z, f c := by
  classical
  rw [← Finset.sum_biUnion]
  · congr 1; ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_classOf, Finset.mem_sdiff]
    constructor
    · rintro ⟨i, hi, _⟩; exact hi
    · intro h; exact ⟨part c, h, rfl⟩
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, mem_classOf]
    rintro c ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (hi.symm.trans hj)

/-- **Realizability certificate.** A deletion set `Z`, a `q`-partition of the remaining copies and a
realizer for every class. Classes need not be independent in `H[X]`. -/
structure RealCert (w : C.O → ℕ) (wP : P.O → ℕ) (X : C.O → ℕ) (q : ℕ) where
  Z : Finset (Copies C X)
  part : Copies C X → Fin q
  real : ∀ i : Fin q, ClassRealizer C P w wP (classOf C Z part i)

variable {C P}

/-- Cost of a certificate: `w(Z) + Σ_i r_i`. -/
def RealCert.cost {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C P w wP X q) : ℕ :=
  ∑ c ∈ cert.Z, copyWeight C w c + ∑ i : Fin q, (cert.real i).loss

/-- A certificate is exact if every class realizer is exact. -/
def RealCert.Exact {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C P w wP X q) : Prop := ∀ i, (cert.real i).Exact

theorem RealCert.cost_of_exact {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C P w wP X q) (h : cert.Exact) :
    cert.cost = ∑ c ∈ cert.Z, copyWeight C w c := by
  unfold RealCert.cost
  have : ∑ i : Fin q, (cert.real i).loss = 0 :=
    Finset.sum_eq_zero (fun i _ => h i)
  omega

/-- Total weight of all copies. -/
theorem sum_copyWeight_univ (w : C.O → ℕ) (X : C.O → ℕ) :
    ∑ c : Copies C X, copyWeight C w c = wMultSize C w X := by
  unfold wMultSize copyWeight Copies
  rw [Fintype.sum_sigma]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Realizable-Class Transfer (RCT), class form.** Some class of the certificate satisfies
`|X|_w ≤ q · w_P(R(C_i)) + w(Z) + Σ_i r_i`. -/
theorem realizable_class_transfer {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (cert : RealCert C P w wP X q) :
    ∃ i : Fin q, wMultSize C w X ≤ q * ∑ o ∈ (cert.real i).out, wP o + cert.cost := by
  classical
  -- the heaviest realized class
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
    (fun i => ∑ o ∈ (cert.real i).out, wP o) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  have hsplit : wMultSize C w X =
      ∑ c ∈ Finset.univ \ cert.Z, copyWeight C w c + ∑ c ∈ cert.Z, copyWeight C w c := by
    rw [← sum_copyWeight_univ, Finset.sum_sdiff (Finset.subset_univ _)]
  have hclasses := sum_classOf C cert.Z cert.part (copyWeight C w)
  have hbound : ∑ j : Fin q, ∑ c ∈ classOf C cert.Z cert.part j, copyWeight C w c ≤
      ∑ j : Fin q, (∑ o ∈ (cert.real j).out, wP o + (cert.real j).loss) :=
    Finset.sum_le_sum (fun j _ => (cert.real j).bound)
  have hmax : ∑ j : Fin q, ∑ o ∈ (cert.real j).out, wP o ≤ q * ∑ o ∈ (cert.real i).out, wP o := by
    calc ∑ j : Fin q, ∑ o ∈ (cert.real j).out, wP o
        ≤ ∑ _j : Fin q, ∑ o ∈ (cert.real i).out, wP o :=
          Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ _))
      _ = q * ∑ o ∈ (cert.real i).out, wP o := by simp
  rw [Finset.sum_add_distrib] at hbound
  unfold RealCert.cost
  omega

/-- **RCT, packing form.** `|X|_w ≤ q · ν_{w_P}(P) + w(Z) + Σ_i r_i` for every certificate. -/
theorem realizable_transfer_cert {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (cert : RealCert C P w wP X q) :
    wMultSize C w X ≤ q * wNu P wP + cert.cost := by
  obtain ⟨i, hi⟩ := realizable_class_transfer hq cert
  have := csFeasible_wsum_le_wNu P wP _ (cert.real i).feasible
  have := Nat.mul_le_mul_left q this
  omega

/-- **RCT0.** Exact certificates: `|X|_w ≤ q · ν_{w_P}(P) + w(Z)`. -/
theorem realizable_transfer_exact {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (cert : RealCert C P w wP X q) (hex : cert.Exact) :
    wMultSize C w X ≤ q * wNu P wP + ∑ c ∈ cert.Z, copyWeight C w c := by
  have := realizable_transfer_cert hq cert
  rwa [cert.cost_of_exact hex] at this

end PaperV
