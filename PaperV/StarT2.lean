/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — §6.3 (STAR-T2) counterexample: `β = 1` does NOT force the uncovered residual to be a
star with ≤ 2 leaves. Ledger node L-C2 (finite, host-clique).

Concrete instance (n = 7 vertices `Fin 7`, 6 hosts `Fin 6`), palettes
  L = (0,1,4), (1,4), (0,2,5), (2,5), (0,3,6), (3,6).
Coverable pairs (9): the six through vertex 0 — {0,1},{0,4},{0,2},{0,5},{0,3},{0,6} — and the
three non-0 pairs {1,4},{2,5},{3,6}. A host-clique packing assigns objects `(host, pair)` with
per-host matching (endpoints disjoint within a host) and global pair-uniqueness (each pair used
at most once). Facts (verified exhaustively by the certificate; here formalised):
  ν = 6, |cov| = 9, k = 3, and EVERY maximum packing leaves a 3-leaf star centred at 0
  (β = 1). Hence β = 1 does not bound the residual to ≤ 2 leaves — the conjecture is false.

Key upper-bound certificate (no enumeration): vertex 0 lies only in hosts {0,2,4} and is matched
at most once per host, so at most 3 pairs through 0 are covered; there are only 3 coverable pairs
avoiding 0; hence ν ≤ 6. A size-6 packing attains it.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

import Mathlib.Tactic.FinCases

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Card

@[expose] public section
open Finset

namespace PaperV
namespace StarT2

/-- The 12 coverable objects `(host, a, b)` of the STAR-T2 instance (each pair `a<b` in the
host's palette). Indexed by `Fin 12`. -/
def objs : Fin 12 → (Fin 6 × Fin 7 × Fin 7)
  | 0 => (0, 0, 1)
  | 1 => (0, 0, 4)
  | 2 => (0, 1, 4)
  | 3 => (1, 1, 4)
  | 4 => (2, 0, 2)
  | 5 => (2, 0, 5)
  | 6 => (2, 2, 5)
  | 7 => (3, 2, 5)
  | 8 => (4, 0, 3)
  | 9 => (4, 0, 6)
  | 10 => (4, 3, 6)
  | 11 => (5, 3, 6)

/-- The unordered pair (as a `Finset (Fin 7)`) of object `i`. -/
def opair (i : Fin 12) : Finset (Fin 7) := {(objs i).2.1, (objs i).2.2}

/-- The host of object `i`. -/
def ohost (i : Fin 12) : Fin 6 := (objs i).1

/-- A packing `R` (a `Finset (Fin 12)`) is *feasible*: global pair-uniqueness (distinct objects
with the same underlying pair are forbidden) and per-host matching (two objects at the same host
share no vertex). -/
def Feasible (R : Finset (Fin 12)) : Prop :=
  (∀ i ∈ R, ∀ j ∈ R, i ≠ j → opair i ≠ opair j) ∧
  (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ohost i = ohost j → (opair i ∩ opair j) = ∅)

open Classical in
noncomputable instance : DecidablePred Feasible := Classical.decPred _

/-- The packing number `ν` of the instance: the maximum size of a feasible packing. -/
noncomputable def nu : ℕ := (univ.filter Feasible).sup Finset.card

/-- The coverable pairs left uncovered by `R`. Encoded via object indices whose pair no object of
`R` realises. The residual is a *`k`-leaf star centred at 0* if all its pairs contain `0` and
there are `k` of them. -/
def coveredPairs (R : Finset (Fin 12)) : Finset (Finset (Fin 7)) := R.image opair

private def witness : Finset (Fin 12) := {1, 3, 5, 7, 9, 11}

private lemma witness_feasible : Feasible witness := by
  simp only [witness, Feasible, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro i hi j hj hij
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [opair, objs] <;> decide
  · intro hh
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ohost, objs]

private lemma witness_card : witness.card = 6 := by decide

private lemma feasible_card_le_six (R : Finset (Fin 12)) (hR : Feasible R) : R.card ≤ 6 := by
  let through : Finset (Fin 12) := R.filter (fun i => 0 ∈ opair i)
  let away : Finset (Fin 12) := R.filter (fun i => 0 ∉ opair i)
  have hthrough : through.card ≤ 3 := by
    have hinj : Set.InjOn ohost (↑through : Set (Fin 12)) := by
      intro i hi j hj heq
      by_contra hne
      have hempty := hR.2 i (Finset.mem_filter.mp hi).1 j
        (Finset.mem_filter.mp hj).1 hne heq
      have hz : (0 : Fin 7) ∈ opair i ∩ opair j := Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mp hi |>.2, Finset.mem_filter.mp hj |>.2⟩
      rw [hempty] at hz
      simp at hz
    have himage : through.image ohost ⊆ ({0, 2, 4} : Finset (Fin 6)) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi0 := (Finset.mem_filter.mp hi).2
      fin_cases i <;> simp_all [opair, ohost, objs]
    calc
      through.card = (through.image ohost).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ ({0, 2, 4} : Finset (Fin 6)).card := Finset.card_le_card himage
      _ = 3 := by decide
  have haway : away.card ≤ 3 := by
    let pairs : Finset (Finset (Fin 7)) := {{1, 4}, {2, 5}, {3, 6}}
    have hinj : Set.InjOn opair (↑away : Set (Fin 12)) := by
      intro i hi j hj heq
      by_contra hne
      exact hR.1 i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne heq
    have himage : away.image opair ⊆ pairs := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi0 := (Finset.mem_filter.mp hi).2
      fin_cases i <;> simp_all [pairs, opair, objs]
    calc
      away.card = (away.image opair).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ pairs.card := Finset.card_le_card himage
      _ = 3 := by decide
  have hunion : through ∪ away = R := by
    exact Finset.filter_union_filter_not_eq (fun i => 0 ∈ opair i) R
  rw [← hunion]
  exact (Finset.card_union_le through away).trans (Nat.add_le_add hthrough haway)

/-- **STAR-T2 (§6.3).** For this instance `ν = 6`, and there is a maximum packing whose uncovered
coverable pairs form a 3-leaf star centred at `0`, while `β = 1` (every maximum packing's residual
is a star at `0`, so its matching number is `1`). Hence `β = 1` does not force a ≤2-leaf residual
star: the conjecture is FALSE. -/
theorem star_t2_nu : nu = 6 := by
  apply Nat.le_antisymm
  · unfold nu
    apply Finset.sup_le
    intro R hR
    exact feasible_card_le_six R (Finset.mem_filter.mp hR).2
  · unfold nu
    rw [← witness_card]
    apply Finset.le_sup (s := univ.filter Feasible)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, witness_feasible⟩

/-- Refutation payload: a maximum packing exists whose residual (uncovered coverable pairs) is a
star centred at `0` with 3 leaves — three distinct pairs, all containing `0`. -/
theorem star_t2_three_leaf :
    ∃ R : Finset (Fin 12), Feasible R ∧ R.card = 6 ∧
      ∃ p q r : Fin 7, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        ({0, p} : Finset (Fin 7)) ∉ coveredPairs R ∧
        ({0, q} : Finset (Fin 7)) ∉ coveredPairs R ∧
        ({0, r} : Finset (Fin 7)) ∉ coveredPairs R := by
  refine ⟨witness, witness_feasible, witness_card, 1, 2, 3, ?_⟩
  decide

end StarT2
end PaperV
