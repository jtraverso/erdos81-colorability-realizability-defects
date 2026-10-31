/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — §5.2 SEAL, Proposition 5.1 (finite-run feasibility).  Ledger node L-8.

A host-clique packing is FEASIBLE iff it maintains two invariants:
  (per-host matching)  the pairs assigned to any one host are pairwise vertex-disjoint;
  (pair uniqueness)    each global pair is assigned to at most one host.
Every SEAL repair move (N1 relocate-insert, N2 two-step rotation) is a composition of "legal
steps": delete an assignment, or insert `(j,e)` ONLY when `e` is globally uncovered and both
endpoints of `e` are unmatched at host `j`. Prop 5.1 = every legal step preserves feasibility,
hence every finite execution stays feasible.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/

module

public import Mathlib.Data.Finset.Basic

@[expose] public section

open Finset

namespace PaperV

/-- A host-clique assignment: a host `j : J` together with an unordered pair of vertices
`{a,b} ⊆ W`, encoded as an ordered pair with `a ≠ b` handled by the feasibility predicate. -/
structure Assign (J W : Type*) where
  host : J
  a : W
  b : W
  deriving DecidableEq

variable {J W : Type*} [DecidableEq J] [DecidableEq W]

/-- The two endpoints of an assignment as a `Finset W`. -/
def Assign.ends (x : Assign J W) : Finset W := {x.a, x.b}

/-- Two assignments at the same host clash if they share a vertex (violating the per-host
matching). -/
def hostClash (x y : Assign J W) : Prop :=
  x.host = y.host ∧ (x.ends ∩ y.ends).Nonempty

/-- A packing `R` (a `Finset` of assignments) is *feasible*:
(1) no two distinct assignments at the same host share a vertex (per-host matching), and
(2) no global pair is used by two distinct assignments (pair uniqueness). -/
def SealFeasible (R : Finset (Assign J W)) : Prop :=
  (∀ x ∈ R, ∀ y ∈ R, x ≠ y → x.host = y.host → (x.ends ∩ y.ends) = ∅) ∧
  (∀ x ∈ R, ∀ y ∈ R, x.ends = y.ends → x.host = y.host)

/-- The pair `e = {a,b}` is *uncovered* by `R` (no assignment uses that global pair). -/
def Uncovered (R : Finset (Assign J W)) (a b : W) : Prop :=
  ∀ x ∈ R, x.ends ≠ ({a, b} : Finset W)

/-- Vertex `w` is *free at host `j`* in `R` (unmatched there). -/
def FreeAt (R : Finset (Assign J W)) (j : J) (w : W) : Prop :=
  ∀ x ∈ R, x.host = j → w ∉ x.ends

/-- A legal insertion: add `(j, {a,b})` when the pair is globally uncovered and both endpoints
are free at `j`, and `a ≠ b`. -/
theorem feasible_insert (R : Finset (Assign J W)) (hR : SealFeasible R)
    (j : J) (a b : W) (hab : a ≠ b)
    (hunc : Uncovered R a b) (hfa : FreeAt R j a) (hfb : FreeAt R j b) :
    SealFeasible (insert ⟨j, a, b⟩ R) := by
  constructor
  · intro x hx y hy hxy hhost
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hxy rfl).elim
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hznew := (Finset.mem_inter.mp hz).1
        have hzy := (Finset.mem_inter.mp hz).2
        have hzab : z = a ∨ z = b := by
          simpa [Assign.ends] using hznew
        rcases hzab with hza | hzb
        · exact hfa y hy hhost.symm (hza ▸ hzy)
        · exact hfb y hy hhost.symm (hzb ▸ hzy)
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzx := (Finset.mem_inter.mp hz).1
        have hznew := (Finset.mem_inter.mp hz).2
        have hzab : z = a ∨ z = b := by
          simpa [Assign.ends] using hznew
        rcases hzab with hza | hzb
        · exact hfa x hx hhost (hza ▸ hzx)
        · exact hfb x hx hhost (hzb ▸ hzx)
      · exact hR.1 x hx y hy hxy hhost
  · intro x hx y hy hends
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rfl
      · exact ((hunc y hy) hends.symm).elim
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ((hunc x hx) hends).elim
      · exact hR.2 x hx y hy hends

/-- A legal deletion always preserves feasibility. -/
theorem feasible_erase (R : Finset (Assign J W)) (hR : SealFeasible R) (x : Assign J W) :
    SealFeasible (R.erase x) := by
  constructor
  · intro y hy z hz hyz hhost
    exact hR.1 y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz hhost
  · intro y hy z hz hends
    exact hR.2 y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hends

/-- **Proposition 5.1 (finite-run feasibility).** Any packing reached from a feasible one by a
finite sequence of legal deletions/insertions is feasible. Formalised as: the reflexive-
transitive closure of the legal-step relation preserves feasibility. -/
inductive LegalStep : Finset (Assign J W) → Finset (Assign J W) → Prop
  | erase (R : Finset (Assign J W)) (x : Assign J W) : LegalStep R (R.erase x)
  | insert (R : Finset (Assign J W)) (j : J) (a b : W) :
      a ≠ b → Uncovered R a b → FreeAt R j a → FreeAt R j b →
      LegalStep R (insert ⟨j, a, b⟩ R)

theorem feasible_run {R R' : Finset (Assign J W)} (hR : SealFeasible R)
    (h : Relation.ReflTransGen LegalStep R R') : SealFeasible R' := by
  induction h with
  | refl => exact hR
  | tail hstep hlegal ih =>
      cases hlegal with
      | erase x => exact feasible_erase _ ih x
      | insert j a b hab hunc hfa hfb =>
          exact feasible_insert _ ih j a b hab hunc hfa hfb

end PaperV
