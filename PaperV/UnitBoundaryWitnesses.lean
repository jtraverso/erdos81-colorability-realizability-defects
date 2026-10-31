/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Appendix A closure: (1) glue between the resource model and `ConflictSystem`;
(2) finite witnesses for the unit-boundary kernels and their stated limits (AV5441 §5/§7).

Glue.  `resCS res` is the conflict system "distinct objects whose resource sets meet"; its feasible
sets are exactly the `ResFeasible` families and `nu (resCS res) = packOpt res univ`. So Lemma A / B
are statements about `nu` of a conflict system of Definition 2.1, not a parallel framework.

Witnesses (all by `decide` on `Fin` types; no kernel-bypassing decision procedure):
  W1  duplicated frontier: two outer objects on different pages share one shared resource;
      `packOpt = z + |B| + ν_D(B) = 0 + 1 + 0 = 1`  (Lemma A instance, non-empty).
  W2  weights break Lemma A: a central of weight 100 vs an outer of weight 1 on the same resource;
      every normalized packing has weight 1, a feasible packing has weight 100.
  W3  two shared resources per outer object break the normalization: the outer object blocks two
      disjoint centrals and contributes one; every normalized packing has size 1 < packOpt = 2.
  W4  Lemma B is tight: `h = |B₁ \ B₀| = 1` is attained and the natural inequality holds with equality.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.UnitBoundaryCompletion
public import PaperV.ConflictGraph

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext

@[expose] public section

open Finset

namespace PaperV

namespace UnitBoundary

/-! ### Glue: resource model ↔ `ConflictSystem` (Definition 2.1) -/

variable {α R : Type*} [Fintype α] [DecidableEq α] [DecidableEq R]

/-- The conflict system induced by resource incidence: distinct objects conflict iff their
resource sets meet. -/
abbrev resCS (res : α → Finset R) : ConflictSystem where
  O := α
  K a b := a ≠ b ∧ ¬ Disjoint (res a) (res b)
  Ksymm := by
    rintro a b ⟨hne, hd⟩
    exact ⟨hne.symm, fun h => hd h.symm⟩
  Kirrefl := by rintro a ⟨h, _⟩; exact h rfl
  decK := by intro a b; infer_instance

theorem csFeasible_resCS_iff (res : α → Finset R) (S : Finset α) :
    CSFeasible (resCS res) S ↔ ResFeasible res S := by
  constructor
  · intro h a ha b hb hne
    by_contra hd
    exact h ha hb ⟨hne, hd⟩
  · rintro h a ha b hb ⟨hne, hd⟩
    exact hd (h ha hb hne)

private theorem feasible_card_le_nu (C : ConflictSystem) (P : Finset C.O)
    (hP : CSFeasible C P) : P.card ≤ nu C := by
  classical
  unfold nu
  exact Finset.le_sup (by simp [hP])

/-- `ν` of the induced conflict system is the packing optimum of the whole universe. -/
theorem nu_resCS (res : α → Finset R) : nu (resCS res) = packOpt res Finset.univ := by
  classical
  apply Nat.le_antisymm
  · unfold nu
    apply Finset.sup_le
    intro P hP
    exact le_packOpt res (Finset.subset_univ P)
      ((csFeasible_resCS_iff res P).mp (Finset.mem_filter.mp hP).2)
  · apply packOpt_le
    intro P _ hP
    exact feasible_card_le_nu (resCS res) P ((csFeasible_resCS_iff res P).mpr hP)

/-! ### Evaluation lemmas for the (classically defined) optima on finite instances -/

instance instDecidableResFeasible (res : α → Finset R) : DecidablePred (ResFeasible res) :=
  fun P => by unfold ResFeasible; infer_instance

theorem packOpt_eq_of {res : α → Finset R} {U : Finset α} {n : ℕ}
    (h1 : ∃ P ∈ U.powerset, ResFeasible res P ∧ P.card = n)
    (h2 : ∀ P ∈ U.powerset, ResFeasible res P → P.card ≤ n) : packOpt res U = n := by
  obtain ⟨P, hP, hf, hc⟩ := h1
  apply le_antisymm
  · exact packOpt_le res (fun P hP hf => h2 P (Finset.mem_powerset.mpr hP) hf)
  · rw [← hc]; exact le_packOpt res (Finset.mem_powerset.mp hP) hf

theorem nuAvoid_eq_of {res : α → Finset R} {D : Finset α} {Bd : Finset R} {n : ℕ}
    (h1 : ∃ T ∈ D.powerset, (ResFeasible res T ∧ ∀ d ∈ T, Disjoint (res d) Bd) ∧ T.card = n)
    (h2 : ∀ T ∈ D.powerset, (ResFeasible res T ∧ ∀ d ∈ T, Disjoint (res d) Bd) → T.card ≤ n) :
    nuAvoid res D Bd = n := by
  obtain ⟨T, hT, hf, hc⟩ := h1
  apply le_antisymm
  · obtain ⟨T', hT', hf', hav', hc'⟩ := exists_nuAvoid res D Bd
    rw [← hc']; exact h2 T' (Finset.mem_powerset.mpr hT') ⟨hf', hav'⟩
  · rw [← hc]; exact le_nuAvoid res (Finset.mem_powerset.mp hT) hf.1 hf.2

/-! ### Finite witnesses -/

section Witnesses

/-- W1 — duplicated frontier. Objects `0,1` are outer (pages with private resources `1`, `2`), both
using the shared resource `0`; object `2` is central on `{0}`. -/
def res1 : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0}

theorem w1_config : Config res1 {0, 1} {2} {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem w1_ZB : (Z res1 {0, 1} {0}).card = 0 ∧ B res1 {0, 1} {0} = {0} := by decide

theorem w1_nuAvoid : nuAvoid res1 {2} {0} = 0 :=
  nuAvoid_eq_of ⟨∅, by decide, by decide, rfl⟩ (by decide)

/-- Lemma A instance: the optimum is `0 + 1 + 0 = 1` (both pages want resource `0`; one survives). -/
theorem w1_packOpt : packOpt res1 ({0, 1} ∪ {2}) = 1 :=
  packOpt_eq_of ⟨{0}, by decide, by decide, rfl⟩ (by decide)

/-- Consistency with Lemma A on this instance. -/
theorem w1_lemmaA_check : packOpt res1 ({0, 1} ∪ {2}) =
    (Z res1 {0, 1} {0}).card + (B res1 {0, 1} {0}).card + nuAvoid res1 {2} (B res1 {0, 1} {0}) := by
  rw [w1_packOpt, w1_ZB.1, w1_ZB.2, w1_nuAvoid]; rfl

/-- W2 — weights break Lemma A. Outer `0` (weight 1) and central `1` (weight 100) on resource `0`. -/
def res2 : Fin 2 → Finset (Fin 1)
  | 0 => {0}
  | 1 => {0}

def w2 : Fin 2 → ℕ
  | 0 => 1
  | 1 => 100

theorem w2_config : Config res2 {0} {1} {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The only representative choice. -/
def reps2 : Reps res2 {0} {0} where
  rep := fun _ => 0
  rep_mem := by decide
  rep_uses := by decide

/-- Every normalized (cardinality-optimal) packing has weight `1`, while `{1}` is feasible with
weight `100`: the completion lemma does not extend to weights. -/
theorem w2_weights_fail :
    ∃ P ⊆ ({0} ∪ {1} : Finset (Fin 2)), ResFeasible res2 P ∧
      ∀ C ∈ ({1} : Finset (Fin 2)).powerset, (∀ d ∈ C, Disjoint (res2 d) (B res2 {0} {0})) →
        ∑ o ∈ normPack reps2 C, w2 o < ∑ o ∈ P, w2 o := by
  refine ⟨{1}, by decide, by decide, ?_⟩
  decide

/-- W3 — two shared resources per outer object. Outer `0` uses shared `{0,1}`; centrals `1`, `2` use
`{0}`, `{1}`. The unit hypothesis fails, and so does the normalization: `packOpt = 2` while any
normalized packing has one element. -/
def res3 : Fin 3 → Finset (Fin 2)
  | 0 => {0, 1}
  | 1 => {0}
  | 2 => {1}

theorem w3_not_unit : ¬ (∀ o ∈ ({0} : Finset (Fin 3)), (res3 o ∩ {0, 1}).card ≤ 1) := by decide

theorem w3_packOpt : packOpt res3 ({0} ∪ {1, 2}) = 2 :=
  packOpt_eq_of ⟨{1, 2}, by decide, by decide, rfl⟩ (by decide)

theorem w3_B : B res3 {0} {0, 1} = {0, 1} := by decide

theorem w3_normPack_small (reps : Reps res3 {0} {0, 1}) (C : Finset (Fin 3)) (hC : C ⊆ {1, 2})
    (hav : ∀ d ∈ C, Disjoint (res3 d) (B res3 {0} {0, 1})) :
    (normPack reps C).card + 1 ≤ packOpt res3 ({0} ∪ {1, 2}) := by
  rw [w3_packOpt]
  have key : ∀ d ∈ ({1, 2} : Finset (Fin 3)), ¬ Disjoint (res3 d) {0, 1} := by decide
  have hC0 : C = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    exact key d (hC hd) (w3_B ▸ hav d hd)
  subst hC0
  have hsub : normPack reps ∅ ⊆ {0} := by
    intro x hx
    unfold normPack at hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Z_subset h
      · exact (Finset.mem_sdiff.mp (repSet_subset reps h)).1
    · exact absurd h (Finset.notMem_empty x)
  have := Finset.card_le_card hsub
  simp at this
  omega

/-- W4 — Lemma B is tight. `R = Fin 2`, shared `SR = {0}`; `Q₀ = {0}` with private resource `1`
(so `z₀ = 1, B₀ = ∅`), `Q₁ = {2}` on the shared resource (`z₁ = 0, B₁ = {0}`), central `D = {1}` on
`{0}`. Transporting `C₀ = {1}` removes it: `h = 1 = |B₁ \ B₀|`, and
`|P₀| + z₁ = 2 = |P₁| + z₀ + |B₀ \ B₁|`. -/
def res4 : Fin 3 → Finset (Fin 2)
  | 0 => {1}
  | 1 => {0}
  | 2 => {0}

theorem w4_config₀ : Config res4 {0} {1} {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem w4_config₁ : Config res4 {2} {1} {0} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

def reps4₀ : Reps res4 {0} {0} where
  rep := fun _ => 0
  rep_mem := by decide
  rep_uses := by decide

def reps4₁ : Reps res4 {2} {0} where
  rep := fun _ => 2
  rep_mem := by decide
  rep_uses := by decide

theorem w4_tight :
    (B res4 {2} {0} \ B res4 {0} {0}).card = 1 ∧
    (normPack reps4₁ (keptCentral res4 {1} (B res4 {2} {0}))).card + 1 =
      (Z res4 {2} {0}).card + (B res4 {2} {0}).card + ({1} : Finset (Fin 3)).card ∧
    (normPack reps4₀ {1}).card + (Z res4 {2} {0}).card =
      (normPack reps4₁ (keptCentral res4 {1} (B res4 {2} {0}))).card + (Z res4 {0} {0}).card +
        (B res4 {0} {0} \ B res4 {2} {0}).card := by
  decide

end Witnesses

end UnitBoundary

end PaperV
