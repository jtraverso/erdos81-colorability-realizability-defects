/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Conflict systems, the copy graph H[X], and the transfer statements (§2, §3).

Ledger `LEDGER_PAPER_IV_v0.4.2.md`:
  Def 2.1 conflict system (𝒪,K) symmetric irreflexive; feasible = independent; ν.
  Def 2.2 q-multiset X and conflict graph H[X]: one vertex per copy; two copies adjacent
          when their objects conflict, and twin copies (same object) ALWAYS adjacent.
  Def 2.3 D_q, oct = D_2  (in PaperV.Core).
  Thm 3.4 (q-integral transfer, combinatorial core): |X| ≤ q·ν + D_q(H[X]).
  Thm 3.3 (½ transfer): q = 2 specialization ⇒ |X| ≤ 2·ν + oct(H[X]).

Design note: μ* is NOT modelled as an LP sup. For a resource-dominated (1/q)-integral
optimum x*, the resource constraint (Σ load ≤ 1) scaled by q forces multiplicity ≤ q, and
|X| = q·μ*. So the transfer bound μ*−ν ≤ D_q/q is exactly the integer statement
`|X| ≤ q·ν + D_q(H[X])` below, with |X| = Σ multiplicities.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Core

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpRw

@[expose] public section

open SimpleGraph Finset

namespace PaperV

/-- **Def 2.1 (conflict system).** Finite objects `O` with a symmetric, irreflexive
conflict relation `K`. -/
structure ConflictSystem where
  O : Type*
  [finO : Fintype O]
  [decEqO : DecidableEq O]
  K : O → O → Prop
  Ksymm : Symmetric K
  Kirrefl : ∀ a, ¬ K a a
  [decK : DecidableRel K]

attribute [instance] ConflictSystem.finO ConflictSystem.decEqO ConflictSystem.decK

variable (C : ConflictSystem)

/-- Feasible (independent) object set: no two members conflict. -/
def CSFeasible (S : Finset C.O) : Prop := ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ C.K a b

open Classical in
/-- The independence number `ν(C)` = max size of a feasible object set. -/
noncomputable def nu : ℕ :=
  (univ.filter (fun S : Finset C.O => CSFeasible C S)).sup Finset.card

/-- **Def 2.2 (copy graph `H[X]`).** A multiplicity function `X : O → ℕ`; copies are
`Σ o, Fin (X o)`. Two copies are adjacent iff twin copies of one object or conflicting
objects. -/
abbrev Copies (X : C.O → ℕ) : Type _ := Σ o : C.O, Fin (X o)

instance (X : C.O → ℕ) : Fintype (Copies C X) := by unfold Copies; infer_instance
instance (X : C.O → ℕ) : DecidableEq (Copies C X) := by unfold Copies; infer_instance

/-- Underlying object of a copy. -/
def objOf {X : C.O → ℕ} (c : Copies C X) : C.O := c.1

/-- The conflict graph `H[X]` on the copies of `X`. -/
def Hgraph (X : C.O → ℕ) : SimpleGraph (Copies C X) where
  Adj a b := a ≠ b ∧ (a.1 = b.1 ∨ C.K a.1 b.1)
  symm := by
    constructor
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (C.Ksymm h)
  loopless := by refine ⟨?_⟩; rintro a ⟨hne, _⟩; exact hne rfl

instance (X : C.O → ℕ) : DecidableRel (Hgraph C X).Adj := by
  intro a b; unfold Hgraph; infer_instance

/-- Total number of copies `|X| = Σ_o X o`. -/
def multSize (X : C.O → ℕ) : ℕ := ∑ o : C.O, X o

theorem card_copies (X : C.O → ℕ) : Fintype.card (Copies C X) = multSize C X := by
  simp only [Copies, multSize, Fintype.card_sigma, Fintype.card_fin]

/-- `X` is a `q`-multiset: every object has multiplicity at most `q`. -/
def IsQMultiset (X : C.O → ℕ) (q : ℕ) : Prop := ∀ o, X o ≤ q

/-- Key modelling lemma: an independent set of `H[X]` uses ≤1 copy per object, so it maps
injectively to a FEASIBLE object set of the same cardinality; hence `|S| ≤ ν(C)`. -/
theorem indep_le_nu (X : C.O → ℕ) (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) : S.card ≤ nu C := by
  classical
  let T : Finset C.O := S.image (objOf (C := C) (X := X))
  have hinj : Set.InjOn (objOf (C := C) (X := X)) S := by
    intro a ha b hb hab
    by_contra hne
    exact hS ha hb ⟨hne, Or.inl hab⟩
  have hcard : T.card = S.card := by
    exact Finset.card_image_of_injOn hinj
  have hT : CSFeasible C T := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := by
      intro heq
      subst b
      exact C.Kirrefl a.1 hxy
    exact hS ha hb ⟨hab, Or.inr hxy⟩
  rw [← hcard]
  exact Finset.le_sup (by simp [hT])

lemma exists_large_color_class {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 1 ≤ q) (c : V → Fin q) :
    ∃ i : Fin q, Fintype.card V ≤ q * (Finset.univ.filter fun v => c v = i).card := by
  by_contra h
  push_neg at h
  -- Sum of color class sizes equals |V|
  have hsum : ∑ i : Fin q, (Finset.univ.filter fun v => c v = i).card = Fintype.card V := by
    rw [← Finset.card_biUnion]
    · congr; ext v; simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hi hj
      rw [hi] at hj
      exact hij hj
  -- Since q * card_i < |V| for all i, we have q * card_i ≤ |V| - 1
  -- Summing: q * |V| ≤ q * (|V| - 1), contradiction
  by_cases hV : Fintype.card V = 0
  · -- When |V| = 0, the hypothesis q * card < 0 is impossible
    exact absurd (h ⟨0, hq⟩) (by simp [hV])
  · have hsub : Fintype.card V - 1 < Fintype.card V := Nat.sub_lt (Nat.pos_of_ne_zero hV) (by norm_num)
    have hle' : ∑ i : Fin q, q * (Finset.univ.filter fun v => c v = i).card ≤ q * (Fintype.card V - 1) := by
      calc ∑ i : Fin q, q * (Finset.univ.filter fun v => c v = i).card
          ≤ ∑ _i : Fin q, (Fintype.card V - 1) := Finset.sum_le_sum fun i _ => by
              have := h i; omega
        _ = q * (Fintype.card V - 1) := by simp
    have heq : ∑ i : Fin q, q * (Finset.univ.filter fun v => c v = i).card = q * Fintype.card V := by
      rw [← Finset.mul_sum, hsum]
    have hstrict : q * (Fintype.card V - 1) < q * Fintype.card V := Nat.mul_lt_mul_of_pos_left hsub hq
    omega

lemma card_set_compl_finset {V : Type*} [Fintype V] [DecidableEq V]
    (O : Finset V) : Fintype.card ↥((O : Set V)ᶜ) = Fintype.card V - O.card := by
  rw [Fintype.card_compl_set]
  simp

lemma colorable_complement_has_large_feasible {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q) (O : Finset V)
    (hc : (H.induce ((O : Set V)ᶜ)).Colorable q) :
    ∃ S : Finset V, Feasible H S ∧ Fintype.card V - O.card ≤ q * S.card := by
  classical
  let c := hc.some
  obtain ⟨i, hi⟩ := exists_large_color_class q hq c
  let S' : Finset ↥((O : Set V)ᶜ) := Finset.univ.filter fun v => c v = i
  let S : Finset V := S'.image Subtype.val
  have hcard : S.card = S'.card :=
    Finset.card_image_of_injOn Set.injOn_subtype_val
  refine ⟨S, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    have hca : c a' = i := (Finset.mem_filter.mp ha').2
    have hcb : c b' = i := (Finset.mem_filter.mp hb').2
    exact c.valid (SimpleGraph.induce_adj.mpr hab) (hca.trans hcb.symm)
  · rw [← card_set_compl_finset O, hcard]
    exact hi

lemma defect_values_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (q : ℕ) :
    {n | ∃ O : Finset V, IsDefectSet H q O ∧ O.card = n}.Nonempty := by
  classical
  refine ⟨Fintype.card V, Finset.univ, ?_, by simp⟩
  unfold IsDefectSet
  letI : IsEmpty ↥(((Finset.univ : Finset V) : Set V)ᶜ) :=
    ⟨fun v => by have := v.property; simp at this⟩
  exact SimpleGraph.Colorable.of_isEmpty q

/-- **Theorem 3.4 (q-integral transfer, combinatorial core).**
`|X| ≤ q · ν(C) + D_q(H[X])`. -/
theorem transfer_q (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) (hX : IsQMultiset C X q) :
    multSize C X ≤ q * nu C + Dq (Hgraph C X) q := by
  clear hX
  classical
  let H := Hgraph C X
  have hmem := Nat.sInf_mem (defect_values_nonempty H q)
  change Dq H q ∈ {n | ∃ O : Finset (Copies C X),
    IsDefectSet H q O ∧ O.card = n} at hmem
  obtain ⟨O, hO, hOcard⟩ := hmem
  obtain ⟨S, hS, hlarge⟩ :=
    colorable_complement_has_large_feasible H q hq O hO
  have hSnub : S.card ≤ nu C := indep_le_nu C X S hS
  have hcopies : Fintype.card (Copies C X) = multSize C X := card_copies C X
  have hmul : q * S.card ≤ q * nu C := Nat.mul_le_mul_left q hSnub
  change O.card = Dq H q at hOcard
  change multSize C X ≤ q * nu C + Dq H q
  omega

/-- **Theorem 3.3 (half-integral transfer).** The `q = 2` specialization. -/
theorem transfer_half (X : C.O → ℕ) (hX : IsQMultiset C X 2) :
    multSize C X ≤ 2 * nu C + oct (Hgraph C X) := by
  have := transfer_q C X 2 (by norm_num) hX
  simpa [oct] using this

end PaperV
