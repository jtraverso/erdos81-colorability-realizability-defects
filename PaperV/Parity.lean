/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Lemma 3.5 (parity localization).  Ledger node L-2 (auxiliary; NOT in the main chain).

  oct(H) ≤ τ( internal-edge subgraph of a bipartition A ⊎ Aᶜ ).

Reason: deleting a vertex cover of the internal edges leaves only cross edges, which is
bipartite with parts A, Aᶜ; hence that cover is an odd-cycle transversal.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Core

import Mathlib.Tactic.Tauto

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `C` is a vertex cover of `H`: every edge has an endpoint in `C`. -/
def IsVertexCover (H : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃a b⦄, H.Adj a b → a ∈ C ∨ b ∈ C

/-- Vertex-cover number `τ(H)`. -/
noncomputable def tau (H : SimpleGraph V) : ℕ :=
  sInf { n | ∃ C : Finset V, IsVertexCover H C ∧ C.card = n }

/-- The internal-edge subgraph of the bipartition `A ⊎ Aᶜ`: keep only edges whose endpoints
lie on the same side. -/
def internalGraph (H : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ ((a ∈ A ∧ b ∈ A) ∨ (a ∉ A ∧ b ∉ A))
  symm := by
    constructor
    rintro a b ⟨hab, h⟩
    exact ⟨hab.symm, by tauto⟩
  loopless := by refine ⟨fun a h => ?_⟩; exact h.1.ne rfl

instance (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) :
    DecidableRel (internalGraph H A).Adj := by
  intro a b; unfold internalGraph; infer_instance

/-- **Lemma 3.5 (parity localization).** `oct(H) ≤ τ` of the internal-edge subgraph. -/
theorem parity_localization (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) :
    oct H ≤ tau (internalGraph H A) := by
  unfold tau oct
  apply csInf_le_csInf
  · -- BddBelow: all naturals are ≥ 0
    use 0
    intro n ⟨_, _, hn⟩
    rw [← hn]
    exact Nat.zero_le _
  · -- Nonempty: there exists a vertex cover (e.g., univ)
    refine ⟨Fintype.card V, Finset.univ, ?_, rfl⟩
    intro a b _
    exact Or.inl (Finset.mem_univ _)
  · -- Subset: vertex covers of internalGraph are defect sets for H
    intro n hn
    obtain ⟨C, hC_vc, hn_eq⟩ := hn
    refine ⟨C, ?_, hn_eq⟩
    -- Need to show H.induce(Cᶜ) is 2-colorable
    -- Key: all edges in H.induce(Cᶜ) are cross edges between A and Aᶜ
    -- So we can color A ∩ Cᶜ with color 0 and Aᶜ ∩ Cᶜ with color 1
    rw [IsDefectSet]
    -- Define coloring: v ↦ 0 if v ∈ A, 1 otherwise
    let color : Set.compl (C : Set V) → Fin 2 := fun v => if v.val ∈ A then 0 else 1
    refine ⟨color, ?_⟩
    intro a b hab
    -- a, b are adjacent in H.induce(Cᶜ), so H.Adj a b and a, b ∉ C
    rw [SimpleGraph.induce_adj] at hab
    have hadj := hab
    -- Since C is a vertex cover of internalGraph, and a, b ∉ C, the edge (a,b) is not internal
    -- So it's a cross edge: (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)
    have haC : (a : V) ∉ C := a.prop
    have hbC : (b : V) ∉ C := b.prop
    -- If (a,b) were an internal edge, C would cover it, contradiction
    have hnot_internal : ¬(internalGraph H A).Adj a b := by
      intro h
      have := hC_vc h
      cases this with
      | inl h => exact haC h
      | inr h => exact hbC h
    -- So the edge is a cross edge: exactly one endpoint in A
    simp [internalGraph] at hnot_internal
    have hnot_both_A : (a : V) ∈ A → (b : V) ∉ A := (hnot_internal hadj).1
    have hnot_both_Ac : (a : V) ∉ A → (b : V) ∈ A := (hnot_internal hadj).2
    -- Colors are different
    simp [completeGraph, color]
    by_cases haA : (a : V) ∈ A
    · simp [haA, hnot_both_A haA]
    · simp [haA, hnot_both_Ac haA]

end PaperV
