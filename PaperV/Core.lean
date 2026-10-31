/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Core: colourability defect (oct / D_q) and the splitting lemma (Lemma 3.1, Cor 3.2).

Ledger `LEDGER_PAPER_IV_v0.4.2.md`:
  Def 2.3  D_q(H) = min #vertices to delete to make H q-colourable; oct = D_2.
  Lemma 3.1 (splitting): for every 2-multiset X, ∃ disjoint feasible S₁,S₂ ⊆ X with
             |S₁|+|S₂| ≥ |X| − oct(H[X]).   [feasible = independent set in H[X]]
  Cor 3.2:   ν ≥ ⌈(|X| − oct)/2⌉.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.

We phrase the splitting lemma at the level of a finite SimpleGraph H (= H[X]); "feasible"
= independent set of H. The multiset semantics (twin copies adjacent ⇒ each colour class has
≤1 copy per object) is layered on top when H is instantiated as H[X].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `O` is a `q`-bipartizer of `H` if deleting `O` leaves a `q`-colourable graph. -/
def IsDefectSet (H : SimpleGraph V) (q : ℕ) (O : Finset V) : Prop :=
  (H.induce ((O : Set V)ᶜ)).Colorable q

/-- The colourability defect `D_q(H)`: minimum size of a set whose deletion makes `H`
`q`-colourable. `oct = D_2`. -/
noncomputable def Dq (H : SimpleGraph V) (q : ℕ) : ℕ :=
  sInf { n | ∃ O : Finset V, IsDefectSet H q O ∧ O.card = n }

/-- Odd-cycle-transversal number `oct(H) = D_2(H)`. -/
noncomputable def oct (H : SimpleGraph V) : ℕ := Dq H 2

/-- A finite set is *feasible* (independent) in `H` if no two of its members are adjacent. -/
def Feasible (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ H.Adj a b

/-- The defect-set family is nonempty (delete everything ⇒ empty graph is `q`-colourable for
`q ≥ 1`; and even `q = 0` fails only on nonempty vertex set, but we only ever use `q ≥ 1`). -/
theorem defectSet_nonempty (H : SimpleGraph V) {q : ℕ} (hq : 1 ≤ q) :
    { n | ∃ O : Finset V, IsDefectSet H q O ∧ O.card = n }.Nonempty := by
  refine ⟨Fintype.card V, Finset.univ, ?_, Finset.card_univ⟩
  unfold IsDefectSet
  letI : IsEmpty ↥(((Finset.univ : Finset V) : Set V)ᶜ) :=
    ⟨fun x => by simpa using x.property⟩
  exact SimpleGraph.Colorable.of_isEmpty q

/-- **Lemma 3.1 (splitting).** For every finite graph `H` there exist disjoint feasible
(independent) sets `S₁, S₂` with `|S₁| + |S₂| ≥ |V| − oct(H)`. -/
theorem splitting (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ S₁ S₂ : Finset V, Disjoint S₁ S₂ ∧ Feasible H S₁ ∧ Feasible H S₂ ∧
      Fintype.card V - oct H ≤ S₁.card + S₂.card := by
  -- The set of defect sizes is nonempty
  have hne := defectSet_nonempty H (by norm_num : 1 ≤ 2)
  -- oct(H) is attained by some defect set O
  have hoct : ∃ O : Finset V, IsDefectSet H 2 O ∧ O.card = oct H := by
    have := Nat.sInf_mem hne
    exact this
  obtain ⟨O, hO_defect, hO_card⟩ := hoct
  -- H.induce(Oᶜ) is 2-colourable
  rw [IsDefectSet] at hO_defect
  obtain ⟨col, hcol⟩ := hO_defect
  -- Define S₁ and S₂ as the two colour classes
  let OcType := {v : V // v ∉ O}
  let S₁' : Finset OcType := Finset.univ.filter (fun v => col v = 0)
  let S₂' : Finset OcType := Finset.univ.filter (fun v => col v = 1)
  let S₁ : Finset V := S₁'.map ⟨Subtype.val, Subtype.val_injective⟩
  let S₂ : Finset V := S₂'.map ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨S₁, S₂, ?_, ?_, ?_, ?_⟩
  -- Disjoint
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    rw [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [OcType, S₁', S₂', Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    have : a' = b' := Subtype.val_injective hab
    subst this
    rw [ha'] at hb'
    exact Fin.zero_ne_one hb'
  -- S₁ is feasible
  · intro a ha b hb hab
    rw [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [OcType, S₁', Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    have hadj : (H.induce (↑O)ᶜ).Adj a' b' := hab
    have hne := SimpleGraph.Adj.ne (hcol hadj)
    rw [ha', hb'] at hne
    exact hne rfl
  -- S₂ is feasible
  · intro a ha b hb hab
    rw [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [OcType, S₂', Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    have hadj : (H.induce (↑O)ᶜ).Adj a' b' := hab
    have hne := SimpleGraph.Adj.ne (hcol hadj)
    rw [ha', hb'] at hne
    exact hne rfl
  -- Cardinality bound
  · -- S₁' ∪ S₂' = univ, and |S₁'| + |S₂'| = |univ| = |Oᶜ|
    have hunion : S₁' ∪ S₂' = Finset.univ := by
      ext x
      simp only [Finset.mem_union, OcType, S₁', S₂', Finset.mem_filter, Finset.mem_univ, true_and]
      have h : (col x).val < 2 := Fin.is_lt (col x)
      have h01 : (col x).val = 0 ∨ (col x).val = 1 := by omega
      rcases h01 with h01 | h01 <;> simp [Fin.ext_iff, h01]
    have hcard : S₁'.card + S₂'.card = Fintype.card OcType := by
      rw [← Finset.card_union_of_disjoint]
      · rw [hunion]
        exact Finset.card_univ
      · rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        simp only [OcType, S₁', S₂', Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have heq : a = b := by simpa using hab
        subst heq
        simp [ha] at hb
    have hcard_S1 : S₁.card = S₁'.card := Finset.card_map _
    have hcard_S2 : S₂.card = S₂'.card := Finset.card_map _
    rw [hcard_S1, hcard_S2, hcard]
    -- Fintype.card OcType = Fintype.card V - |O| = Fintype.card V - oct H
    have hcardO : Fintype.card {x // x ∈ O} = O.card := Fintype.card_ofFinset O (fun x => Iff.rfl)
    have heq : Fintype.card OcType = Fintype.card V - O.card := by
      rw [Fintype.card_subtype_compl, hcardO]
    rw [heq, hO_card]

/-- **Corollary 3.2.** The independence number is at least `⌈(|V| − oct)/2⌉`; concretely the
larger of the two split classes has card `≥ (|V| − oct + 1)/2`. -/
theorem splitting_half (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ S : Finset V, Feasible H S ∧ (Fintype.card V - oct H + 1) / 2 ≤ S.card := by
  obtain ⟨S₁, S₂, _, h₁, h₂, hcard⟩ := splitting H
  by_cases hle : S₁.card ≤ S₂.card
  · exact ⟨S₂, h₂, by omega⟩
  · exact ⟨S₁, h₁, by omega⟩

end PaperV
