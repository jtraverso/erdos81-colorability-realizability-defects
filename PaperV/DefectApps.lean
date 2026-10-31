/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — Applications of the defect machinery (v0.9.15 candidate).

Two payoffs that land the abstract `D_q`/`oct` results on named objects:

* `oct_eq_zero_iff_no_odd_loop` — `oct(H) = 0` iff `H` has no odd closed walk, i.e. `oct` really is
  the odd-cycle-transversal number (combines `oct_eq_zero_iff` with the bipartite characterisation).
* `conflict_defect_lower` — the extremal lower bound instantiated on the paper's actual conflict graph
  `H[X]`: `multSize(X) − q·ν ≤ D_q(H[X])`, in terms of the conflict system's packing number `ν`.
-/
module

public import PaperV.DqBasic
public import PaperV.OddCycle
public import PaperV.Extremal
public import PaperV.ConflictGraph

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext

@[expose] public section

open SimpleGraph Finset

namespace PaperV

section Oct
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`oct` is the odd-cycle-transversal invariant:** `oct H = 0` iff every closed walk of `H` has
even length (equivalently `H` has no odd cycle, i.e. `H` is bipartite). Combines `oct_eq_zero_iff`
with `two_colorable_iff_forall_loop_even`. -/
theorem oct_eq_zero_iff_no_odd_loop (H : SimpleGraph V) [DecidableRel H.Adj] :
    oct H = 0 ↔ ∀ (v : V) (c : H.Walk v v), Even c.length := by
  rw [oct_eq_zero_iff, two_colorable_iff_forall_loop_even]

end Oct

section Conflict
variable {C : ConflictSystem}

/-- **Concrete extremal lower bound on the conflict system.** The colourability defect of the actual
conflict graph `H[X]` is at least the deficit `multSize(X) − q·ν`, with `ν` the packing number of the
conflict system. Instantiates `Dq_ge_card_sub` at `H := H[X]` with `indep_le_nu`. -/
theorem conflict_defect_lower (X : C.O → ℕ) {q : ℕ} (hq : 1 ≤ q) :
    multSize C X - q * nu C ≤ Dq (Hgraph C X) q := by
  have h := Dq_ge_card_sub (Hgraph C X) hq (fun S hS => indep_le_nu C X S hS)
  rwa [card_copies] at h

/-- Concrete: the conflict-graph defect is antitone in the number of colours. -/
theorem conflict_Dq_antitone (X : C.O → ℕ) {q q' : ℕ} (hq : 1 ≤ q) (hqq : q ≤ q') :
    Dq (Hgraph C X) q' ≤ Dq (Hgraph C X) q :=
  Dq_antitone (Hgraph C X) hq hqq

/-- Concrete: `oct(H[X]) = 0` iff the conflict graph has no odd closed walk (is bipartite). -/
theorem conflict_oct_eq_zero_iff (X : C.O → ℕ) :
    oct (Hgraph C X) = 0 ↔ ∀ (v : Copies C X) (c : (Hgraph C X).Walk v v), Even c.length :=
  oct_eq_zero_iff_no_odd_loop (Hgraph C X)

/-- Concrete: the conflict-graph defect vanishes exactly at/above its chromatic number. -/
theorem conflict_Dq_eq_zero_iff_chromatic (X : C.O → ℕ) {q : ℕ} (hq : 1 ≤ q) :
    Dq (Hgraph C X) q = 0 ↔ (Hgraph C X).chromaticNumber ≤ (q : ℕ∞) :=
  Dq_eq_zero_iff_chromatic (Hgraph C X) hq

end Conflict

section Examples
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem induce_top_eq (s : Set V) : (⊤ : SimpleGraph V).induce s = ⊤ := by
  ext a b; simp [SimpleGraph.induce, Subtype.ext_iff]

theorem colorable_top_induce_iff (O : Finset V) (q : ℕ) :
    ((⊤ : SimpleGraph V).induce ((O : Set V)ᶜ)).Colorable q ↔ Fintype.card ↥((O : Set V)ᶜ) ≤ q := by
  rw [induce_top_eq, ← chromaticNumber_le_iff_colorable, chromaticNumber_top]
  exact_mod_cast Iff.rfl

/-- **Extremal witness: the complete graph.** `D_q(K_n) = n − q` — the splitting/defect bounds are
tight (`K_n` needs all-but-`q` of its `n` vertices deleted to become `q`-colourable). -/
theorem Dq_top (q : ℕ) : Dq (⊤ : SimpleGraph V) q = Fintype.card V - q := by
  have hcompl : ∀ O : Finset V, Fintype.card ↥((O : Set V)ᶜ) = Fintype.card V - O.card := by
    intro O; rw [Fintype.card_compl_set]; congr 1; simp
  apply le_antisymm
  · obtain ⟨O, _, hOcard⟩ := Finset.exists_subset_card_eq
      (show Fintype.card V - q ≤ (Finset.univ : Finset V).card by
        rw [Finset.card_univ]; exact Nat.sub_le _ _)
    apply Nat.sInf_le
    refine ⟨O, ?_, hOcard⟩
    rw [IsDefectSet, colorable_top_induce_iff, hcompl, hOcard]
    omega
  · apply le_csInf
    · exact ⟨Fintype.card V, Finset.univ,
        by rw [IsDefectSet, colorable_top_induce_iff, hcompl]; simp, Finset.card_univ⟩
    · rintro n ⟨O, hO, rfl⟩
      rw [IsDefectSet, colorable_top_induce_iff, hcompl] at hO
      have hOle : O.card ≤ Fintype.card V := Finset.card_le_univ O
      omega

/-- `oct(K_n) = n − 2`: the complete graph is the extremal non-bipartite example. -/
theorem oct_top : oct (⊤ : SimpleGraph V) = Fintype.card V - 2 := Dq_top 2

/-- Independence number of `G` = clique number of its complement. -/
noncomputable def indepNum (G : SimpleGraph V) : ℕ := Gᶜ.cliqueNum

theorem feasible_card_le_indepNum (G : SimpleGraph V) (S : Finset V) (hS : Feasible G S) :
    S.card ≤ indepNum G := by
  apply IsClique.card_le_cliqueNum (G := Gᶜ) (t := S)
  intro a ha b hb hab
  exact ⟨hab, hS ha hb⟩

/-- **Extremal lower bound via the independence number** `α(G)`: `|V| − q·α(G) ≤ D_q(G)`.
Connects the defect to the classical independence number (`cliqueNum` of the complement). -/
theorem Dq_ge_card_sub_indepNum (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq : 1 ≤ q) :
    Fintype.card V - q * indepNum G ≤ Dq G q :=
  Dq_ge_card_sub G hq (fun S hS => feasible_card_le_indepNum G S hS)

end Examples

end PaperV
