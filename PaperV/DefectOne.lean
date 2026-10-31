/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV/V — The `q = 1` defect and the scope of the edge-defect profile (Proposition 3.10).

`D_1(H) = |V(H)| − α(H)`: making a graph 1-colourable means keeping an independent set, so the
minimum deletion is the complement of a maximum independent set. On a line graph this reads
`D_1(L(G)) = |E(G)| − ν_match(G)`.

Consequence for Proposition 3.10: `Δ(G)` and the Class 1/2 bit determine WHERE the profile
`q ↦ D_q(L(G))` vanishes, not its positive values. Witness: `L(P₄) ≅ P₃` and `L(C₄) ≅ C₄` (both
`P₄, C₄` have `Δ = 2`), the two line graphs have the same zero set (`D_2 = 0`), but `D_1 = 1` vs `2`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.DefectApps
public import PaperV.LineGraph

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A maximum independent (feasible) set exists and has size `α(H)`. -/
theorem exists_feasible_card_indepNum (H : SimpleGraph V) :
    ∃ S : Finset V, Feasible H S ∧ S.card = indepNum H := by
  obtain ⟨s, hs⟩ := (Hᶜ).exists_isNClique_cliqueNum
  refine ⟨s, ?_, hs.2⟩
  intro a ha b hb hadj
  by_cases hab : a = b
  · subst hab; exact H.irrefl hadj
  · exact (hs.1 ha hb hab).2 hadj

/-- Upper bound: delete the complement of a maximum independent set. -/
theorem Dq_one_le (H : SimpleGraph V) [DecidableRel H.Adj] :
    Dq H 1 ≤ Fintype.card V - indepNum H := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_feasible_card_indepNum H
  unfold Dq
  apply Nat.sInf_le
  refine ⟨Finset.univ \ S, ?_, by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]⟩
  unfold IsDefectSet
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) ?_⟩
  intro v w hvw _
  have hv : v.1 ∈ S := by
    have := v.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      not_not] at this
    exact this
  have hw : w.1 ∈ S := by
    have := w.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      not_not] at this
    exact this
  exact hS hv hw (SimpleGraph.induce_adj.mp hvw)

/-- **`D_1(H) = |V(H)| − α(H)`.** -/
theorem Dq_one_eq (H : SimpleGraph V) [DecidableRel H.Adj] :
    Dq H 1 = Fintype.card V - indepNum H := by
  apply le_antisymm (Dq_one_le H)
  have := Dq_ge_card_sub_indepNum H (le_refl 1)
  simpa using this

/-- **`D_1(L(G)) = |E(G)| − ν_match(G)`**, where `ν_match(G) = α(L(G))` (independent sets of the line
graph are the matchings, `feasible_lineGraph_iff`). -/
theorem Dq_one_lineGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    Dq (G.lineGraph) 1 = @Fintype.card ↑G.edgeSet G.fintypeEdgeSet - indepNum (G.lineGraph) := by
  classical
  exact Dq_one_eq (G.lineGraph)

/-! ### Evaluating `α` on finite instances -/

instance instDecidablePredFeasible (H : SimpleGraph V) [DecidableRel H.Adj] :
    DecidablePred (Feasible H) := fun S => by unfold Feasible; infer_instance

theorem indepNum_eq_of (H : SimpleGraph V) {n : ℕ}
    (h1 : ∃ S : Finset V, Feasible H S ∧ S.card = n)
    (h2 : ∀ S ∈ (Finset.univ : Finset V).powerset, Feasible H S → S.card ≤ n) :
    indepNum H = n := by
  obtain ⟨S, hS, hc⟩ := h1
  apply le_antisymm
  · obtain ⟨T, hT, hTc⟩ := exists_feasible_card_indepNum H
    rw [← hTc]; exact h2 T (Finset.mem_powerset.mpr (Finset.subset_univ _)) hT
  · rw [← hc]; exact feasible_card_le_indepNum H S hS

instance instDecidableRelPathGraphAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-! ### Witness for the scope of Proposition 3.10

`L(P₄) ≅ P₃` and `L(C₄) ≅ C₄` (a path on 4 vertices has 3 consecutive edges; a 4-cycle's edges
form a 4-cycle). Both `P₄` and `C₄` have `Δ = 2`. Their line graphs have the same zero set of the
profile (`D_2 = 0`, both bipartite), yet `D_1(P₃) = 1 ≠ 2 = D_1(C₄)`. -/

theorem indepNum_pathGraph_three : indepNum (pathGraph 3) = 2 :=
  indepNum_eq_of _ ⟨{0, 2}, by decide, by decide⟩ (by decide)

theorem indepNum_cycleGraph_four : indepNum (cycleGraph 4) = 2 :=
  indepNum_eq_of _ ⟨{0, 2}, by decide, by decide⟩ (by decide)

theorem Dq_one_pathGraph_three : Dq (pathGraph 3) 1 = 1 := by
  rw [Dq_one_eq, indepNum_pathGraph_three]; simp

theorem Dq_one_cycleGraph_four : Dq (cycleGraph 4) 1 = 2 := by
  rw [Dq_one_eq, indepNum_cycleGraph_four]; simp

theorem Dq_two_pathGraph_three : Dq (pathGraph 3) 2 = 0 := by
  rw [Dq_eq_zero_iff_chromatic _ (by norm_num), chromaticNumber_pathGraph 3 (by norm_num)]
  norm_num

theorem Dq_two_cycleGraph_four : Dq (cycleGraph 4) 2 = 0 := by
  rw [Dq_eq_zero_iff_chromatic _ (by norm_num),
    chromaticNumber_cycleGraph_of_even 4 (by norm_num) (by decide)]
  norm_num

/-- **Scope of Proposition 3.10.** Two graphs with the same maximum degree (`P₄`, `C₄`, `Δ = 2`) whose
line graphs (`P₃`, `C₄`) share the zero set of the defect profile (`D_2 = 0`) but differ at `q = 1`
(`D_1 = 1` vs `D_1 = 2`): the threshold is determined, the positive values are not. -/
theorem profile_zero_set_not_values :
    (pathGraph 4).maxDegree = 2 ∧ (cycleGraph 4).maxDegree = 2 ∧
    Dq (pathGraph 3) 2 = 0 ∧ Dq (cycleGraph 4) 2 = 0 ∧
    Dq (pathGraph 3) 1 = 1 ∧ Dq (cycleGraph 4) 1 = 2 :=
  ⟨by decide, by decide, Dq_two_pathGraph_three, Dq_two_cycleGraph_four,
    Dq_one_pathGraph_three, Dq_one_cycleGraph_four⟩

end PaperV
