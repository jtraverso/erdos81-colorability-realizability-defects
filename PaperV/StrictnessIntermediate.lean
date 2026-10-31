/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — The realizability defect can be strictly between `0` and the colourability defect.

Instance: the star `K_{1,3}` (one left vertex, three right vertices), unit weights, multiplicity `1`, `q = 1`,
TWO hosts with full lists.

  Colourability: the three bases pairwise share the centre, so a `1`-colourable class is a single base and
    `D_1^w(X) = 3 − 1 = 2`.
  Realizability (host realizers): with two hosts at most two of the three bases can be placed (every triangle uses
    the link `(host, centre)`), so `ν(hostCS) ≤ 2` and `D_{1,ℛ_host}^w(X) ≥ 3 − 2 = 1`; deleting one base and placing
    the other two on distinct hosts is an admissible certificate of cost `1`. Hence `D_{1,ℛ_host}^w(X) = 1`.

So `0 < D_{1,ℛ_host} = 1 < D_1 = 2`: the realizability framework is not only "exact realizers or nothing" — partial
realization (a deletion/loss term that is paid but smaller than the colourability price) is what the certificate
`(Z, partition, realizers)` measures. Together with `StrictnessExample.lean` (`D = 0` vs `r² − r`) this gives both
regimes.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinClass
public import PaperV.RealizerCombinators
public import PaperV.DefectOne

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace StarExample

open UnitBoundary Host

/-- Unit multiplicity on the bases of `K_{1,3}`. -/
abbrev one : Fin 1 × Fin 3 → ℕ := fun _ => 1

/-- The auxiliary conflict graph of the star. -/
abbrev starGraph := Hgraph (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) (one)

/-- With unit multiplicities the object map on copies is injective. -/
theorem objOf_injective :
    Function.Injective (objOf (C := baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) (X := one)) := by
  rintro ⟨o, j⟩ ⟨o', j'⟩ h
  have ho : o = o' := h
  subst ho
  have : j = j' := Subsingleton.elim _ _
  rw [this]

theorem card_copies_star :
    Fintype.card (Copies (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one) = 3 := by
  rw [card_copies]
  show ∑ _o : Fin 1 × Fin 3, 1 = 3
  simp

/-- All three bases share the centre: the conflict graph is complete, `α = 1`. -/
theorem indepNum_starGraph : indepNum starGraph = 1 :=
  indepNum_eq_of _ ⟨{⟨((0 : Fin 1), (0 : Fin 3)), ⟨0, Nat.one_pos⟩⟩}, by decide, by decide⟩ (by decide)

/-- **Colourability defect** `D_1 = 2`. -/
theorem wDq_star : wDq (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one one 1 = 2 :=
  (wDq_one (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one 1).trans
    (by rw [Dq_one_eq, indepNum_starGraph, card_copies_star])

/-- Two hosts: at most two triangles pack (all bases share the centre, so triangles on the same host share the
link `(host, centre)`). -/
theorem nu_hostCS_star_le : nu (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds) ≤ 2 := by
  classical
  unfold nu
  apply Finset.sup_le
  intro T hT
  have hT' : CSFeasible (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds) T :=
    (Finset.mem_filter.mp hT).2
  -- distinct feasible triangles have distinct hosts
  have hinj : Set.InjOn (fun t : (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds).O =>
      (t : (Fin 1 × Fin 3) × Fin 2).2) (↑T) := by
    intro a ha b hb hab
    by_contra hne
    apply hT' ha hb
    refine ⟨hne, ?_⟩
    rw [Finset.not_disjoint_iff]
    refine ⟨Sum.inr (a.2, Sum.inl a.1.1), ?_, ?_⟩
    · exact mem_triRes.mpr (Or.inr ⟨Sum.inl a.1.1, by simp [bipEnds], rfl⟩)
    · have h1 : a.1.1 = b.1.1 := Subsingleton.elim _ _
      refine mem_triRes.mpr (Or.inr ⟨Sum.inl b.1.1, by simp [bipEnds], ?_⟩)
      simp only [hab, h1]
  calc T.card = (T.image (fun t : (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds).O =>
        (t : (Fin 1 × Fin 3) × Fin 2).2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin 2) := Finset.card_le_univ _
    _ = 2 := Fintype.card_fin 2

/-- Full lists. -/
abbrev fullList : Fin 1 × Fin 3 → Finset (Fin 2) := fun _ => Finset.univ

/-- Hosts for the two kept bases `(0,0) ↦ 0`, `(0,1) ↦ 1`. -/
def hostOf (e : Fin 1 × Fin 3) : Fin 2 := if e.2 = 1 then 1 else 0

/-- The deleted copy: the base `(0, 2)`. -/
def Zstar : Finset (Copies (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one) :=
  {⟨((0 : Fin 1), (2 : Fin 3)), ⟨0, Nat.one_pos⟩⟩}

theorem baseSet_class : baseSet (classOf (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) Zstar
    (fun _ => (0 : Fin 1)) 0) = {((0 : Fin 1), (0 : Fin 3)), ((0 : Fin 1), (1 : Fin 3))} := by
  decide

theorem properOn_kept : ProperOn bipEnds fullList {((0 : Fin 1), (0 : Fin 3)), ((0 : Fin 1), (1 : Fin 3))} hostOf := by
  decide

/-- The single class (index in `Fin 1`) has the kept bases as base set, and `hostOf` is proper on it. -/
theorem properOn_class (i : Fin 1) : ProperOn bipEnds fullList
    ((classOf (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) Zstar (fun _ => (0 : Fin 1)) i).image
      (objOf (C := baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) (X := one))) hostOf := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have h := baseSet_class
  unfold baseSet at h
  rw [h]; exact properOn_kept

/-- The certificate: delete `(0,2)`, place the other two bases on the two hosts. -/
noncomputable def starCert :
    RealCert (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds)
      (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds) one (triWeight one) one 1 :=
  ⟨Zstar, fun _ => 0, fun i => hostRealizer bipEnds fullList one _ objOf_injective.injOn hostOf
    (properOn_class i)⟩

theorem starCert_admissible : starCert.Admissible (HostClass bipEnds fullList one one) :=
  fun i => hostRealizer_mem _ _ _ _ objOf_injective.injOn hostOf (properOn_class i)

theorem starCert_cost : starCert.cost = 1 := by
  rw [starCert.cost_of_exact (fun _ => rfl)]
  simp [starCert, Zstar, copyWeight]

/-- **Realizability defect** `D_{1,ℛ_host} = 1`: strictly between `0` and the colourability defect `2`. -/
theorem wRDq_host_star : wRDq (HostClass bipEnds fullList one one) 1 = 1 := by
  apply le_antisymm
  · have := wRDq_le_cost _ starCert starCert_admissible
    rwa [starCert_cost] at this
  · have hge := wRDq_ge (le_refl 1) (HostClass bipEnds fullList one one) ⟨starCert, starCert_admissible⟩
    have hsize : wMultSize (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one one = 3 := by
      show ∑ _o : Fin 1 × Fin 3, 1 * 1 = 3
      simp
    have hnu : wNu (hostCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) (Fin 2) bipEnds) (triWeight one) ≤ 2 := by
      rw [show triWeight (one) = (fun _ => 1 : (Fin 1 × Fin 3) × Fin 2 → ℕ) from rfl]
      exact le_of_eq_of_le (wNu_one _) nu_hostCS_star_le
    rw [hsize] at hge
    omega

/-- **Intermediate regime.** `0 < D_{1,ℛ_host}^w(X) = 1 < 2 = D_1^w(X)`. -/
theorem intermediate_defect :
    wDq (baseCS (E := Fin 1 × Fin 3) (V := Fin 1 ⊕ Fin 3) bipEnds) one one 1 = 2 ∧
    wRDq (HostClass bipEnds fullList one one) 1 = 1 :=
  ⟨wDq_star, wRDq_host_star⟩

end StarExample
end PaperV
