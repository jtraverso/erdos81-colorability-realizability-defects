/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Strict separation between colourability and realizability defects (V-G5).

Requests: the `r²` bases `(u, v)` of the complete bipartite graph `K_{r,r}` (left endpoint `u`, right
endpoint `v`), unit weights, multiplicity `1`, `q = 1`, hosts `Fin r`, all lists full.

  Colourability defect: a `1`-colourable (independent) class of `H[X]` is a matching of `K_{r,r}`, so
    `D_1^w(X) = |X| − α(L(K_{r,r})) = r² − r`      (via `Dq_one_eq`).
  Realizability defect (host realizers): the explicit assignment `c(u, v) = u + v (mod r)` is a proper
    list host assignment of ALL bases, so the single class `X` is realized exactly:
    `D_{1,ℛ_host}^w(X) = 0`.

Same multiset, same `q`, same weights, quadratic gap. No Galvin is needed for this instance; the
assignment is explicit. Consequence: all `r²` requests are physically packable with `r` hosts:
`ν(hostCS) = r²`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.HostRealizer
public import PaperV.DefectOne

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV
namespace Strictness

open UnitBoundary Host

variable (r : ℕ)

/-- Endpoints of the base `(u, v)`: left vertex `inl u`, right vertex `inr v`. -/
def krEnds (e : Fin r × Fin r) : Finset (Fin r ⊕ Fin r) := {Sum.inl e.1, Sum.inr e.2}

/-- Bases share an endpoint iff they agree in a coordinate. -/
theorem not_disjoint_krEnds_iff (e e' : Fin r × Fin r) :
    ¬ Disjoint (krEnds r e) (krEnds r e') ↔ e.1 = e'.1 ∨ e.2 = e'.2 := by
  simp only [krEnds, Finset.not_disjoint_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, ha'⟩
    rcases ha with rfl | rfl <;> rcases ha' with h | h <;> simp_all
  · rintro (h | h)
    · exact ⟨Sum.inl e.1, Or.inl rfl, Or.inl (by rw [h])⟩
    · exact ⟨Sum.inr e.2, Or.inr rfl, Or.inr (by rw [h])⟩

/-- Unit multiplicity. -/
abbrev one : Fin r × Fin r → ℕ := fun _ => 1

/-- The auxiliary conflict graph `H[X]` of the bases (the line graph of `K_{r,r}` with unit copies). -/
abbrev krGraph := Hgraph (baseCS (krEnds r)) (one r)

/-- With unit multiplicities the object map on copies is injective. -/
theorem objOf_injective : Function.Injective (objOf (C := baseCS (krEnds r)) (X := one r)) := by
  rintro ⟨o, j⟩ ⟨o', j'⟩ h
  have ho : o = o' := h
  subst ho
  have : j = j' := Subsingleton.elim _ _
  rw [this]

theorem card_copies_kr : Fintype.card (Copies (baseCS (krEnds r)) (one r)) = r * r := by
  rw [card_copies]
  show ∑ _o : Fin r × Fin r, 1 = r * r
  simp

/-- Independent sets of `H[X]` have pairwise distinct left endpoints, hence size ≤ `r`. -/
theorem feasible_card_le (S : Finset (Copies (baseCS (krEnds r)) (one r)))
    (hS : Feasible (krGraph r) S) : S.card ≤ r := by
  have hinj : Set.InjOn (fun c : Copies (baseCS (krEnds r)) (one r) => c.1.1) S := by
    intro a ha b hb hab
    by_contra hne
    apply hS ha hb
    refine ⟨hne, ?_⟩
    by_cases hobj : a.1 = b.1
    · exact Or.inl hobj
    · right
      refine ⟨hobj, ?_⟩
      exact (not_disjoint_krEnds_iff r _ _).mpr (Or.inl hab)
  calc S.card = (S.image (fun c : Copies (baseCS (krEnds r)) (one r) => c.1.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin r) := Finset.card_le_univ _
    _ = r := Fintype.card_fin r

/-- The diagonal `{(u, u)}` is an independent set of size `r`. -/
def diag : Finset (Copies (baseCS (krEnds r)) (one r)) :=
  Finset.univ.image (fun u : Fin r => (⟨(u, u), ⟨0, Nat.one_pos⟩⟩ : Copies (baseCS (krEnds r)) (one r)))

theorem diag_feasible : Feasible (krGraph r) (diag r) := by
  intro a ha b hb hab
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hne, h⟩ := hab
  have huv : u ≠ v := fun h => hne (by rw [h])
  rcases h with h | ⟨_, h⟩
  · exact huv (Prod.mk.inj h).1
  · rw [not_disjoint_krEnds_iff] at h
    rcases h with h | h <;> exact huv h

theorem diag_card : (diag r).card = r := by
  unfold diag
  rw [Finset.card_image_of_injective _ (fun u v h => (Prod.mk.inj (Sigma.mk.inj_iff.mp h).1).1)]
  simp

theorem indepNum_krGraph : indepNum (krGraph r) = r :=
  indepNum_eq_of _ ⟨diag r, diag_feasible r, diag_card r⟩
    (fun S _ hS => feasible_card_le r S hS)

/-- **Colourability defect:** `D_1(H[X]) = r² − r`. -/
theorem Dq_one_krGraph : Dq (krGraph r) 1 = r * r - r := by
  rw [Dq_one_eq, indepNum_krGraph, card_copies_kr]

/-- Weighted form with unit weights. -/
theorem wDq_one_kr : wDq (baseCS (krEnds r)) (one r) (one r) 1 = r * r - r := by
  exact (wDq_one (baseCS (krEnds r)) (one r) 1).trans (Dq_one_krGraph r)

/-! ### The explicit host assignment `c(u, v) = u + v` -/

variable [NeZero r]

/-- Host of the base `(u, v)`: `u + v` in `Fin r`. -/
def hostOf (e : Fin r × Fin r) : Fin r := e.1 + e.2

/-- Full lists. -/
abbrev fullList : Fin r × Fin r → Finset (Fin r) := fun _ => Finset.univ

omit [NeZero r] in
/-- `c(u, v) = u + v` is a proper list host assignment of every set of bases. -/
theorem properOn_hostOf (T : Finset (Fin r × Fin r)) :
    ProperOn (krEnds r) (fullList r) T (hostOf r) where
  mem := fun _ _ => Finset.mem_univ _
  proper := by
    intro e _ e' _ hne hshare heq
    rw [not_disjoint_krEnds_iff] at hshare
    unfold hostOf at heq
    apply hne
    rcases hshare with h | h
    · rw [h] at heq
      exact Prod.ext h (add_left_cancel heq)
    · rw [h] at heq
      exact Prod.ext (add_right_cancel heq) h

/-- Checkable instance: the explicit assignment is verified by `decide` for `r = 3`. -/
example : ProperOn (krEnds 3) (fullList 3) Finset.univ (hostOf 3) := by decide

/-- The all-in-one-class certificate: `Z = ∅`, `q = 1`, host realizer with `c = hostOf`. -/
noncomputable def hostCert :
    RealCert (baseCS (krEnds r)) (hostCS (Fin r) (krEnds r)) (one r) (triWeight (one r)) (one r) 1 :=
  ⟨∅, fun _ => 0, fun _ => hostRealizer (krEnds r) (fullList r) (one r) _
    ((objOf_injective r).injOn) (hostOf r) (properOn_hostOf r _)⟩

theorem hostCert_admissible :
    (hostCert r).Admissible (HostClass (krEnds r) (fullList r) (one r) (one r)) :=
  fun _ => hostRealizer_mem _ _ _ _ ((objOf_injective r).injOn) (hostOf r) (properOn_hostOf r _)

theorem hostCert_cost : (hostCert r).cost = 0 := by
  simp [RealCert.cost, hostCert, hostRealizer]

/-- **Realizability defect with host realizers:** `D_{1,ℛ_host}(X) = 0`. -/
theorem wRDq_host_kr : wRDq (HostClass (krEnds r) (fullList r) (one r) (one r)) 1 = 0 :=
  Nat.eq_zero_of_le_zero (by
    have := wRDq_le_cost _ (hostCert r) (hostCert_admissible r)
    rwa [hostCert_cost] at this)

/-- **Strict separation.** Same multiset, `q = 1`, unit weights:
`D_1^w(X) = r² − r` while `D_{1,ℛ_host}^w(X) = 0`. -/
theorem strict_separation :
    wDq (baseCS (krEnds r)) (one r) (one r) 1 = r * r - r ∧
    wRDq (HostClass (krEnds r) (fullList r) (one r) (one r)) 1 = 0 :=
  ⟨wDq_one_kr r, wRDq_host_kr r⟩

/-- The gap is quadratic: for `r ≥ 2` the colourability defect is positive while the realizability
defect vanishes. -/
theorem strict_separation_pos (hr : 2 ≤ r) :
    0 < wDq (baseCS (krEnds r)) (one r) (one r) 1 ∧
    wRDq (HostClass (krEnds r) (fullList r) (one r) (one r)) 1 = 0 := by
  refine ⟨?_, wRDq_host_kr r⟩
  rw [wDq_one_kr]
  have : r < r * r := by nlinarith
  omega

/-- **Physical consequence:** all `r²` requests pack with `r` hosts, `ν(hostCS) = r²`. -/
theorem nu_hostCS_kr : nu (hostCS (Fin r) (krEnds r)) = r * r := by
  apply le_antisymm
  · have := nu_hostCS_le (H := Fin r) (krEnds r)
    simpa using this
  · have h := realizable_transfer_exact (le_refl 1) (hostCert r) (fun _ => rfl)
    have hZ : ∑ c ∈ (hostCert r).Z, copyWeight (baseCS (krEnds r)) (one r) c = 0 := by
      simp [hostCert]
    have hsize : wMultSize (baseCS (krEnds r)) (one r) (one r) = r * r := by
      show ∑ _o : Fin r × Fin r, 1 * 1 = r * r
      simp
    have hnu : wNu (hostCS (Fin r) (krEnds r)) (triWeight (one r)) = nu (hostCS (Fin r) (krEnds r)) := by
      have := wNu_one (hostCS (Fin r) (krEnds r))
      exact this
    rw [hZ, hsize, hnu] at h
    omega

end Strictness
end PaperV
