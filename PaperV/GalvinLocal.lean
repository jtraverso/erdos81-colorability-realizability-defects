/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Local-list host assignment (Borodin–Kostochka–Woodall) for the bipartite host model.

`GalvinMultigraph.lean` (returned by Aristotle, re-gated here) proves `galvin_bkw_local`: in a bipartite multigraph,
lists of size ≥ max(d(u), d(v)) per edge admit a proper list edge colouring. This adapter transports it to the host
model of `HostRealizer.lean` on the simple request graph `B : Finset (U × R)` (the subtype `{e // e ∈ B}` is the edge
type), yielding a proper list HOST assignment under the LOCAL condition

  `|L(e)| ≥ max(d_B(e.1), d_B(e.2))`   for every `e ∈ B`,

which is what the K₃ channel of Paper VI needs (no global palette, per-edge lists). Consequences: physical packing
of all bases of `B` and `|B| ≤ ν(hostCS)`; and the GLT with local lists (`galvin_local_lifted_transfer`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinMultigraph
public import PaperV.GalvinClass

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace Host

variable {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H]

/-- Degree of `u` in the request graph `B`. -/
def degB₁ (B : Finset (U × R)) (u : U) : ℕ := (B.filter fun e => e.1 = u).card

/-- Degree of `r` in the request graph `B`. -/
def degB₂ (B : Finset (U × R)) (r : R) : ℕ := (B.filter fun e => e.2 = r).card

/-- **BKW → HostAssignment.** Per-edge lists of size ≥ max(d(u), d(r)) on `B` give a proper list host assignment
of every base of `B`. -/
theorem bkw_host_assignment [Nonempty H] (B : Finset (U × R)) (L : U × R → Finset H)
    (hL : ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card) :
    ∃ c : U × R → H, ProperOn bipEnds L B c := by
  classical
  -- edge type: the elements of `B`
  let E := {e : U × R // e ∈ B}
  let left : E → U := fun e => e.1.1
  let right : E → R := fun e => e.1.2
  let enc : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  have hinj : Function.Injective (fun h : H => (enc h : ℕ)) :=
    fun a b hab => enc.injective (Fin.ext hab)
  let L' : E → Finset ℕ := fun e => (L e.1).image (fun h => (enc h : ℕ))
  -- degrees in the subtype encoding agree with the degrees in `B`
  have hdegL : ∀ e : E, Galvin.degL left (left e) = degB₁ B e.1.1 := by
    intro e
    unfold Galvin.degL degB₁
    have h : (Finset.univ.filter fun f : E => left f = left e) =
        (B.filter fun f => f.1 = e.1.1).subtype (fun f => f ∈ B) := by
      ext f; rw [Finset.mem_subtype, Finset.mem_filter]; simp [left, f.2]
    rw [h, Finset.card_subtype, Finset.filter_true_of_mem (fun f hf => (Finset.mem_filter.mp hf).1)]
  have hdegR : ∀ e : E, Galvin.degR right (right e) = degB₂ B e.1.2 := by
    intro e
    unfold Galvin.degR degB₂
    have h : (Finset.univ.filter fun f : E => right f = right e) =
        (B.filter fun f => f.2 = e.1.2).subtype (fun f => f ∈ B) := by
      ext f; rw [Finset.mem_subtype, Finset.mem_filter]; simp [right, f.2]
    rw [h, Finset.card_subtype, Finset.filter_true_of_mem (fun f hf => (Finset.mem_filter.mp hf).1)]
  have hL' : ∀ e : E, max (Galvin.degL left (left e)) (Galvin.degR right (right e)) ≤ (L' e).card := by
    intro e
    rw [hdegL, hdegR]
    show _ ≤ ((L e.1).image (fun h => (enc h : ℕ))).card
    rw [Finset.card_image_of_injective _ hinj]
    exact hL e.1 e.2
  obtain ⟨φ, hφmem, hφprop⟩ := Galvin.galvin_bkw_local left right L' hL'
  have hdec : ∀ e : E, ∃ x ∈ L e.1, (enc x : ℕ) = φ e := by
    intro e
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (hφmem e)
    exact ⟨x, hx, hxe⟩
  refine ⟨fun e => if h : e ∈ B then (hdec ⟨e, h⟩).choose else Classical.arbitrary H, ?_, ?_⟩
  · intro e he
    simp only [he, dite_true]
    exact (hdec ⟨e, he⟩).choose_spec.1
  · intro e he f hf hef hnd
    simp only [he, hf, dite_true]
    intro heq
    have h1 := (hdec ⟨e, he⟩).choose_spec.2
    have h2 := (hdec ⟨f, hf⟩).choose_spec.2
    rw [not_disjoint_bipEnds_iff] at hnd
    have hne : (⟨e, he⟩ : E) ≠ ⟨f, hf⟩ := fun h => hef (congrArg Subtype.val h)
    apply hφprop ⟨e, he⟩ ⟨f, hf⟩ hne hnd
    rw [← h1, ← h2, heq]

/-- **Physical completion under local lists.** -/
theorem bkw_full_packing [Nonempty H] (B : Finset (U × R)) (L : U × R → Finset H)
    (hL : ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card) :
    ∃ c : U × R → H, (∀ e ∈ B, c e ∈ L e) ∧
      UnitBoundary.ResFeasible (triRes (H := H) bipEnds) (B.image (fun e => (e, c e))) ∧
      B.card ≤ nu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) := by
  classical
  obtain ⟨c, hc⟩ := bkw_host_assignment B L hL
  refine ⟨c, hc.mem, resFeasible_of_properOn hc, ?_⟩
  have hfeas : CSFeasible (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (B.image (fun e => (e, c e))) :=
    csFeasible_hostCS_of_properOn hc
  have hcard : (B.image (fun e => (e, c e))).card = B.card :=
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
  rw [← hcard]
  unfold nu
  exact Finset.le_sup (f := Finset.card) (by simp [hfeas])

/-- Local Galvin hypotheses on a base set: per-edge lists ≥ max of the endpoint degrees in that set. -/
def LocalListHyp (L : U × R → Finset H) (B : Finset (U × R)) : Prop :=
  ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card

/-- **GLT with local lists.** If every class of a `q`-partition of the copies outside `Z` has pairwise distinct
bases and satisfies the local list condition, then `|X|_w ≤ q · ν_w(hostCS) + w(Z)`. -/
theorem galvin_local_lifted_transfer [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ}
    {q : ℕ} (hq : 1 ≤ q)
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (hG : ∀ i, LocalListHyp L (baseSet (classOf (baseCS bipEnds) Z part i))) :
    wMultSize (baseCS bipEnds) w X ≤
      q * wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) +
        ∑ c ∈ Z, copyWeight (baseCS bipEnds) w c := by
  classical
  have hc : ∀ i, ∃ c : U × R → H, ProperOn bipEnds L (baseSet (classOf (baseCS bipEnds) Z part i)) c :=
    fun i => bkw_host_assignment _ L (hG i)
  exact host_transfer bipEnds L w hq Z part hinj (fun i => (hc i).choose) (fun i => (hc i).choose_spec)

end Host
end PaperV
