/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Galvin realizers inside the realizability framework and the Galvin-Lifted Transfer (GLT).

`GalvinRealizer.lean` produces proper list host assignments from Galvin's theorem. Here they are packaged as
class realizers of `HostRealizer.lean`, giving:

  galvinRealizer  : a class of copies with pairwise distinct bases whose base set satisfies Galvin's
                    hypotheses (degrees ≤ Δ, lists ≥ Δ) is realized EXACTLY (loss 0) by triangles on hosts
                    from the lists; it is admissible for `HostClass`.
  GLT             : if every class of a `q`-partition of the copies outside `Z` satisfies Galvin's hypotheses,
                    `|X|_w ≤ q · ν_w(hostCS) + w(Z)`.
  defect bound    : `D_{q, ℛ_host}^w(X) ≤ w(Z)` for any such certificate.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinRealizer

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace Host

variable {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H]

/-- Base set of a class of copies. -/
def baseSet {X : U × R → ℕ} (S : Finset (Copies (baseCS bipEnds) X)) : Finset (U × R) :=
  S.image (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))

/-- Galvin's hypotheses on a base set `B`: degrees ≤ Δ and lists ≥ Δ on `B`. -/
structure GalvinHyp (L : U × R → Finset H) (B : Finset (U × R)) (Δ : ℕ) : Prop where
  degU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ
  degR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ
  lists : ∀ e ∈ B, Δ ≤ (L e).card

/-- **Galvin realizer.** A class with pairwise distinct bases satisfying Galvin's hypotheses is realized exactly. -/
noncomputable def galvinRealizer [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ}
    (S : Finset (Copies (baseCS bipEnds) X))
    (hinj : Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X)) S)
    {Δ : ℕ} (hG : GalvinHyp L (baseSet S) Δ) :
    ClassRealizer (baseCS bipEnds) (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) w (triWeight w) S :=
  hostRealizer bipEnds L w S hinj
    (galvin_host_assignment (baseSet S) Δ hG.degU hG.degR L hG.lists).choose
    (galvin_host_assignment (baseSet S) Δ hG.degU hG.degR L hG.lists).choose_spec

theorem galvinRealizer_loss [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ}
    (S : Finset (Copies (baseCS bipEnds) X))
    (hinj : Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X)) S)
    {Δ : ℕ} (hG : GalvinHyp L (baseSet S) Δ) : (galvinRealizer L w S hinj hG).loss = 0 := rfl

theorem galvinRealizer_mem [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ}
    (S : Finset (Copies (baseCS bipEnds) X))
    (hinj : Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X)) S)
    {Δ : ℕ} (hG : GalvinHyp L (baseSet S) Δ) :
    HostClass bipEnds L w X S (galvinRealizer L w S hinj hG) :=
  hostRealizer_mem _ _ _ _ _ _ _

/-- **Galvin certificate**: a deletion set `Z` and a `q`-partition whose classes have distinct bases and satisfy
Galvin's hypotheses. -/
noncomputable def galvinCert [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ} {q : ℕ}
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (Δ : Fin q → ℕ) (hG : ∀ i, GalvinHyp L (baseSet (classOf (baseCS bipEnds) Z part i)) (Δ i)) :
    RealCert (baseCS bipEnds) (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) w (triWeight w) X q :=
  ⟨Z, part, fun i => galvinRealizer L w _ (hinj i) (hG i)⟩

theorem galvinCert_admissible [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ} {q : ℕ}
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (Δ : Fin q → ℕ) (hG : ∀ i, GalvinHyp L (baseSet (classOf (baseCS bipEnds) Z part i)) (Δ i)) :
    (galvinCert L w Z part hinj Δ hG).Admissible (HostClass bipEnds L w X) :=
  fun i => galvinRealizer_mem L w _ (hinj i) (hG i)

theorem galvinCert_cost [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ} {q : ℕ}
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (Δ : Fin q → ℕ) (hG : ∀ i, GalvinHyp L (baseSet (classOf (baseCS bipEnds) Z part i)) (Δ i)) :
    (galvinCert L w Z part hinj Δ hG).cost = ∑ c ∈ Z, copyWeight (baseCS bipEnds) w c :=
  (galvinCert L w Z part hinj Δ hG).cost_of_exact (fun _ => rfl)

/-- **Galvin-Lifted Transfer (GLT).** If every class of a `q`-partition of the copies outside `Z` has pairwise
distinct bases and satisfies Galvin's hypotheses, then `|X|_w ≤ q · ν_w(hostCS) + w(Z)`. -/
theorem galvin_lifted_transfer [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ} {q : ℕ}
    (hq : 1 ≤ q)
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (Δ : Fin q → ℕ) (hG : ∀ i, GalvinHyp L (baseSet (classOf (baseCS bipEnds) Z part i)) (Δ i)) :
    wMultSize (baseCS bipEnds) w X ≤
      q * wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) +
        ∑ c ∈ Z, copyWeight (baseCS bipEnds) w c :=
  realizable_transfer_exact hq (galvinCert L w Z part hinj Δ hG) (fun _ => rfl)

/-- **Realizability defect under Galvin certificates:** `D_{q,ℛ_host}^w(X) ≤ w(Z)`. -/
theorem wRDq_host_le_of_galvin [Nonempty H] (L : U × R → Finset H) (w : U × R → ℕ) {X : U × R → ℕ} {q : ℕ}
    (Z : Finset (Copies (baseCS bipEnds) X)) (part : Copies (baseCS bipEnds) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS (E := U × R) (V := U ⊕ R) bipEnds) (X := X))
      (classOf (baseCS bipEnds) Z part i))
    (Δ : Fin q → ℕ) (hG : ∀ i, GalvinHyp L (baseSet (classOf (baseCS bipEnds) Z part i)) (Δ i)) :
    wRDq (HostClass bipEnds L w X) q ≤ ∑ c ∈ Z, copyWeight (baseCS bipEnds) w c := by
  have := wRDq_le_cost _ (galvinCert L w Z part hinj Δ hG) (galvinCert_admissible L w Z part hinj Δ hG)
  rwa [galvinCert_cost] at this

end Host
end PaperV
