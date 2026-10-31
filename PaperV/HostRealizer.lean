/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Host realizers: physical soundness of proper list host assignments (Part III, V-G3).

Requests are *bases* `e : E` with endpoints `ends e ⊆ V` (a base is an edge of a request graph) and a
list `L e ⊆ H` of admissible hosts. Placing base `e` on host `h` creates the physical object
(triangle) `h–u–v`, whose resources are the base itself and the two host–endpoint links `(h, x)`,
`x ∈ ends e`. Two triangles conflict iff they share a resource: same base, or same host with a common
endpoint.

  Auxiliary system (bases):  `baseCS ends`   — bases conflict iff they share an endpoint.
  Physical system (triangles): `hostCS H ends` — triangles conflict iff they share a resource.

Soundness: a *proper list host assignment* on a set of bases (`c e ∈ L e`, distinct hosts on bases
sharing an endpoint) packs all its triangles: `ResFeasible (triRes ends)`. Hence every class of
distinct bases carrying a proper assignment is realized exactly (loss `0`) — the **host realizer**.
This is independent of how the assignment is found (Galvin's theorem supplies one whenever all
lists have size ≥ Δ; an explicit assignment suffices in `StrictnessExample.lean`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.RealizabilityDefect
public import PaperV.UnitBoundaryWitnesses

import Mathlib.Tactic.Convert
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

open UnitBoundary

namespace Host

variable {E V H : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

/-- Footprint of the triangle `(e, h)`: the base `e` and the links `(h, x)` for `x ∈ ends e`. -/
def triRes (ends : E → Finset V) (t : E × H) : Finset (E ⊕ (H × V)) :=
  {Sum.inl t.1} ∪ (ends t.1).image (fun x => Sum.inr (t.2, x))

omit [Fintype E] [Fintype V] [Fintype H] in
theorem mem_triRes {ends : E → Finset V} {t : E × H} {r : E ⊕ (H × V)} :
    r ∈ triRes ends t ↔ r = Sum.inl t.1 ∨ ∃ x ∈ ends t.1, r = Sum.inr (t.2, x) := by
  simp [triRes, eq_comm]

/-- The auxiliary base system: bases conflict iff they share an endpoint. -/
abbrev baseCS (ends : E → Finset V) : ConflictSystem := resCS (α := E) (R := V) ends

variable (H) in
/-- The physical host system (hosts `H`): triangles conflict iff their footprints intersect. -/
abbrev hostCS (ends : E → Finset V) : ConflictSystem :=
  resCS (α := E × H) (R := E ⊕ (H × V)) (triRes ends)

/-- **Proper list host assignment on a set `T` of bases**: hosts from the lists, distinct hosts on
bases sharing an endpoint. -/
structure ProperOn (ends : E → Finset V) (L : E → Finset H) (T : Finset E) (c : E → H) : Prop where
  mem : ∀ e ∈ T, c e ∈ L e
  proper : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → ¬ Disjoint (ends e) (ends e') → c e ≠ c e'

omit [Fintype E] [Fintype V] [Fintype H] in
/-- Proper list host assignments are decidable on finite data (certificates are checkable). -/
instance instDecidableProperOn (ends : E → Finset V) (L : E → Finset H) (T : Finset E) (c : E → H) :
    Decidable (ProperOn ends L T c) :=
  decidable_of_iff ((∀ e ∈ T, c e ∈ L e) ∧
      ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → ¬ Disjoint (ends e) (ends e') → c e ≠ c e')
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.proper⟩⟩

omit [Fintype E] [Fintype V] [Fintype H] in
/-- **Physical soundness.** A proper assignment on `T` packs all its triangles. -/
theorem resFeasible_of_properOn {ends : E → Finset V} {L : E → Finset H} {T : Finset E} {c : E → H}
    (hc : ProperOn ends L T c) : ResFeasible (triRes ends) (T.image (fun e => (e, c e))) := by
  intro a ha b hb hab
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hb
  have hee' : e ≠ e' := fun h => hab (by rw [h])
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [mem_triRes] at hr hr'
  rcases hr with rfl | ⟨x, hx, rfl⟩
  · rcases hr' with h | ⟨x', _, h⟩
    · exact hee' (Sum.inl.inj h)
    · simp at h
  · rcases hr' with h | ⟨x', hx', h⟩
    · simp at h
    · have hh : c e = c e' := (Prod.mk.inj (Sum.inr.inj h)).1
      have hxx : x = x' := (Prod.mk.inj (Sum.inr.inj h)).2
      subst hxx
      exact hc.proper e he e' he' hee' (Finset.not_disjoint_iff.mpr ⟨x, hx, hx'⟩) hh

theorem csFeasible_hostCS_of_properOn {ends : E → Finset V} {L : E → Finset H} {T : Finset E}
    {c : E → H} (hc : ProperOn ends L T c) :
    CSFeasible (hostCS H ends) (T.image (fun e => (e, c e))) :=
  (csFeasible_resCS_iff _ _).mpr (resFeasible_of_properOn hc)

/-- Distinct feasible triangles have distinct bases (they would share the base resource). -/
theorem base_injOn_of_csFeasible {ends : E → Finset V} {T : Finset (E × H)}
    (hT : CSFeasible (hostCS H ends) T) : Set.InjOn (Prod.fst : E × H → E) (T : Set (E × H)) := by
  intro a ha b hb hab
  by_contra hne
  apply hT ha hb
  refine ⟨hne, ?_⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨Sum.inl a.1, mem_triRes.mpr (Or.inl rfl), mem_triRes.mpr (Or.inl (by rw [hab]))⟩

/-- At most `|E|` triangles can be packed: `ν(hostCS) ≤ |E|`. -/
theorem nu_hostCS_le (ends : E → Finset V) : nu (hostCS H ends) ≤ Fintype.card E := by
  classical
  unfold nu
  apply Finset.sup_le
  intro T hT
  have hT' : CSFeasible (hostCS H ends) T := (Finset.mem_filter.mp hT).2
  calc T.card = (T.image Prod.fst).card := (Finset.card_image_of_injOn (base_injOn_of_csFeasible hT')).symm
    _ ≤ Fintype.card E := Finset.card_le_univ _

/-- Weight of a triangle = weight of its base. -/
def triWeight (w : E → ℕ) (t : E × H) : ℕ := w t.1

/-- **Host realizer.** A class `S` of copies with pairwise distinct bases, together with a proper list
assignment on those bases, is realized exactly by the corresponding triangles. -/
def hostRealizer (ends : E → Finset V) (L : E → Finset H) (w : E → ℕ) {X : E → ℕ}
    (S : Finset (Copies (baseCS ends) X))
    (hinj : Set.InjOn (objOf (C := baseCS ends) (X := X)) S) (c : E → H)
    (hc : ProperOn ends L (S.image (objOf (C := baseCS ends) (X := X))) c) :
    ClassRealizer (baseCS ends) (hostCS H ends) w (triWeight w) S where
  out := (S.image (objOf (C := baseCS ends) (X := X))).image (fun e => (e, c e))
  feasible := csFeasible_hostCS_of_properOn hc
  loss := 0
  bound := by
    have h1 : ∑ t ∈ (S.image (objOf (C := baseCS ends) (X := X))).image (fun e => (e, c e)),
        triWeight w t = ∑ e ∈ S.image (objOf (C := baseCS ends) (X := X)), w e := by
      rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]; rfl
    have h2 : ∑ e ∈ S.image (objOf (C := baseCS ends) (X := X)), w e =
        ∑ c ∈ S, copyWeight (baseCS ends) w c := by
      rw [Finset.sum_image hinj]; rfl
    rw [Nat.add_zero]
    convert le_of_eq (h1.trans h2).symm using 2

/-- The admissibility class of host realizers with lists `L`. -/
def HostClass (ends : E → Finset V) (L : E → Finset H) (w : E → ℕ) (X : E → ℕ) :
    RealizerClass (baseCS ends) (hostCS H ends) w (triWeight w) X :=
  fun S r => ∃ c : E → H, ProperOn ends L (S.image (objOf (C := baseCS ends) (X := X))) c ∧
    r.out = (S.image (objOf (C := baseCS ends) (X := X))).image (fun e => (e, c e)) ∧ r.loss = 0

theorem hostRealizer_mem (ends : E → Finset V) (L : E → Finset H) (w : E → ℕ) {X : E → ℕ}
    (S : Finset (Copies (baseCS ends) X))
    (hinj : Set.InjOn (objOf (C := baseCS ends) (X := X)) S) (c : E → H)
    (hc : ProperOn ends L (S.image (objOf (C := baseCS ends) (X := X))) c) :
    HostClass ends L w X S (hostRealizer ends L w S hinj c hc) :=
  ⟨c, hc, rfl, rfl⟩

/-- **Host-lifted transfer.** If every class of a `q`-partition of the copies outside `Z` has pairwise
distinct bases and a proper list host assignment, then `|X|_w ≤ q · ν_w(hostCS) + w(Z)`. -/
theorem host_transfer (ends : E → Finset V) (L : E → Finset H) (w : E → ℕ) {X : E → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (Z : Finset (Copies (baseCS ends) X)) (part : Copies (baseCS ends) X → Fin q)
    (hinj : ∀ i, Set.InjOn (objOf (C := baseCS ends) (X := X)) (classOf (baseCS ends) Z part i))
    (c : Fin q → E → H)
    (hc : ∀ i, ProperOn ends L
      ((classOf (baseCS ends) Z part i).image (objOf (C := baseCS ends) (X := X))) (c i)) :
    wMultSize (baseCS ends) w X ≤ q * wNu (hostCS H ends) (triWeight w) +
      ∑ c ∈ Z, copyWeight (baseCS ends) w c := by
  let cert : RealCert (baseCS ends) (hostCS H ends) w (triWeight w) X q :=
    ⟨Z, part, fun i => hostRealizer ends L w _ (hinj i) (c i) (hc i)⟩
  exact realizable_transfer_exact hq cert (fun _ => rfl)

end Host
end PaperV
