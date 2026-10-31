/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Exact host completion: `ν(hostCS_B) = |B|` on the restricted target system.

The physical system `hostCS H ends` of `HostRealizer.lean` ranges over the whole base universe `E`,
so its packing number is bounded by `|E|` (`nu_hostCS_le`) and a request family `B ⊆ E` only gives the
lower bound `|B| ≤ ν(hostCS)` (`galvin_full_packing`). The *equality* asked for in Corollary 5.3
holds once the target universe is restricted to the requested bases: this file defines that system

  `hostCSOn H ends B` — triangles `(e, h)` with `e ∈ B`, conflicting iff they share a resource —

and proves `ν(hostCSOn H ends B) = |B|` whenever the bases of `B` carry a proper list host assignment
(in particular under Galvin's global lists or the local Borodin–Kostochka–Woodall lists). The
unrestricted system satisfies the same equality exactly when every base is requested (`B = univ`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinRealizer
public import PaperV.GalvinLocal

@[expose] public section

open Finset

namespace PaperV

open UnitBoundary

namespace Host

/-! ### Generic transport lemmas for resource feasibility -/

theorem ResFeasible.subset {α ρ : Type*} [DecidableEq α] [DecidableEq ρ] {res : α → Finset ρ}
    {P Q : Finset α} (h : ResFeasible res P) (hQ : Q ⊆ P) : ResFeasible res Q :=
  fun _ ha _ hb hab => h (hQ ha) (hQ hb) hab

theorem resFeasible_comap {α β ρ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ρ]
    (res : β → Finset ρ) (f : α → β) (hf : Function.Injective f) {S : Finset α}
    (h : ResFeasible res (S.image f)) : ResFeasible (fun a => res (f a)) S :=
  fun _ ha _ hb hab =>
    h (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb) (fun he => hab (hf he))

section Restricted

variable {E V H : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

variable (H) in
/-- **The host system restricted to the requested bases `B`.** Objects are the triangles `(e, h)`
with `e ∈ B`; two of them conflict iff their footprints `triRes ends` meet. -/
abbrev hostCSOn (ends : E → Finset V) (B : Finset E) : ConflictSystem :=
  resCS (α := {e : E // e ∈ B} × H) (R := E ⊕ (H × V)) (fun t => triRes ends (t.1.1, t.2))

omit [Fintype E] [Fintype V] in
/-- Distinct feasible triangles of the restricted system have distinct bases. -/
theorem base_injOn_of_csFeasible_on {ends : E → Finset V} {B : Finset E}
    {T : Finset ({e : E // e ∈ B} × H)} (hT : CSFeasible (hostCSOn H ends B) T) :
    Set.InjOn (Prod.fst : {e : E // e ∈ B} × H → {e : E // e ∈ B}) (T : Set _) := by
  intro a ha b hb hab
  by_contra hne
  apply hT ha hb
  refine ⟨hne, ?_⟩
  have hval : a.1.1 = b.1.1 := congrArg Subtype.val hab
  rw [Finset.not_disjoint_iff]
  exact ⟨Sum.inl a.1.1, mem_triRes.mpr (Or.inl rfl), mem_triRes.mpr (Or.inl (by rw [hval]))⟩

omit [Fintype E] [Fintype V] in
/-- **Upper bound.** The restricted system packs at most `|B|` triangles. -/
theorem nu_hostCSOn_le (ends : E → Finset V) (B : Finset E) :
    nu (hostCSOn H ends B) ≤ B.card := by
  classical
  unfold nu
  apply Finset.sup_le
  intro T hT
  have hT' : CSFeasible (hostCSOn H ends B) T := (Finset.mem_filter.mp hT).2
  calc T.card = (T.image Prod.fst).card :=
        (Finset.card_image_of_injOn (base_injOn_of_csFeasible_on hT')).symm
    _ ≤ Fintype.card {e : E // e ∈ B} := Finset.card_le_univ _
    _ = B.card := by simp

/-- The triangles of a proper list host assignment on `B`, as objects of the restricted system. -/
def packOn (B : Finset E) (c : E → H) :
    Finset ({e : E // e ∈ B} × H) :=
  B.attach.image (fun e => (e, c e.1))

omit [Fintype E] [Fintype V] [DecidableEq V] [Fintype H] in
/-- The restricted packing of a proper assignment has exactly `|B|` triangles. -/
theorem card_packOn (B : Finset E) (c : E → H) :
    (packOn B c).card = B.card := by
  classical
  rw [packOn, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
    Finset.card_attach]

omit [Fintype E] [Fintype V] in
/-- **Soundness in the restricted system.** A proper list host assignment on `B` is a feasible
packing of `hostCSOn H ends B`. -/
theorem csFeasible_hostCSOn_of_properOn {ends : E → Finset V} {L : E → Finset H} {B : Finset E}
    {c : E → H} (hc : ProperOn ends L B c) :
    CSFeasible (hostCSOn H ends B) (packOn B c) := by
  classical
  rw [csFeasible_resCS_iff]
  have hbig : ResFeasible (triRes ends) (B.image (fun e => (e, c e))) := resFeasible_of_properOn hc
  have hsub : (packOn B c).image (fun t : {e : E // e ∈ B} × H => (t.1.1, t.2))
      ⊆ B.image (fun e => (e, c e)) := by
    intro x hx
    simp only [packOn, Finset.mem_image, Finset.mem_attach, true_and] at hx
    obtain ⟨t, ⟨e, rfl⟩, rfl⟩ := hx
    exact Finset.mem_image_of_mem _ e.2
  have hinj : Function.Injective (fun t : {e : E // e ∈ B} × H => (t.1.1, t.2)) := by
    rintro ⟨⟨a1, ha1⟩, a2⟩ ⟨⟨b1, hb1⟩, b2⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2]
  exact resFeasible_comap (α := {e : E // e ∈ B} × H) (triRes ends)
    (fun t : {e : E // e ∈ B} × H => (t.1.1, t.2)) hinj (ResFeasible.subset hbig hsub)

/-- **Lower bound.** A proper list host assignment on `B` realizes `|B|` triangles. -/
theorem le_nu_hostCSOn_of_properOn {ends : E → Finset V} {L : E → Finset H} {B : Finset E}
    {c : E → H} (hc : ProperOn ends L B c) : B.card ≤ nu (hostCSOn H ends B) := by
  classical
  rw [← card_packOn B c]
  unfold nu
  exact Finset.le_sup (f := Finset.card)
    (by simp [csFeasible_hostCSOn_of_properOn hc])

/-- **Exact host completion.** If every base of `B` carries a proper list host assignment, the
restricted host system has packing number exactly `|B|`: every request is realized and nothing
beyond the requests can be packed. -/
theorem nu_hostCSOn_eq_of_properOn {ends : E → Finset V} {L : E → Finset H} {B : Finset E}
    {c : E → H} (hc : ProperOn ends L B c) : nu (hostCSOn H ends B) = B.card :=
  le_antisymm (nu_hostCSOn_le ends B) (le_nu_hostCSOn_of_properOn hc)

/-- In the *unrestricted* system the same equality holds exactly when every base is requested. -/
theorem nu_hostCS_eq_card_of_properOn_univ {ends : E → Finset V} {L : E → Finset H} {c : E → H}
    (hc : ProperOn ends L Finset.univ c) : nu (hostCS H ends) = Fintype.card E := by
  classical
  refine le_antisymm (nu_hostCS_le ends) ?_
  have hfeas : CSFeasible (hostCS H ends) (Finset.univ.image (fun e => (e, c e))) :=
    csFeasible_hostCS_of_properOn hc
  have hcard : (Finset.univ.image (fun e : E => (e, c e))).card = Fintype.card E := by
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ]
  rw [← hcard]
  unfold nu
  exact Finset.le_sup (f := Finset.card) (by simp [hfeas])

end Restricted

/-! ### The bipartite request instance: Galvin and Borodin–Kostochka–Woodall -/

section Bipartite

variable {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H]

/-- **Corollary 5.3, exact form (Galvin).** With degrees at most `Δ` and host lists of size at least
`Δ`, the host system restricted to the requests `B` has packing number exactly `|B|`. -/
theorem galvin_host_completion_exact [Nonempty H] (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    nu (hostCSOn (E := U × R) (V := U ⊕ R) H bipEnds B) = B.card := by
  obtain ⟨c, hc⟩ := galvin_host_assignment B Δ hdegU hdegR L hL
  exact nu_hostCSOn_eq_of_properOn hc

/-- **Corollary 5.3, exact form (local BKW lists).** -/
theorem bkw_host_completion_exact [Nonempty H] (B : Finset (U × R)) (L : U × R → Finset H)
    (hL : ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card) :
    nu (hostCSOn (E := U × R) (V := U ⊕ R) H bipEnds B) = B.card := by
  obtain ⟨c, hc⟩ := bkw_host_assignment B L hL
  exact nu_hostCSOn_eq_of_properOn hc

/-- If *every* base is requested, Galvin's hypotheses give the equality in the unrestricted host
system as well. -/
theorem galvin_nu_hostCS_eq_card [Nonempty H] (Δ : ℕ)
    (hdegU : ∀ u, ((Finset.univ : Finset (U × R)).filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, ((Finset.univ : Finset (U × R)).filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e, Δ ≤ (L e).card) :
    nu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) = Fintype.card (U × R) := by
  obtain ⟨c, hc⟩ := galvin_host_assignment Finset.univ Δ hdegU hdegR L (fun e _ => hL e)
  exact nu_hostCS_eq_card_of_properOn_univ hc

end Bipartite

end Host
end PaperV
