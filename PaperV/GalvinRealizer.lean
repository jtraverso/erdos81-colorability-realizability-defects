/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Galvin/Kőnig adapters for the host model (wave 2b: `Galvin → HostAssignment`,
`Galvin/Kőnig + weighted transfer → WeightedHostSelection`).

Bipartite host instance of `HostRealizer.lean`: bases are the pairs `(u, r) : U × R`, the request
graph is a simple bipartite edge set `B : Finset (U × R)` encoded as the multiplicity
`X e = if e ∈ B then 1 else 0`; endpoints `ends (u, r) = {inl u, inr r}`; host lists `L e ⊆ H`.

  Mode 1 (complete all bases).  `galvin_host_assignment`: degrees ≤ Δ and `|L e| ≥ Δ` on `B` give a
    proper list HOST assignment of every base of `B` (`Host.ProperOn`), hence (`galvin_full_packing`)
    all triangles of `B` pack physically and `|B| ≤ ν(hostCS)`. This is `Galvin → HostAssignment`.
  Mode 2 (select a heavy class).  `weighted_host_selection`: from ANY proper edge colouring of `B`
    with `d` colours and weights `w`, some colour class `M` (a matching) has `d·w(M) ≥ w(B)`; a matching
    with nonempty lists always packs physically (no two of its bases share an endpoint), so
    `w(B) ≤ d · ν_w(hostCS)`. With Kőnig's colouring `d = Δ` (`konig_weighted_host_selection`).
    This is the transfer engine's "class of weight ≥ average" in the physical host model.
  Mode 2′ (Galvin, single host).  `galvin_heavy_single_host`: in Galvin's assignment each host class is
    a matching placed on ONE host; some host carries weight ≥ `w(B)/|H|`.

Scope note (external audit of Paper III, `EXT-V14C-N02`): the ported theorem is Galvin's
maximum-degree case for SIMPLE bipartite graphs. The Borodin–Kostochka–Woodall local refinement
`|L(uv)| ≥ max(d(u), d(v))` and the multigraph version are NOT claimed here.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Galvin
public import PaperV.HostRealizer

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace Host

variable {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H]

/-- Endpoints of the base `(u, r)`. -/
def bipEnds (e : U × R) : Finset (U ⊕ R) := {Sum.inl e.1, Sum.inr e.2}

theorem not_disjoint_bipEnds_iff (e e' : U × R) :
    ¬ Disjoint (bipEnds e) (bipEnds e') ↔ e.1 = e'.1 ∨ e.2 = e'.2 := by
  simp only [bipEnds, Finset.not_disjoint_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, ha'⟩
    rcases ha with rfl | rfl <;> rcases ha' with h | h <;> simp_all
  · rintro (h | h)
    · exact ⟨Sum.inl e.1, Or.inl rfl, Or.inl (by rw [h])⟩
    · exact ⟨Sum.inr e.2, Or.inr rfl, Or.inr (by rw [h])⟩

/-- A matching (no two bases share an endpoint) with nonempty lists is a proper list host assignment
for ANY choice of hosts from the lists. -/
theorem properOn_of_matching [Nonempty H] (L : U × R → Finset H) (M : Finset (U × R))
    (hM : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2)
    (hL : ∀ e ∈ M, (L e).Nonempty) :
    ∃ c : U × R → H, ProperOn bipEnds L M c := by
  classical
  refine ⟨fun e => if h : (L e).Nonempty then h.choose else Classical.arbitrary H, ?_, ?_⟩
  · intro e he
    have h := hL e he
    simp only [h, dite_true]
    exact h.choose_spec
  · intro e he f hf hef hnd
    exfalso
    rw [not_disjoint_bipEnds_iff] at hnd
    rcases hnd with h | h
    · exact (hM e he f hf hef).1 h
    · exact (hM e he f hf hef).2 h

/-! ### Mode 1: Galvin ⇒ proper list host assignment of all bases -/

/-- **`Galvin → HostAssignment`.** Simple bipartite request graph `B` with degrees ≤ `Δ` and host lists
of size ≥ `Δ` on `B`: there is a proper list host assignment of every base of `B`. -/
theorem galvin_host_assignment [Nonempty H] (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    ∃ c : U × R → H, ProperOn bipEnds L B c := by
  classical
  let enc : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let L' : U × R → Finset ℕ := fun e => (L e).image (fun h => (enc h : ℕ))
  have hinj : Function.Injective (fun h : H => (enc h : ℕ)) :=
    fun a b hab => enc.injective (Fin.ext hab)
  have hL' : ∀ e ∈ B, Δ ≤ (L' e).card := by
    intro e he
    rw [Finset.card_image_of_injective _ hinj]; exact hL e he
  obtain ⟨φ, hφmem, hφprop⟩ := Galvin.galvin_max_degree B Δ hdegU hdegR L' hL'
  -- decode the colour back to a host
  have hdec : ∀ e ∈ B, ∃ x ∈ L e, (enc x : ℕ) = φ e := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (hφmem e he)
    exact ⟨x, hx, hxe⟩
  refine ⟨fun e => if h : ∃ x ∈ L e, (enc x : ℕ) = φ e then h.choose else Classical.arbitrary H,
    ?_, ?_⟩
  · intro e he
    have h := hdec e he
    simp only [h, dite_true]
    exact h.choose_spec.1
  · intro e he f hf hef hnd
    have he' := hdec e he
    have hf' := hdec f hf
    simp only [he', hf', dite_true]
    intro heq
    have h1 := he'.choose_spec.2
    have h2 := hf'.choose_spec.2
    rw [not_disjoint_bipEnds_iff] at hnd
    apply hφprop e he f hf hef hnd
    rw [← h1, ← h2, heq]

/-- **Physical completion.** Under Galvin's hypotheses all triangles of `B` pack with hosts from the
lists, and `|B| ≤ ν(hostCS)`. -/
theorem galvin_full_packing [Nonempty H] (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    ∃ c : U × R → H, (∀ e ∈ B, c e ∈ L e) ∧
      UnitBoundary.ResFeasible (triRes (H := H) bipEnds) (B.image (fun e => (e, c e))) ∧
      B.card ≤ nu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) := by
  classical
  obtain ⟨c, hc⟩ := galvin_host_assignment B Δ hdegU hdegR L hL
  refine ⟨c, hc.mem, resFeasible_of_properOn hc, ?_⟩
  have hfeas : CSFeasible (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (B.image (fun e => (e, c e))) :=
    csFeasible_hostCS_of_properOn hc
  have hcard : (B.image (fun e => (e, c e))).card = B.card :=
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
  rw [← hcard]
  unfold nu
  exact Finset.le_sup (f := Finset.card) (by simp [hfeas])

/-! ### Mode 2: heavy colour class + physical realization -/

/-- Averaging over the `d` colour classes of a colouring `φ` of `B`: some class carries at least
`1/d` of the total weight. -/
theorem exists_heavy_colour_class (B : Finset (U × R)) (w : U × R → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (φ : U × R → ℕ) (hφ : ∀ e ∈ B, φ e < d) :
    ∃ i < d, ∑ e ∈ B, w e ≤ d * ∑ e ∈ B.filter (fun e => φ e = i), w e := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun i => ∑ e ∈ B.filter (fun e => φ e = i), w e) ⟨0, Finset.mem_range.mpr hd⟩
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  have hsplit : ∑ e ∈ B, w e = ∑ j ∈ Finset.range d, ∑ e ∈ B.filter (fun e => φ e = j), w e := by
    rw [← Finset.sum_biUnion]
    · congr 1; ext e
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · intro he; exact ⟨φ e, hφ e he, he, rfl⟩
      · rintro ⟨_, _, he, _⟩; exact he
    · intro a _ b _ hab
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      rintro e ⟨_, ha⟩ ⟨_, hb⟩; exact hab (ha.symm.trans hb)
  rw [hsplit]
  calc ∑ j ∈ Finset.range d, ∑ e ∈ B.filter (fun e => φ e = j), w e
      ≤ ∑ _j ∈ Finset.range d, ∑ e ∈ B.filter (fun e => φ e = i), w e :=
        Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = d * ∑ e ∈ B.filter (fun e => φ e = i), w e := by simp

/-- **Weighted host selection.** From a proper edge colouring of `B` with `d` colours and weights `w`:
some colour class `M ⊆ B` is a matching with `d·w(M) ≥ w(B)`, and (lists nonempty on `B`) it packs
physically with hosts from the lists. -/
theorem weighted_host_selection [Nonempty H] (B : Finset (U × R)) (w : U × R → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (φ : U × R → ℕ) (hφlt : ∀ e ∈ B, φ e < d)
    (hφ : ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, (L e).Nonempty) :
    ∃ M ⊆ B, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      ∑ e ∈ B, w e ≤ d * ∑ e ∈ M, w e ∧
      ∃ c : U × R → H, ProperOn bipEnds L M c := by
  classical
  obtain ⟨i, -, hi⟩ := exists_heavy_colour_class B w d hd φ hφlt
  let M := B.filter (fun e => φ e = i)
  have hMB : M ⊆ B := Finset.filter_subset _ _
  have hmatch : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
    intro e he f hf hef
    have he' := Finset.mem_filter.mp he
    have hf' := Finset.mem_filter.mp hf
    constructor
    · intro h; exact hφ e he'.1 f hf'.1 hef (Or.inl h) (he'.2.trans hf'.2.symm)
    · intro h; exact hφ e he'.1 f hf'.1 hef (Or.inr h) (he'.2.trans hf'.2.symm)
  refine ⟨M, hMB, hmatch, hi, properOn_of_matching L M hmatch (fun e he => hL e (hMB he))⟩

/-- Packing form: `w(B) ≤ d · ν_w(hostCS)` (weights of triangles = weights of bases). -/
theorem weighted_host_selection_nu [Nonempty H] (B : Finset (U × R)) (w : U × R → ℕ) (d : ℕ)
    (hd : 1 ≤ d) (φ : U × R → ℕ) (hφlt : ∀ e ∈ B, φ e < d)
    (hφ : ∀ e ∈ B, ∀ f ∈ B, e ≠ f → (e.1 = f.1 ∨ e.2 = f.2) → φ e ≠ φ f)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, (L e).Nonempty) :
    ∑ e ∈ B, w e ≤ d * wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) := by
  classical
  obtain ⟨M, -, -, hheavy, c, hc⟩ := weighted_host_selection B w d hd φ hφlt hφ L hL
  have hfeas : CSFeasible (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (M.image (fun e => (e, c e))) :=
    csFeasible_hostCS_of_properOn hc
  have hw : ∑ t ∈ M.image (fun e => (e, c e)), triWeight w t = ∑ e ∈ M, w e := by
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]; rfl
  have hle := csFeasible_wsum_le_wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) _ hfeas
  have : ∑ e ∈ M, w e ≤ wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) := by
    calc ∑ e ∈ M, w e = ∑ t ∈ M.image (fun e => (e, c e)), triWeight w t := hw.symm
      _ ≤ _ := hle
  calc ∑ e ∈ B, w e ≤ d * ∑ e ∈ M, w e := hheavy
    _ ≤ d * wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) := Nat.mul_le_mul_left d this

/-- **Kőnig + weighted transfer.** Degrees ≤ `Δ ≥ 1`, nonempty lists: `w(B) ≤ Δ · ν_w(hostCS)`, i.e. a
matching of weight ≥ `w(B)/Δ` packs physically. -/
theorem konig_weighted_host_selection [Nonempty H] (B : Finset (U × R)) (w : U × R → ℕ) (Δ : ℕ)
    (hΔ : 1 ≤ Δ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, (L e).Nonempty) :
    ∑ e ∈ B, w e ≤ Δ * wNu (hostCS (E := U × R) (V := U ⊕ R) H bipEnds) (triWeight w) := by
  obtain ⟨φ, hφlt, hφ⟩ := Galvin.konig_edge_coloring B Δ hdegU hdegR
  exact weighted_host_selection_nu B w Δ hΔ φ hφlt hφ L hL

/-! ### Mode 2′: Galvin's assignment, heavy single host -/

/-- In a proper list host assignment of `B`, each host class is a matching; some host carries weight
≥ `w(B)/|H|`, and that class packs on that single host. -/
theorem galvin_heavy_single_host [Nonempty H] (B : Finset (U × R)) (w : U × R → ℕ)
    (L : U × R → Finset H) (c : U × R → H) (hc : ProperOn bipEnds L B c) :
    ∃ h : H, ∑ e ∈ B, w e ≤ Fintype.card H * ∑ e ∈ B.filter (fun e => c e = h), w e ∧
      UnitBoundary.ResFeasible (triRes (H := H) bipEnds)
        ((B.filter (fun e => c e = h)).image (fun e => (e, c e))) := by
  classical
  obtain ⟨h, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset H)
    (fun h => ∑ e ∈ B.filter (fun e => c e = h), w e) Finset.univ_nonempty
  refine ⟨h, ?_, ?_⟩
  · have hsplit : ∑ e ∈ B, w e = ∑ h' : H, ∑ e ∈ B.filter (fun e => c e = h'), w e := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext e
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        constructor
        · intro he; exact ⟨c e, he, rfl⟩
        · rintro ⟨_, he, _⟩; exact he
      · intro a _ b _ hab
        simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
        rintro e ⟨_, ha⟩ ⟨_, hb⟩; exact hab (ha.symm.trans hb)
    rw [hsplit]
    calc ∑ h' : H, ∑ e ∈ B.filter (fun e => c e = h'), w e
        ≤ ∑ _h' : H, ∑ e ∈ B.filter (fun e => c e = h), w e :=
          Finset.sum_le_sum (fun h' _ => hmax h' (Finset.mem_univ _))
      _ = Fintype.card H * ∑ e ∈ B.filter (fun e => c e = h), w e := by simp
  · apply resFeasible_of_properOn (L := L)
    exact ⟨fun e he => hc.mem e (Finset.mem_filter.mp he).1,
      fun e he f hf hef hnd => hc.proper e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef hnd⟩

end Host
end PaperV
