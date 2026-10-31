/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Bridge between the host-realizer theorems and the SEAL packing model (§8).

SEAL's feasibility predicate `SealFeasible` (per-host matching + global pair uniqueness) is exactly the
physical feasibility of host triangles in `HostRealizer.lean`. Hence every theorem-backed proper list host
assignment produces a SEAL-feasible packing:

  * `sealFeasible_of_properOn`: a proper list host assignment `c` on a set `T` of pairs (each unordered pair
    listed once) gives the SEAL-feasible packing `{(c e, e.1, e.2) : e ∈ T}` of size `|T|`.
  * `seal_galvin_regime`  : bipartite coverable-pair graph `B` (left/right vertex classes), lists of size ≥ Δ
    (or ≥ max of the endpoint degrees) ⇒ a SEAL-feasible packing covering EVERY coverable pair, i.e. `u = 0`.
  * `seal_konig_guarantee`: bipartite `B` with degrees ≤ d and nonempty lists ⇒ a SEAL-feasible packing of size
    ≥ |B|/d (Kőnig colouring + heaviest class), a provable approximation guarantee for the constructive phase.

These are the formal statements behind the "exact Galvin/BKW regime" and the "1/Δ guarantee" of SEAL v3; the
algorithm that finds the assignment is outside Lean, but its OUTPUT is checkable (`instDecidableProperOn`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinLocal
public import PaperV.SealTermination

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV
namespace SealBridge

open Host

variable {J W : Type*} [DecidableEq J] [DecidableEq W]

/-- The SEAL packing induced by a host assignment `c` on a set of (ordered) pairs `T`. -/
def sealOf (T : Finset (W × W)) (c : W × W → J) : Finset (Assign J W) :=
  T.image (fun e => ⟨c e, e.1, e.2⟩)

/-- Endpoints of a pair as a set. -/
def pairEnds (e : W × W) : Finset W := {e.1, e.2}

theorem ends_sealOf (e : W × W) (c : W × W → J) :
    (⟨c e, e.1, e.2⟩ : Assign J W).ends = pairEnds e := rfl

/-- `T` lists each unordered pair once. -/
def PairsOnce (T : Finset (W × W)) : Prop :=
  ∀ e ∈ T, ∀ e' ∈ T, pairEnds e = pairEnds e' → e = e'

/-- **Physical soundness in SEAL's terms.** A proper list host assignment on `T` (pairs sharing a vertex get
distinct hosts) yields a SEAL-feasible packing. -/
theorem sealFeasible_of_properOn (L : W × W → Finset J) (T : Finset (W × W)) (hT : PairsOnce T)
    (c : W × W → J) (hc : ProperOn pairEnds L T c) : SealFeasible (sealOf T c) := by
  constructor
  · intro x hx y hy hxy hhost
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hy
    have hee' : e ≠ e' := fun h => hxy (by rw [h])
    by_contra hne
    have hnd : ¬ Disjoint (pairEnds e) (pairEnds e') := by
      rw [Finset.not_disjoint_iff_nonempty_inter]
      exact Finset.nonempty_iff_ne_empty.mpr hne
    exact hc.proper e he e' he' hee' hnd hhost
  · intro x hx y hy hends
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hy
    have : e = e' := hT e he e' he' hends
    subst this; rfl

theorem card_sealOf (T : Finset (W × W)) (c : W × W → J) : (sealOf T c).card = T.card :=
  Finset.card_image_of_injective _ (fun a b h => by
    have h1 := congrArg Assign.a h
    have h2 := congrArg Assign.b h
    exact Prod.ext h1 h2)

/-- Every pair of `T` is covered by the induced packing. -/
theorem covered_sealOf (T : Finset (W × W)) (c : W × W → J) (e : W × W) (he : e ∈ T) :
    ∃ x ∈ sealOf T c, x.ends = pairEnds e :=
  ⟨⟨c e, e.1, e.2⟩, Finset.mem_image_of_mem _ he, rfl⟩

/-! ### Bipartite coverable-pair graphs: the Galvin/BKW exact regime and the Kőnig guarantee

Vertices are split into two classes `U ⊕ R`; a coverable pair is `(inl u, inr r)`. -/

variable {U R : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R] [Fintype J]

/-- Embed a bipartite request edge `(u, r)` as a SEAL pair on `W := U ⊕ R`. -/
def bipPair (e : U × R) : (U ⊕ R) × (U ⊕ R) := (Sum.inl e.1, Sum.inr e.2)

theorem pairEnds_bipPair (e : U × R) : pairEnds (bipPair e) = bipEnds e := rfl

theorem bipPair_injective : Function.Injective (bipPair (U := U) (R := R)) := by
  intro e e' h
  simp only [bipPair, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
  exact Prod.ext h.1 h.2

theorem pairsOnce_bipPair (B : Finset (U × R)) : PairsOnce (B.image bipPair) := by
  intro e he e' he' hends
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨f', _, rfl⟩ := Finset.mem_image.mp he'
  rw [pairEnds_bipPair, pairEnds_bipPair] at hends
  have h1 : Sum.inl f.1 ∈ bipEnds f' := by rw [← hends]; simp [bipEnds]
  have h2 : Sum.inr f.2 ∈ bipEnds f' := by rw [← hends]; simp [bipEnds]
  simp [bipEnds] at h1 h2
  rw [show f = f' from Prod.ext h1 h2]

/-- Transport a proper assignment on `B` (bipartite host model) to the SEAL pairs. -/
theorem properOn_transport (L : U × R → Finset J) (B : Finset (U × R)) (c : U × R → J)
    (hc : ProperOn bipEnds L B c) (c' : (U ⊕ R) × (U ⊕ R) → J)
    (hc' : ∀ e ∈ B, c' (bipPair e) = c e) (L' : (U ⊕ R) × (U ⊕ R) → Finset J)
    (hL' : ∀ e ∈ B, L' (bipPair e) = L e) :
    ProperOn pairEnds L' (B.image bipPair) c' := by
  constructor
  · intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    rw [hc' e he, hL' e he]; exact hc.mem e he
  · intro p hp q hq hpq hnd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
    have hef : e ≠ f := fun h => hpq (by rw [h])
    rw [pairEnds_bipPair, pairEnds_bipPair] at hnd
    rw [hc' e he, hc' f hf]
    exact hc.proper e he f hf hef hnd

/-- **Exact regime (Galvin, global lists).** Bipartite coverable pairs `B` with degrees ≤ Δ and host lists of
size ≥ Δ: there is a SEAL-feasible packing covering every coverable pair (`u = 0`). -/
theorem seal_galvin_regime [Nonempty J] (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset J) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    ∃ Rp : Finset (Assign J (U ⊕ R)), SealFeasible Rp ∧ Rp.card = B.card ∧
      ∀ e ∈ B, ∃ x ∈ Rp, x.ends = bipEnds e := by
  classical
  obtain ⟨c, hc⟩ := galvin_host_assignment B Δ hdegU hdegR L hL
  -- lift `c` and `L` along the (injective) embedding of pairs
  let c' : (U ⊕ R) × (U ⊕ R) → J := fun p =>
    if h : ∃ e ∈ B, bipPair e = p then c h.choose else Classical.arbitrary J
  let L' : (U ⊕ R) × (U ⊕ R) → Finset J := fun p =>
    if h : ∃ e ∈ B, bipPair e = p then L h.choose else ∅
  have hkey : ∀ e ∈ B, (∃ f ∈ B, bipPair f = bipPair e) ∧
      ∀ (h : ∃ f ∈ B, bipPair f = bipPair e), h.choose = e := by
    intro e he
    refine ⟨⟨e, he, rfl⟩, fun h => bipPair_injective h.choose_spec.2⟩
  have hc' : ∀ e ∈ B, c' (bipPair e) = c e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [c', dif_pos hex, hch hex]
  have hL' : ∀ e ∈ B, L' (bipPair e) = L e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [L', dif_pos hex, hch hex]
  have hprop := properOn_transport L B c hc c' hc' L' hL'
  refine ⟨sealOf (B.image bipPair) c', sealFeasible_of_properOn L' _ (pairsOnce_bipPair B) c' hprop, ?_, ?_⟩
  · rw [card_sealOf, Finset.card_image_of_injective _ bipPair_injective]
  · intro e he
    obtain ⟨x, hx, hxe⟩ := covered_sealOf (B.image bipPair) c' (bipPair e) (Finset.mem_image_of_mem _ he)
    exact ⟨x, hx, by rw [hxe, pairEnds_bipPair]⟩

/-- **Exact regime (BKW, local lists).** Per-edge lists of size ≥ max(d(u), d(r)) suffice. -/
theorem seal_bkw_regime [Nonempty J] (B : Finset (U × R))
    (L : U × R → Finset J) (hL : ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card) :
    ∃ Rp : Finset (Assign J (U ⊕ R)), SealFeasible Rp ∧ Rp.card = B.card ∧
      ∀ e ∈ B, ∃ x ∈ Rp, x.ends = bipEnds e := by
  classical
  obtain ⟨c, hc⟩ := bkw_host_assignment B L hL
  let c' : (U ⊕ R) × (U ⊕ R) → J := fun p =>
    if h : ∃ e ∈ B, bipPair e = p then c h.choose else Classical.arbitrary J
  let L' : (U ⊕ R) × (U ⊕ R) → Finset J := fun p =>
    if h : ∃ e ∈ B, bipPair e = p then L h.choose else ∅
  have hkey : ∀ e ∈ B, (∃ f ∈ B, bipPair f = bipPair e) ∧
      ∀ (h : ∃ f ∈ B, bipPair f = bipPair e), h.choose = e := by
    intro e he
    refine ⟨⟨e, he, rfl⟩, fun h => bipPair_injective h.choose_spec.2⟩
  have hc' : ∀ e ∈ B, c' (bipPair e) = c e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [c', dif_pos hex, hch hex]
  have hL' : ∀ e ∈ B, L' (bipPair e) = L e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [L', dif_pos hex, hch hex]
  have hprop := properOn_transport L B c hc c' hc' L' hL'
  refine ⟨sealOf (B.image bipPair) c', sealFeasible_of_properOn L' _ (pairsOnce_bipPair B) c' hprop, ?_, ?_⟩
  · rw [card_sealOf, Finset.card_image_of_injective _ bipPair_injective]
  · intro e he
    obtain ⟨x, hx, hxe⟩ := covered_sealOf (B.image bipPair) c' (bipPair e) (Finset.mem_image_of_mem _ he)
    exact ⟨x, hx, by rw [hxe, pairEnds_bipPair]⟩

/-- **Kőnig guarantee.** Bipartite coverable pairs with degrees ≤ d (d ≥ 1) and nonempty lists: some SEAL-feasible
packing has size ≥ |B|/d, i.e. `|B| ≤ d · |Rp|`. -/
theorem seal_konig_guarantee [Nonempty J] (B : Finset (U × R)) (d : ℕ) (hd : 1 ≤ d)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ d)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ d)
    (L : U × R → Finset J) (hL : ∀ e ∈ B, (L e).Nonempty) :
    ∃ Rp : Finset (Assign J (U ⊕ R)), SealFeasible Rp ∧ B.card ≤ d * Rp.card := by
  classical
  obtain ⟨φ, hφlt, hφ⟩ := Galvin.konig_edge_coloring B d hdegU hdegR
  obtain ⟨M, hMB, -, hheavy, c, hc⟩ :=
    weighted_host_selection B (fun _ => 1) d hd φ hφlt hφ L hL
  let c' : (U ⊕ R) × (U ⊕ R) → J := fun p =>
    if h : ∃ e ∈ M, bipPair e = p then c h.choose else Classical.arbitrary J
  let L' : (U ⊕ R) × (U ⊕ R) → Finset J := fun p =>
    if h : ∃ e ∈ M, bipPair e = p then L h.choose else ∅
  have hkey : ∀ e ∈ M, (∃ f ∈ M, bipPair f = bipPair e) ∧
      ∀ (h : ∃ f ∈ M, bipPair f = bipPair e), h.choose = e := by
    intro e he
    refine ⟨⟨e, he, rfl⟩, fun h => bipPair_injective h.choose_spec.2⟩
  have hc' : ∀ e ∈ M, c' (bipPair e) = c e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [c', dif_pos hex, hch hex]
  have hL' : ∀ e ∈ M, L' (bipPair e) = L e := by
    intro e he
    obtain ⟨hex, hch⟩ := hkey e he
    simp only [L', dif_pos hex, hch hex]
  have hprop := properOn_transport L M c hc c' hc' L' hL'
  refine ⟨sealOf (M.image bipPair) c', sealFeasible_of_properOn L' _ (pairsOnce_bipPair M) c' hprop, ?_⟩
  rw [card_sealOf, Finset.card_image_of_injective _ bipPair_injective]
  simpa using hheavy

end SealBridge
end PaperV
