/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Realizability defect `D_{q,ℛ}^w` and the Realizability-Defect Transfer (RDT).

Given an admissibility predicate `ℛ` on class realizers, the realizability defect is the minimum
cost `w(Z) + Σ_i r_i` over certificates whose realizers are all `ℛ`-admissible:

  RDT  : `|X|_w ≤ q · ν_{w_P}(P) + D_{q,ℛ}^w`   (whenever an admissible certificate exists),
  mono : `ℛ ⊆ ℛ'  ⇒  D_{q,ℛ'}^w ≤ D_{q,ℛ}^w`,
  identity : with `P = C` and `ℛ` = "identity realizer on an independent class" (weight-preserving,
             loss `0`), `D_{q,ℛ}^w = D_q^w(H[X])` exactly, so RDT is literally `transfer_q_weighted`;
             any `ℛ` containing the identity realizers has `D_{q,ℛ}^w ≤ D_q^w`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Realizer

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {C P : ConflictSystem}

/-- An admissibility class `ℛ` of realizers. -/
abbrev RealizerClass (C P : ConflictSystem) (w : C.O → ℕ) (wP : P.O → ℕ) (X : C.O → ℕ) :=
  ∀ S : Finset (Copies C X), ClassRealizer C P w wP S → Prop

/-- A certificate is `ℛ`-admissible if every class realizer is. -/
def RealCert.Admissible {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (R : RealizerClass C P w wP X) (cert : RealCert C P w wP X q) : Prop :=
  ∀ i, R _ (cert.real i)

/-- **Realizability defect** `D_{q,ℛ}^w(X)`: minimum certificate cost over `ℛ`-admissible
certificates. -/
noncomputable def wRDq {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    (R : RealizerClass C P w wP X) (q : ℕ) : ℕ :=
  sInf { n | ∃ cert : RealCert C P w wP X q, cert.Admissible R ∧ cert.cost = n }

/-- Any admissible certificate bounds the realizability defect from above. -/
theorem wRDq_le_cost {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (R : RealizerClass C P w wP X) (cert : RealCert C P w wP X q) (h : cert.Admissible R) :
    wRDq R q ≤ cert.cost :=
  Nat.sInf_le ⟨cert, h, rfl⟩

/-- **RDT.** `|X|_w ≤ q · ν_{w_P}(P) + D_{q,ℛ}^w(X)` whenever some admissible certificate exists. -/
theorem realizability_defect_transfer {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (R : RealizerClass C P w wP X)
    (hne : ∃ cert : RealCert C P w wP X q, cert.Admissible R) :
    wMultSize C w X ≤ q * wNu P wP + wRDq R q := by
  obtain ⟨cert₀, h₀⟩ := hne
  have hmem := Nat.sInf_mem (s := { n | ∃ cert : RealCert C P w wP X q,
    cert.Admissible R ∧ cert.cost = n }) ⟨_, cert₀, h₀, rfl⟩
  obtain ⟨cert, _, hcost⟩ := hmem
  have := realizable_transfer_cert hq cert
  unfold wRDq
  omega

/-- **Monotonicity in `ℛ`.** Enlarging the admissible class can only lower the defect. -/
theorem wRDq_mono {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    {R R' : RealizerClass C P w wP X} (hRR' : ∀ S r, R S r → R' S r)
    (hne : ∃ cert : RealCert C P w wP X q, cert.Admissible R) :
    wRDq R' q ≤ wRDq R q := by
  obtain ⟨cert₀, h₀⟩ := hne
  have hmem := Nat.sInf_mem (s := { n | ∃ cert : RealCert C P w wP X q,
    cert.Admissible R ∧ cert.cost = n }) ⟨_, cert₀, h₀, rfl⟩
  obtain ⟨cert, hadm, hcost⟩ := hmem
  have h' : cert.Admissible R' := fun i => hRR' _ _ (hadm i)
  have := wRDq_le_cost R' cert h'
  unfold wRDq at this ⊢
  omega

/-! ### The identity realizer (`P = C`) -/

variable (C)

/-- The independent-class step of `wIndep_le_wNu`: on an independent class the object map is
injective and weights are preserved. -/
theorem sum_copyWeight_image_objOf {w : C.O → ℕ} {X : C.O → ℕ} (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) :
    ∑ o ∈ S.image (objOf (C := C) (X := X)), w o = ∑ c ∈ S, copyWeight C w c := by
  have hinj : Set.InjOn (objOf (C := C) (X := X)) S := by
    intro a ha b hb hab
    by_contra hne
    exact hS ha hb ⟨hne, Or.inl hab⟩
  rw [Finset.sum_image hinj]; rfl

theorem csFeasible_image_objOf {X : C.O → ℕ} (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) : CSFeasible C (S.image (objOf (C := C) (X := X))) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by
    intro heq; subst b; exact C.Kirrefl a.1 hxy
  exact hS ha hb ⟨hab, Or.inr hxy⟩

/-- **Identity realizer**: an independent class of `H[X]` is realized by its own objects, loss `0`. -/
def identityRealizer (w : C.O → ℕ) {X : C.O → ℕ} (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) : ClassRealizer C C w w S where
  out := S.image (objOf (C := C) (X := X))
  feasible := csFeasible_image_objOf C S hS
  loss := 0
  bound := by rw [sum_copyWeight_image_objOf C S hS]; exact Nat.le_add_right _ _

/-- The identity admissibility class: independent class, realized by its own objects, loss `0`. -/
def IdentityClass (w : C.O → ℕ) (X : C.O → ℕ) : RealizerClass C C w w X :=
  fun S r => Feasible (Hgraph C X) S ∧ r.out = S.image (objOf (C := C) (X := X)) ∧ r.loss = 0

theorem identityRealizer_mem (w : C.O → ℕ) {X : C.O → ℕ} (S : Finset (Copies C X))
    (hS : Feasible (Hgraph C X) S) : IdentityClass C w X S (identityRealizer C w S hS) :=
  ⟨hS, rfl, rfl⟩

/-- `ℛ` contains the identity realizers. -/
def ContainsIdentity (w : C.O → ℕ) (X : C.O → ℕ) (R : RealizerClass C C w w X) : Prop :=
  ∀ S (hS : Feasible (Hgraph C X) S), R S (identityRealizer C w S hS)

theorem identityClass_containsIdentity (w : C.O → ℕ) (X : C.O → ℕ) :
    ContainsIdentity C w X (IdentityClass C w X) :=
  fun S hS => identityRealizer_mem C w S hS

variable {C}

/-- From a colourability certificate `(Z, q-colouring of H[X] − Z)` build an identity certificate of
cost `w(Z)`. -/
theorem exists_identity_cert {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (Z : Finset (Copies C X)) (hZ : IsDefectSet (Hgraph C X) q Z)
    (R : RealizerClass C C w w X) (hR : ContainsIdentity C w X R) :
    ∃ cert : RealCert C C w w X q, cert.Admissible R ∧ cert.Z = Z ∧
      cert.cost = ∑ c ∈ Z, copyWeight C w c := by
  classical
  let col := hZ.some
  let part : Copies C X → Fin q := fun c =>
    if h : c ∈ Z then ⟨0, hq⟩ else col ⟨c, by simpa using h⟩
  have hfeas : ∀ i, Feasible (Hgraph C X) (classOf C Z part i) := by
    intro i a ha b hb hab
    rw [mem_classOf] at ha hb
    obtain ⟨haZ, hai⟩ := ha
    obtain ⟨hbZ, hbi⟩ := hb
    have ha' : part a = col ⟨a, by simpa using haZ⟩ := by simp [part, haZ]
    have hb' : part b = col ⟨b, by simpa using hbZ⟩ := by simp [part, hbZ]
    have hadj : (Hgraph C X).induce ((Z : Set (Copies C X))ᶜ) |>.Adj
        ⟨a, by simpa using haZ⟩ ⟨b, by simpa using hbZ⟩ := SimpleGraph.induce_adj.mpr hab
    exact col.valid hadj (by rw [← ha', ← hb', hai, hbi])
  refine ⟨⟨Z, part, fun i => identityRealizer C w _ (hfeas i)⟩, fun i => hR _ (hfeas i), rfl, ?_⟩
  simp [RealCert.cost, identityRealizer]

/-- **`D_{q,ℛ}^w ≤ D_q^w`** whenever `ℛ` contains the identity realizers. -/
theorem wRDq_le_wDq {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (R : RealizerClass C C w w X) (hR : ContainsIdentity C w X R) :
    wRDq R q ≤ wDq C w X q := by
  have hmem := Nat.sInf_mem (wDq_values_nonempty C w X q)
  obtain ⟨Z, hZ, hZw⟩ := hmem
  obtain ⟨cert, hadm, -, hcost⟩ := exists_identity_cert hq Z hZ R hR
  have := wRDq_le_cost R cert hadm
  unfold wDq
  omega

/-- Admissible certificates exist for any `ℛ` containing the identity (delete everything). -/
theorem exists_admissible_of_containsIdentity {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (R : RealizerClass C C w w X) (hR : ContainsIdentity C w X R) :
    ∃ cert : RealCert C C w w X q, cert.Admissible R := by
  have hmem := Nat.sInf_mem (wDq_values_nonempty C w X q)
  obtain ⟨Z, hZ, -⟩ := hmem
  obtain ⟨cert, hadm, -, -⟩ := exists_identity_cert hq Z hZ R hR
  exact ⟨cert, hadm⟩

/-- An identity-admissible certificate yields a colourability certificate: `Z` is a `q`-defect set. -/
theorem isDefectSet_of_identity_cert {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C C w w X q) (hadm : cert.Admissible (IdentityClass C w X)) :
    IsDefectSet (Hgraph C X) q cert.Z := by
  classical
  unfold IsDefectSet
  refine ⟨SimpleGraph.Coloring.mk (fun v => cert.part v.1) ?_⟩
  intro a b hab heq
  have hadj : (Hgraph C X).Adj a.1 b.1 := SimpleGraph.induce_adj.mp hab
  have haZ : a.1 ∉ cert.Z := fun h => a.2 (Finset.mem_coe.mpr h)
  have hbZ : b.1 ∉ cert.Z := fun h => b.2 (Finset.mem_coe.mpr h)
  have hfeas := (hadm (cert.part a.1)).1
  exact hfeas ((mem_classOf C).mpr ⟨haZ, rfl⟩) ((mem_classOf C).mpr ⟨hbZ, heq.symm⟩) hadj

/-- **`D_q^w ≤ D_{q,ℛ_id}^w`** for the identity class. -/
theorem wDq_le_wRDq_identity {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q) :
    wDq C w X q ≤ wRDq (IdentityClass C w X) q := by
  have hne := exists_admissible_of_containsIdentity hq _ (identityClass_containsIdentity C w X)
  obtain ⟨cert₀, h₀⟩ := hne
  have hmem := Nat.sInf_mem (s := { n | ∃ cert : RealCert C C w w X q,
    cert.Admissible (IdentityClass C w X) ∧ cert.cost = n }) ⟨_, cert₀, h₀, rfl⟩
  obtain ⟨cert, hadm, hcost⟩ := hmem
  have hdef := isDefectSet_of_identity_cert cert hadm
  have hle : wDq C w X q ≤ ∑ c ∈ cert.Z, copyWeight C w c := Nat.sInf_le ⟨cert.Z, hdef, rfl⟩
  have hcost' : ∑ c ∈ cert.Z, copyWeight C w c ≤ cert.cost := by
    unfold RealCert.cost; omega
  unfold wRDq
  omega

/-- **Identity recovers the engine exactly:** `D_{q,ℛ_id}^w(X) = D_q^w(H[X])`. -/
theorem wRDq_identity_eq_wDq {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q) :
    wRDq (IdentityClass C w X) q = wDq C w X q :=
  le_antisymm (wRDq_le_wDq hq _ (identityClass_containsIdentity C w X)) (wDq_le_wRDq_identity hq)

/-- RDT for the identity class is literally `transfer_q_weighted`. -/
theorem realizability_transfer_identity {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q) :
    wMultSize C w X ≤ q * wNu C w + wRDq (IdentityClass C w X) q := by
  rw [wRDq_identity_eq_wDq hq]
  exact transfer_q_weighted C w X q hq

/-- Any `ℛ` containing the identity realizers gives a bound at least as strong as the colourability
transfer: `|X|_w ≤ q · ν_w + D_{q,ℛ}^w ≤ q · ν_w + D_q^w`. -/
theorem realizability_transfer_of_containsIdentity {w : C.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (R : RealizerClass C C w w X) (hR : ContainsIdentity C w X R) :
    wMultSize C w X ≤ q * wNu C w + wRDq R q ∧ wRDq R q ≤ wDq C w X q :=
  ⟨realizability_defect_transfer hq R (exists_admissible_of_containsIdentity hq R hR),
    wRDq_le_wDq hq R hR⟩

end PaperV
