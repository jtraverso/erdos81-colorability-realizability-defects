/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Colorability and realizability defects in resource-dominated packing relaxations

Statements of the main results of *Colorability and Realizability Defects in Resource-Dominated
Packing Relaxations* (Paper V of the Erdős #81 series, J. P. Traverso Gianini, version 1.10).

A conflict system is a finite set of objects with a symmetric irreflexive conflict relation; its
packing number `ν` is the largest size of a set of pairwise non-conflicting objects. For a
multiset `X` of objects (a multiplicity function), `H[X]` is the conflict graph on the copies of
`X`, and `D_q(H)` is the least number of vertices whose deletion makes `H` `q`-colourable
(`oct = D_2`).

* §3. `lemma_3_1`, `corollary_3_2`: splitting. `theorem_3_3`, `theorem_3_4`: transfer from a
  `1/2`- or `1/q`-integral optimum of a resource-dominated relaxation. `theorem_3_4w`: the weighted
  transfer `|X|_w ≤ q ν_w + D_q^w(H[X])`.
* §4. `theorem_4_2`, `theorem_4_2_nu`: realizable-class transfer. `theorem_4_4`: the identity
  realizer recovers the weighted colourability defect.
* §5. `theorem_5_2_galvin`, `theorem_5_2_bkw`: list edge colouring of bipartite multigraphs
  (Galvin; Borodin–Kostochka–Woodall local form). `corollary_5_3_galvin`, `corollary_5_3_bkw`:
  exact host completion. `example_5_5`: strict separation on `K_{r,r}`.
* §6. `theorem_6_1`, `theorem_6_2`, `corollary_6_2a`: fractional and integral vertex-copy
  inequalities for triangle packings, including `ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 3 ν₃(G)`.
* §7. `proposition_7_1`: the pure-profile packing number. `theorem_7_3_fractional`,
  `theorem_7_3_integral`: mixed triangle/`K₄` copy inequalities.

`edgesIn`, `IsTrianglePacking` and `IsFracTrianglePacking` are copied from the Palomar entry
PALOMAR-2026-10-15-000011 and `nu3` from PALOMAR-2026-10-29-000006 (Paper III); the other
definitions are copied from the Paper V library.
-/

@[expose] public section

open SimpleGraph Finset

namespace ErdosPaperV

/-! ### Conflict systems, conflict graphs and colourability defects (§2) -/

/-- **Definition 2.1 (conflict system).** Finite objects `O` with a symmetric, irreflexive
conflict relation `K`. -/
structure ConflictSystem where
  /-- The objects. -/
  O : Type*
  [finO : Fintype O]
  [decEqO : DecidableEq O]
  /-- The conflict relation. -/
  K : O → O → Prop
  Ksymm : Symmetric K
  Kirrefl : ∀ a, ¬ K a a
  [decK : DecidableRel K]

attribute [instance] ConflictSystem.finO ConflictSystem.decEqO ConflictSystem.decK

/-- A feasible (independent) object set: no two members conflict. -/
def CSFeasible (C : ConflictSystem) (S : Finset C.O) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ C.K a b

open Classical in
/-- The packing number `ν(C)`: the largest size of a feasible object set. -/
noncomputable def nu (C : ConflictSystem) : ℕ :=
  (univ.filter (fun S : Finset C.O => CSFeasible C S)).sup Finset.card

/-- The copies of a multiset `X : O → ℕ`. -/
abbrev Copies (C : ConflictSystem) (X : C.O → ℕ) : Type _ := Σ o : C.O, Fin (X o)

instance (C : ConflictSystem) (X : C.O → ℕ) : Fintype (Copies C X) := by
  unfold Copies; infer_instance
instance (C : ConflictSystem) (X : C.O → ℕ) : DecidableEq (Copies C X) := by
  unfold Copies; infer_instance

/-- The underlying object of a copy. -/
def objOf {C : ConflictSystem} {X : C.O → ℕ} (c : Copies C X) : C.O := c.1

/-- **Definition 2.2 (conflict graph `H[X]`).** Two distinct copies are adjacent when they are
copies of the same object or their objects conflict. -/
def Hgraph (C : ConflictSystem) (X : C.O → ℕ) : SimpleGraph (Copies C X) where
  Adj a b := a ≠ b ∧ (a.1 = b.1 ∨ C.K a.1 b.1)
  symm := by
    constructor
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (C.Ksymm h)
  loopless := by refine ⟨?_⟩; rintro a ⟨hne, _⟩; exact hne rfl

instance (C : ConflictSystem) (X : C.O → ℕ) : DecidableRel (Hgraph C X).Adj := by
  intro a b; unfold Hgraph; infer_instance

/-- The number of copies `|X| = Σ_o X o`. -/
def multSize (C : ConflictSystem) (X : C.O → ℕ) : ℕ := ∑ o : C.O, X o

/-- `X` is a `q`-multiset: every object has multiplicity at most `q`. -/
def IsQMultiset (C : ConflictSystem) (X : C.O → ℕ) (q : ℕ) : Prop := ∀ o, X o ≤ q

/-- `O` is a `q`-defect set of `H`: deleting `O` leaves a `q`-colourable graph. -/
def IsDefectSet {V : Type*} (H : SimpleGraph V) (q : ℕ) (O : Finset V) : Prop :=
  (H.induce ((O : Set V)ᶜ)).Colorable q

/-- **Definition 2.3 (colourability defect).** `D_q(H)`: the least size of a set whose deletion
makes `H` `q`-colourable. -/
noncomputable def Dq {V : Type*} (H : SimpleGraph V) (q : ℕ) : ℕ :=
  sInf { n | ∃ O : Finset V, IsDefectSet H q O ∧ O.card = n }

/-- The odd-cycle-transversal number `oct(H) = D_2(H)`. -/
noncomputable def oct {V : Type*} (H : SimpleGraph V) : ℕ := Dq H 2

/-- A set of vertices is feasible (independent) in `H` if no two of its members are adjacent. -/
def Feasible {V : Type*} (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → ¬ H.Adj a b

/-! ### Weights -/

/-- The weighted size of a multiset: `Σ_o w(o) · X(o)`. -/
def wMultSize (C : ConflictSystem) (w : C.O → ℕ) (X : C.O → ℕ) : ℕ := ∑ o : C.O, w o * X o

open Classical in
/-- The weighted packing number `ν_w(C)`: the largest total weight of a feasible object set. -/
noncomputable def wNu (C : ConflictSystem) (w : C.O → ℕ) : ℕ :=
  (univ.filter (fun S : Finset C.O => CSFeasible C S)).sup (fun S => ∑ o ∈ S, w o)

/-- The weight of a copy is the weight of its object. -/
def copyWeight (C : ConflictSystem) (w : C.O → ℕ) {X : C.O → ℕ} (c : Copies C X) : ℕ := w c.1

/-- The weighted colourability defect `D_q^w(H[X])`: the least total weight of a set of copies
whose deletion leaves `H[X]` `q`-colourable. -/
noncomputable def wDq (C : ConflictSystem) (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) : ℕ :=
  sInf { n | ∃ Z : Finset (Copies C X), IsDefectSet (Hgraph C X) q Z ∧
    ∑ c ∈ Z, copyWeight C w c = n }

/-! ### Resource-dominated relaxations (Definitions 2.4–2.5) -/

/-- A resource-dominated relaxation of `C`: a resource structure inducing the conflicts, and a
feasible region inside the resource-capacity polyhedron whose `0/1` points are exactly the
indicators of feasible object sets. -/
structure ResourceRelaxation (C : ConflictSystem) where
  /-- The resources. -/
  Resource : Type
  [finiteResource : Fintype Resource]
  [decResource : DecidableEq Resource]
  /-- The resource set of each object. -/
  resources : C.O → Finset Resource
  conflicts : ∀ a b, C.K a b ↔ a ≠ b ∧ ¬ Disjoint (resources a) (resources b)
  /-- The feasible region. -/
  feasible : Set (C.O → ℝ)
  nonneg : ∀ x ∈ feasible, ∀ o, 0 ≤ x o
  capacity : ∀ x ∈ feasible, ∀ e,
    ∑ o ∈ Finset.univ.filter (fun o => e ∈ resources o), x o ≤ 1
  integral_iff : ∀ S : Finset C.O,
    (fun o => if o ∈ S then (1 : ℝ) else 0) ∈ feasible ↔ CSFeasible C S

attribute [instance] ResourceRelaxation.finiteResource ResourceRelaxation.decResource

/-- An optimum of a relaxation: a feasible point maximizing the total value. -/
structure ResourceRelaxation.Optimum {C : ConflictSystem} (P : ResourceRelaxation C) where
  /-- The optimal point. -/
  point : C.O → ℝ
  /-- The point is feasible. -/
  feasible : point ∈ P.feasible
  /-- No feasible point has a larger total value. -/
  maximal : ∀ y ∈ P.feasible, ∑ o, y o ≤ ∑ o, point o

/-- The value `μ*` of an optimum. -/
def ResourceRelaxation.Optimum.value {C : ConflictSystem} {P : ResourceRelaxation C}
    (x : P.Optimum) : ℝ :=
  ∑ o, x.point o

/-! ### Realizers (Definitions 4.1 and 4.3) -/

/-- **Realizer of a class.** A class `S` of copies of `X` (source system `C`) is realized by a
feasible object set `out` of the target system `P` with loss `loss`:
`w(S) ≤ w_P(out) + loss`. -/
structure ClassRealizer (C P : ConflictSystem) (w : C.O → ℕ) (wP : P.O → ℕ) {X : C.O → ℕ}
    (S : Finset (Copies C X)) where
  /-- The realizing feasible set of the target system. -/
  out : Finset P.O
  feasible : CSFeasible P out
  /-- The loss. -/
  loss : ℕ
  bound : ∑ c ∈ S, copyWeight C w c ≤ ∑ o ∈ out, wP o + loss

/-- The `i`-th class of a `q`-partition `part` of the copies outside `Z`. -/
def classOf (C : ConflictSystem) {X : C.O → ℕ} (Z : Finset (Copies C X)) {q : ℕ}
    (part : Copies C X → Fin q) (i : Fin q) : Finset (Copies C X) :=
  Finset.univ.filter (fun c => c ∉ Z ∧ part c = i)

/-- **Realizability certificate.** A deletion set `Z`, a `q`-partition of the remaining copies and
a realizer of every class; the classes need not be independent in `H[X]`. -/
structure RealCert (C P : ConflictSystem) (w : C.O → ℕ) (wP : P.O → ℕ) (X : C.O → ℕ)
    (q : ℕ) where
  /-- The deletion set. -/
  Z : Finset (Copies C X)
  /-- The partition of the remaining copies. -/
  part : Copies C X → Fin q
  /-- A realizer of each class. -/
  real : ∀ i : Fin q, ClassRealizer C P w wP (classOf C Z part i)

/-- The cost of a certificate: `w(Z) + Σ_i r_i`. -/
def RealCert.cost {C P : ConflictSystem} {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C P w wP X q) : ℕ :=
  ∑ c ∈ cert.Z, copyWeight C w c + ∑ i : Fin q, (cert.real i).loss

/-- An admissibility class of realizers. -/
abbrev RealizerClass (C P : ConflictSystem) (w : C.O → ℕ) (wP : P.O → ℕ) (X : C.O → ℕ) :=
  ∀ S : Finset (Copies C X), ClassRealizer C P w wP S → Prop

/-- A certificate is `ℛ`-admissible if every class realizer is. -/
def RealCert.Admissible {C P : ConflictSystem} {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    {q : ℕ} (R : RealizerClass C P w wP X) (cert : RealCert C P w wP X q) : Prop :=
  ∀ i, R _ (cert.real i)

/-- **Definition 4.3 (realizability defect)** `D_{q,ℛ}^w(X)`: the least cost of an
`ℛ`-admissible certificate. -/
noncomputable def wRDq {C P : ConflictSystem} {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    (R : RealizerClass C P w wP X) (q : ℕ) : ℕ :=
  sInf { n | ∃ cert : RealCert C P w wP X q, cert.Admissible R ∧ cert.cost = n }

/-- The identity admissibility class: independent classes, realized by their own objects with
loss `0`. -/
def IdentityClass (C : ConflictSystem) (w : C.O → ℕ) (X : C.O → ℕ) :
    RealizerClass C C w w X :=
  fun S r => Feasible (Hgraph C X) S ∧ r.out = S.image (objOf (C := C) (X := X)) ∧ r.loss = 0

/-! ### Host systems (§5) -/

/-- The conflict system induced by resource sets: distinct objects conflict iff their resource
sets meet. -/
abbrev resCS {α R : Type*} [Fintype α] [DecidableEq α] [DecidableEq R] (res : α → Finset R) :
    ConflictSystem where
  O := α
  K a b := a ≠ b ∧ ¬ Disjoint (res a) (res b)
  Ksymm := by
    rintro a b ⟨hne, hd⟩
    exact ⟨hne.symm, fun h => hd h.symm⟩
  Kirrefl := by rintro a ⟨h, _⟩; exact h rfl
  decK := by intro a b; infer_instance

/-- The footprint of the host triangle `(e, h)`: the base `e` and the links `(h, x)` for the
endpoints `x` of `e`. -/
def triRes {E V H : Type*} [DecidableEq E] [DecidableEq V] [DecidableEq H]
    (ends : E → Finset V) (t : E × H) : Finset (E ⊕ (H × V)) :=
  {Sum.inl t.1} ∪ (ends t.1).image (fun x => Sum.inr (t.2, x))

/-- The base system: bases conflict iff they share an endpoint. -/
abbrev baseCS {E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V] (ends : E → Finset V) :
    ConflictSystem :=
  resCS (α := E) (R := V) ends

/-- The host system with hosts `H`: host triangles conflict iff their footprints meet. -/
abbrev hostCS {E V : Type*} (H : Type*) [Fintype E] [DecidableEq E] [DecidableEq V] [Fintype H]
    [DecidableEq H] (ends : E → Finset V) : ConflictSystem :=
  resCS (α := E × H) (R := E ⊕ (H × V)) (triRes ends)

/-- The host system restricted to the requested bases `B`. -/
abbrev hostCSOn {E V : Type*} (H : Type*) [DecidableEq E] [DecidableEq V] [Fintype H]
    [DecidableEq H] (ends : E → Finset V) (B : Finset E) : ConflictSystem :=
  resCS (α := {e : E // e ∈ B} × H) (R := E ⊕ (H × V)) (fun t => triRes ends (t.1.1, t.2))

/-- A proper list host assignment on a set `T` of bases: hosts from the lists, distinct hosts on
bases sharing an endpoint. -/
structure ProperOn {E V H : Type*} [DecidableEq E] [DecidableEq V] (ends : E → Finset V)
    (L : E → Finset H) (T : Finset E) (c : E → H) : Prop where
  mem : ∀ e ∈ T, c e ∈ L e
  proper : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → ¬ Disjoint (ends e) (ends e') → c e ≠ c e'

/-- The weight of a host triangle is the weight of its base. -/
def triWeight {E H : Type*} (w : E → ℕ) (t : E × H) : ℕ := w t.1

/-- The admissibility class of host realizers with lists `L`. -/
def HostClass {E V H : Type*} [Fintype E] [DecidableEq E] [DecidableEq V] [Fintype H]
    [DecidableEq H] (ends : E → Finset V) (L : E → Finset H) (w : E → ℕ) (X : E → ℕ) :
    RealizerClass (baseCS ends) (hostCS H ends) w (triWeight w) X :=
  fun S r => ∃ c : E → H, ProperOn ends L (S.image (objOf (C := baseCS ends) (X := X))) c ∧
    r.out = (S.image (objOf (C := baseCS ends) (X := X))).image (fun e => (e, c e)) ∧ r.loss = 0

/-- The endpoints of the bipartite base `(u, r)`. -/
def bipEnds {U R : Type*} [DecidableEq U] [DecidableEq R] (e : U × R) : Finset (U ⊕ R) :=
  {Sum.inl e.1, Sum.inr e.2}

/-- The degree of `u` in the request graph `B`. -/
def degB₁ {U R : Type*} [DecidableEq U] (B : Finset (U × R)) (u : U) : ℕ :=
  (B.filter fun e => e.1 = u).card

/-- The degree of `r` in the request graph `B`. -/
def degB₂ {U R : Type*} [DecidableEq R] (B : Finset (U × R)) (r : R) : ℕ :=
  (B.filter fun e => e.2 = r).card

/-- The left degree of `u` in the bipartite multigraph with edge set `E`. -/
def degL {U E : Type*} [Fintype E] [DecidableEq U] (left : E → U) (u : U) : ℕ :=
  (Finset.univ.filter fun e => left e = u).card

/-- The right degree of `r` in the bipartite multigraph with edge set `E`. -/
def degR {R E : Type*} [Fintype E] [DecidableEq R] (right : E → R) (r : R) : ℕ :=
  (Finset.univ.filter fun e => right e = r).card

/-- The endpoints of the edge `(u, v)` of `K_{r,r}`. -/
def krEnds (r : ℕ) (e : Fin r × Fin r) : Finset (Fin r ⊕ Fin r) := {Sum.inl e.1, Sum.inr e.2}

/-! ### Triangle packings and vertex copies (§6) -/

/-- The edges of `G` with both endpoints in the vertex set `t`. -/
def edgesIn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- An (integral) triangle packing of `G`: a family of triangles of `G`, any two of which share
at most one vertex, i.e. no edge. -/
def IsTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → #(s ∩ t) ≤ 1

/-- `ν₃(G)`: the maximum number of pairwise edge-disjoint triangles of `G`. -/
noncomputable def nu3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sSup {k | ∃ P : Finset (Finset V), IsTrianglePacking G P ∧ P.card = k}

/-- A fractional triangle packing of `G`: nonnegative weights on vertex sets such that, for every
edge `e` of `G`, the triangles of `G` containing `e` have total weight at most one. -/
def IsFracTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t ≤ 1

/-- `ν₃*(G)`: the supremum of the total weight of a fractional triangle packing. -/
noncomputable def nu3star {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ w, IsFracTrianglePacking G w ∧ x = ∑ t ∈ G.cliqueFinset 3, w t}

/-- The vertex copy `G_{v→u}`: the neighbourhood of `v` is replaced by that of `u`. -/
def copyGraph {V : Type*} (G : SimpleGraph V) (v u : V) : SimpleGraph V where
  Adj a b :=
    (a ≠ v ∧ b ≠ v ∧ G.Adj a b) ∨
    (a = v ∧ b ≠ v ∧ G.Adj u b) ∨
    (b = v ∧ a ≠ v ∧ G.Adj u a)
  symm := by
    constructor
    rintro a b (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  loopless := by
    refine ⟨fun a h => ?_⟩
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact h3.ne rfl
    · exact h2 h1
    · exact h2 h1

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) :
    DecidableRel (copyGraph G v u).Adj := by
  intro a b; unfold copyGraph; infer_instance

/-- The triangle conflict system of `G`: the triangles, two of them conflicting iff they share
an edge. -/
abbrev triCS {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ConflictSystem where
  O := {t : Finset V // t ∈ G.cliqueFinset 3}
  K t₁ t₂ := t₁.1 ≠ t₂.1 ∧ 2 ≤ (t₁.1 ∩ t₂.1).card
  Ksymm := by
    rintro a b ⟨h1, h2⟩
    exact ⟨h1.symm, by rwa [Finset.inter_comm]⟩
  Kirrefl := by rintro a ⟨h1, _⟩; exact h1 rfl
  decK := by intro a b; dsimp only; infer_instance

/-! ### Pure profiles and mixed copies (§7) -/

/-- Pure-profile objects: a host `Fin m` and a pair from the common palette `Fin s`. -/
abbrev PureObj (m s : ℕ) := Fin m × {e : Finset (Fin s) // e.card = 2}

/-- Pure-profile feasibility: pairs at a common host are disjoint, and each pair is used at most
once. -/
def PureFeasible (m s : ℕ) (R : Finset (PureObj m s)) : Prop :=
  (∀ x ∈ R, ∀ y ∈ R, x ≠ y → x.1 = y.1 → (x.2.1 ∩ y.2.1) = ∅) ∧
  (∀ x ∈ R, ∀ y ∈ R, x.2.1 = y.2.1 → x.1 = y.1)

open Classical in
noncomputable instance (m s : ℕ) : DecidablePred (PureFeasible m s) := Classical.decPred _

/-- The pure-profile packing number. -/
noncomputable def pureNu (m s : ℕ) : ℕ := (univ.filter (PureFeasible m s)).sup Finset.card

/-- The mixed conflict system of `G`: the cliques of size 3 or 4, two of them conflicting iff they
share an edge. -/
abbrev mixedCS {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ConflictSystem where
  O := {t : Finset V // t ∈ G.cliqueFinset 3 ∨ t ∈ G.cliqueFinset 4}
  K t₁ t₂ := t₁.1 ≠ t₂.1 ∧ 2 ≤ (t₁.1 ∩ t₂.1).card
  Ksymm := by
    rintro a b ⟨h1, h2⟩
    exact ⟨h1.symm, by rwa [Finset.inter_comm]⟩
  Kirrefl := by rintro a ⟨h1, _⟩; exact h1 rfl
  decK := by intro a b; dsimp only; infer_instance

/-- The size-dependent gain as a weight on the mixed system. -/
def mixedWeight {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (gainOf : ℕ → ℕ) : (mixedCS G).O → ℕ :=
  fun t => gainOf t.1.card

/-- The edge load of a weighting of the mixed cliques at the pair `{a, b}`. -/
noncomputable def mixedEdgeLoad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : (mixedCS G).O → ℝ) (a b : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : (mixedCS G).O => a ∈ t.1 ∧ b ∈ t.1), y t

/-- A fractional mixed packing: nonnegative weights with edge load at most one on every pair. -/
def IsFracMixedPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : (mixedCS G).O → ℝ) : Prop :=
  (∀ t, 0 ≤ y t) ∧ (∀ a b : V, a ≠ b → mixedEdgeLoad G y a b ≤ 1)

/-- The fractional weighted mixed packing number `W*(G)` for the size-dependent gain. -/
noncomputable def Wstar {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (gain : ℕ → ℕ) : ℝ :=
  sSup { s : ℝ | ∃ y : (mixedCS G).O → ℝ, IsFracMixedPacking G y ∧
    s = ∑ t, (gain t.1.card : ℝ) * y t }

/-! ### Statements -/

/-- **Lemma 3.1 (splitting).** Every finite graph has two disjoint independent sets covering all
but `oct(H)` vertices. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    ∃ S₁ S₂ : Finset V, Disjoint S₁ S₂ ∧ Feasible H S₁ ∧ Feasible H S₂ ∧
      Fintype.card V - oct H ≤ S₁.card + S₂.card := by
  sorry

/-- **Corollary 3.2.** For every `q`-multiset `X`, `ν ≥ ⌈(|X| − D_q(H[X])) / q⌉`. -/
theorem corollary_3_2 (C : ConflictSystem) (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q)
    (hX : IsQMultiset C X q) :
    (multSize C X - Dq (Hgraph C X) q + (q - 1)) / q ≤ nu C := by
  sorry

/-- **Theorem 3.4 (`q`-integral transfer).** If a resource-dominated relaxation has a
`1/q`-integral optimum `x*` (with all coordinates at most one) and `X` has `q x*_o` copies of
each object, then `X` is a `q`-multiset and `μ* − ν ≤ D_q(H[X]) / q`. -/
theorem theorem_3_4 {C : ConflictSystem} (P : ResourceRelaxation C) (x : P.Optimum) {q : ℕ}
    (hq : 0 < q) {X : C.O → ℕ} (hX : ∀ o, (q : ℝ) * x.point o = (X o : ℝ))
    (hbounded : ∀ o, x.point o ≤ 1) :
    IsQMultiset C X q ∧ x.value - (nu C : ℝ) ≤ (Dq (Hgraph C X) q : ℝ) / q := by
  sorry

/-- **Theorem 3.3 (half-integral transfer).** The case `q = 2`: `μ* − ν ≤ oct(H[X]) / 2`. -/
theorem theorem_3_3 {C : ConflictSystem} (P : ResourceRelaxation C) (x : P.Optimum)
    {X : C.O → ℕ} (hX : ∀ o, (2 : ℝ) * x.point o = (X o : ℝ))
    (hbounded : ∀ o, x.point o ≤ 1) :
    IsQMultiset C X 2 ∧ x.value - (nu C : ℝ) ≤ (oct (Hgraph C X) : ℝ) / 2 := by
  sorry

/-- **Theorem 3.4w (weighted transfer).** `|X|_w ≤ q ν_w + D_q^w(H[X])`. -/
theorem theorem_3_4w (C : ConflictSystem) (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q) :
    wMultSize C w X ≤ q * wNu C w + wDq C w X q := by
  sorry

/-- **Theorem 4.2 (realizable-class transfer).** Every realizability certificate has a class whose
realization satisfies `|X|_w ≤ q w_P(R(C_i)) + cost`. -/
theorem theorem_4_2 {C P : ConflictSystem} {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (cert : RealCert C P w wP X q) :
    ∃ i : Fin q, wMultSize C w X ≤ q * ∑ o ∈ (cert.real i).out, wP o + cert.cost := by
  sorry

/-- **Theorem 4.2, second assertion.** `|X|_w ≤ q ν_{w_P}(P) + cost`. -/
theorem theorem_4_2_nu {C P : ConflictSystem} {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ}
    {q : ℕ} (hq : 1 ≤ q) (cert : RealCert C P w wP X q) :
    wMultSize C w X ≤ q * wNu P wP + cert.cost := by
  sorry

/-- **Theorem 4.4.** For the identity admissibility class, the realizability defect is the
weighted colourability defect: `D^w_{q,ℛ_id}(X) = D_q^w(H[X])`. -/
theorem theorem_4_4 {C : ConflictSystem} {w X : C.O → ℕ} {q : ℕ} (hq : 1 ≤ q) :
    wRDq (IdentityClass C w X) q = wDq C w X q := by
  sorry

/-- **Theorem 5.2 (Galvin, bipartite multigraphs).** If every vertex of a bipartite multigraph
has degree at most `Δ` and every edge list has at least `Δ` colours, there is a proper list edge
colouring. -/
theorem theorem_5_2_galvin {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U]
    [DecidableEq R] [DecidableEq E] (left : E → U) (right : E → R) (Δ : ℕ)
    (hdegU : ∀ u, degL left u ≤ Δ) (hdegR : ∀ r, degR right r ≤ Δ)
    (L : E → Finset ℕ) (hL : ∀ e, Δ ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  sorry

/-- **Theorem 5.2 (Borodin–Kostochka–Woodall, local form).** Lists of size at least
`max(d(u), d(v))` on each edge `uv` of a bipartite multigraph suffice. -/
theorem theorem_5_2_bkw {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U]
    [DecidableEq R] [DecidableEq E] (left : E → U) (right : E → R)
    (L : E → Finset ℕ) (hL : ∀ e, max (degL left (left e)) (degR right (right e)) ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  sorry

/-- **Corollary 5.3 (host completion, Galvin regime).** With degrees at most `Δ` and host lists of
size at least `Δ`, the host system restricted to the requested bases `B` has packing number
`|B|`. -/
theorem corollary_5_3_galvin {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R]
    [DecidableEq R] [Fintype H] [DecidableEq H] [Nonempty H] (B : Finset (U × R)) (Δ : ℕ)
    (hdegU : ∀ u, (B.filter fun e => e.1 = u).card ≤ Δ)
    (hdegR : ∀ r, (B.filter fun e => e.2 = r).card ≤ Δ)
    (L : U × R → Finset H) (hL : ∀ e ∈ B, Δ ≤ (L e).card) :
    nu (hostCSOn H bipEnds B) = B.card := by
  sorry

/-- **Corollary 5.3 (host completion, local regime).** -/
theorem corollary_5_3_bkw {U R H : Type*} [Fintype U] [DecidableEq U] [Fintype R]
    [DecidableEq R] [Fintype H] [DecidableEq H] [Nonempty H] (B : Finset (U × R))
    (L : U × R → Finset H) (hL : ∀ e ∈ B, max (degB₁ B e.1) (degB₂ B e.2) ≤ (L e).card) :
    nu (hostCSOn H bipEnds B) = B.card := by
  sorry

/-- **Example 5.5 (strict separation).** For `K_{r,r}` with unit weights, `q = 1` and `r` hosts
with full lists: `D_1 = r² − r`, the host realizability defect is `0`, and the host system has
packing number `r²`. -/
theorem example_5_5 (r : ℕ) [NeZero r] :
    wDq (baseCS (krEnds r)) (fun _ => 1) (fun _ => 1) 1 = r * r - r ∧
    wRDq (HostClass (krEnds r) (fun _ => (Finset.univ : Finset (Fin r))) (fun _ => 1)
      (fun _ => 1)) 1 = 0 ∧
    nu (hostCS (Fin r) (krEnds r)) = r * r := by
  sorry

/-- **Theorem 6.1 (fractional copy inequality).** For nonadjacent `u, v`,
`ν₃*(G_{v→u}) + ν₃*(G_{u→v}) ≤ 2 ν₃*(G)`. -/
theorem theorem_6_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) :
    nu3star (copyGraph G v u) + nu3star (copyGraph G u v) ≤ 2 * nu3star G := by
  sorry

/-- **Theorem 6.2 (integral copy inequality).** For nonadjacent `u, v` there is a multiset `T₂` of
triangles of `G` (the images of optimal packings of the two copies) with
`ν₃(G_{v→u}) + ν₃(G_{u→v}) = |T₂| ≤ 2 ν₃(G) + oct(H[T₂])`. -/
theorem theorem_6_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) :
    ∃ T₂ : (triCS G).O → ℕ,
      multSize (triCS G) T₂ = nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ∧
      nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ≤ 2 * nu3 G + oct (Hgraph (triCS G) T₂) := by
  sorry

/-- **Corollary 6.2a (triple copy bound).** For nonadjacent `u, v`,
`ν₃(G_{v→u}) + ν₃(G_{u→v}) ≤ 3 ν₃(G)`. -/
theorem corollary_6_2a {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) :
    nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ≤ 3 * nu3 G := by
  sorry

/-- **Proposition 7.1 (pure profile, integral value).** With `m` hosts and a common palette of
size `s`, the packing number is `min(m ⌊s/2⌋, C(s,2))`. -/
theorem proposition_7_1 (m s : ℕ) : pureNu m s = min (m * (s / 2)) (s.choose 2) := by
  sorry

/-- **Theorem 7.3 (mixed copy inequality, fractional).** For nonadjacent `u, v` and every
size-dependent gain, `W*(G_{v→u}) + W*(G_{u→v}) ≤ 2 W*(G)`. -/
theorem theorem_7_3_fractional {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) (gain : ℕ → ℕ) :
    Wstar (copyGraph G v u) gain + Wstar (copyGraph G u v) gain ≤ 2 * Wstar G gain := by
  sorry

/-- **Theorem 7.3 (mixed copy inequality, integral).** For nonadjacent `u, v` and every
size-dependent gain there is a multiset `X` of cliques of `G` (the images of optimal mixed
packings of the copies) with
`ν_w(G_{v→u}) + ν_w(G_{u→v}) = |X|_w ≤ 2 ν_w(G) + D_2^w(H[X])`. -/
theorem theorem_7_3_integral {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u : V) (huv : ¬ G.Adj u v) (gainOf : ℕ → ℕ) :
    ∃ X : (mixedCS G).O → ℕ,
      wMultSize (mixedCS G) (mixedWeight G gainOf) X =
        wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf) +
          wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf) ∧
      wNu (mixedCS (copyGraph G v u)) (mixedWeight _ gainOf) +
          wNu (mixedCS (copyGraph G u v)) (mixedWeight _ gainOf) ≤
        2 * wNu (mixedCS G) (mixedWeight G gainOf) + wDq (mixedCS G) (mixedWeight G gainOf) X 2 := by
  sorry

end ErdosPaperV
