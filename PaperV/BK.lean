/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — §6.1 (BK) counterexample: `β < k` does NOT imply zero integrality gap.
Ledger node L-C1 (finite, host-clique + master-LP witness).

Concrete instance (vertices `Fin 6`, 8 hosts) with the 27 coverable objects `(host, pair)`
enumerated in `objs`. Facts (certified exhaustively; here formalised):
  ν = 9, |cov| = 12, k = |cov| − ν = 3, and β = 2 (over all 70 maximum packings), so β < k;
  yet the master matching LP has a rational feasible point (`witness`) of value 19/2 > 9 = ν,
  so the gap `μ*_mat − ν ≥ 1/2 > 0`. Hence `β < k ⇏ gap = 0` — the conjecture is FALSE.

The master-LP feasibility (`MasterFeasible`) is the *defining inequalities* of the matching LP,
per host: nonnegativity, per-pair global capacity ≤ 1, per-host vertex degree ≤ 1, and the
odd-set (blossom) inequalities `∑_{e ⊆ S} x ≤ (|S|−1)/2` for odd `S`. No blossom *theory* is
invoked — only the syntactic inequalities, checked on the frozen rational `witness`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import Aesop
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
public import PaperV.PackingCert

@[expose] public section

open Finset

namespace PaperV
namespace BK

/-- The 27 coverable objects `(host, a, b)` (each pair `a<b` in the host's palette). -/
def objs : Fin 27 → (Fin 8 × Fin 6 × Fin 6) :=
  ![(0,0,1),(1,0,3),(1,0,5),(1,3,5),(2,0,5),(3,0,2),(3,0,3),(3,0,4),(3,2,3),(3,2,4),
    (3,3,4),(4,0,1),(4,0,2),(4,0,4),(4,1,2),(4,1,4),(4,2,4),(5,0,3),(5,0,4),(5,0,5),
    (5,3,4),(5,3,5),(5,4,5),(6,0,1),(7,0,4),(7,0,5),(7,4,5)]

def opair (i : Fin 27) : Finset (Fin 6) := {(objs i).2.1, (objs i).2.2}
def ohost (i : Fin 27) : Fin 8 := (objs i).1

/-- Integral feasible host-clique packing: global pair-uniqueness + per-host matching. -/
def Feasible (R : Finset (Fin 27)) : Prop :=
  (∀ i ∈ R, ∀ j ∈ R, i ≠ j → opair i ≠ opair j) ∧
  (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ohost i = ohost j → (opair i ∩ opair j) = ∅)

open Classical in
noncomputable instance : DecidablePred Feasible := Classical.decPred _

/-- A `Bool`-valued, kernel-computable version of `Feasible`, used to certify concrete packings. -/
private def CFeasible (R : Finset (Fin 27)) : Bool :=
  (List.ofFn id).all fun i => (List.ofFn id).all fun j =>
    !(i ∈ R) || !(j ∈ R) || (i == j) || ((opair i != opair j) &&
      ((ohost i != ohost j) || (opair i ∩ opair j == ∅)))

private lemma cFeasible_eq (R : Finset (Fin 27)) : CFeasible R ↔ Feasible R := by
  constructor
  · intro hc
    have hall : ∀ i : Fin 27, ∀ j : Fin 27,
        (!(i ∈ R) || !(j ∈ R) || (i == j) || ((opair i != opair j) &&
          ((ohost i != ohost j) || (opair i ∩ opair j == ∅)))) = true := by
      intro i j
      have hi := (List.all_eq_true.mp hc) i (List.mem_ofFn.mpr ⟨i, rfl⟩)
      exact (List.all_eq_true.mp hi) j (List.mem_ofFn.mpr ⟨j, rfl⟩)
    constructor
    · intro i hi j hj hn
      have h := hall i j
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
      aesop
    · intro i hi j hj hn heq
      have h := hall i j
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
      aesop
  · rintro ⟨hp, hh⟩
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro j hj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    by_cases hiR : i ∈ R
    · by_cases hjR : j ∈ R
      · by_cases hij : i = j
        · exact Or.inl (Or.inr hij)
        · refine Or.inr ⟨hp i hiR j hjR hij, ?_⟩
          by_cases heq : ohost i = ohost j
          · exact Or.inr (hh i hiR j hjR hij heq)
          · exact Or.inl heq
      · exact Or.inl (Or.inl (Or.inr (by simpa using hjR)))
    · exact Or.inl (Or.inl (Or.inl (by simpa using hiR)))

/-- The integral packing number `ν`. -/
noncomputable def nu : ℕ := (univ.filter Feasible).sup Finset.card

/-! ### The BK instance as a conflict system

`Feasible` is exactly independence in the following conflict system, so the general certificate
theory of `PaperV.PackingCert` applies to it verbatim. -/

/-- The conflict system underlying the BK instance: two of the 27 objects conflict when they are
distinct and either realise the same pair, or share a host and a vertex. -/
abbrev bkCS : ConflictSystem where
  O := Fin 27
  K i j := i ≠ j ∧ (opair i = opair j ∨ (ohost i = ohost j ∧ opair i ∩ opair j ≠ ∅))
  Ksymm := by
    rintro i j ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h1.symm, by rwa [Finset.inter_comm]⟩
  Kirrefl := fun _ h => h.1 rfl

/-- `Feasible` is independence in `bkCS`. -/
theorem feasible_iff_csFeasible (R : Finset (Fin 27)) : Feasible R ↔ CSFeasible bkCS R := by
  constructor
  · rintro ⟨h1, h2⟩ a ha b hb ⟨hne, h⟩
    rcases h with h | ⟨he, hi⟩
    · exact h1 a ha b hb hne h
    · exact hi (h2 a ha b hb hne he)
  · refine fun h => ⟨fun i hi j hj hij he => h hi hj ⟨hij, Or.inl he⟩, fun i hi j hj hij he => ?_⟩
    by_contra hne
    exact h hi hj ⟨hij, Or.inr ⟨he, hne⟩⟩

/-- `ν` of the BK instance is the packing number of `bkCS`. -/
theorem nu_eq_nu_bkCS : nu = PaperV.nu bkCS := by
  classical
  refine le_antisymm (Finset.sup_le fun R hR => ?_) (Finset.sup_le fun R hR => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hR
    exact Finset.le_sup (f := Finset.card) (by simp [(feasible_iff_csFeasible R).mp hR])
  · simp only [mem_filter, mem_univ, true_and] at hR
    exact Finset.le_sup (f := Finset.card) (by simp [(feasible_iff_csFeasible R).mpr hR])

/-- The 27 objects indexed by `ℕ` (indices are read modulo 27; all index lists used below lie in
`List.range 27`).  Keeping the certificates `ℕ`-indexed is what lets the kernel evaluate them with
machine-backed arithmetic. -/
private def fv (n : Nat) : Fin 27 := ⟨n % 27, Nat.mod_lt _ (by norm_num)⟩

private lemma fv_val {n : Nat} (h : n ∈ List.range 27) : (fv n).val = n :=
  Nat.mod_eq_of_lt (List.mem_range.mp h)

private lemma fv_surj : ∀ o : Fin 27, o ∈ (List.range 27).map fv := fun o =>
  List.mem_map.mpr ⟨o.val, List.mem_range.mpr o.isLt,
    by simp [fv, Nat.mod_eq_of_lt o.isLt]⟩

/-- The frozen rational master-LP witness (value 19/2). Nonzero entries only. -/
noncomputable def witness : Fin 27 → ℚ := fun i =>
  if i = 0 ∨ i = 3 ∨ i = 4 then 1
  else if i ∈ ({5,6,9,10,12,13,14,15,17,20,22,24,26} : Finset (Fin 27)) then (1:ℚ)/2
  else 0

/-- Twice the witness, valued in `ℕ`, for kernel-computable bounds. -/
private def w2 : Fin 27 → ℕ := fun i =>
  if i = 0 ∨ i = 3 ∨ i = 4 then 2
  else if i ∈ ({5,6,9,10,12,13,14,15,17,20,22,24,26} : Finset (Fin 27)) then 1
  else 0

private lemma witness_eq_w2 (i : Fin 27) : witness i = (w2 i : ℚ) / 2 := by
  fin_cases i <;> simp [witness, w2]

/-- The total value of a weighting. -/
noncomputable def lpValue (x : Fin 27 → ℚ) : ℚ := ∑ i, x i

/-- If twice the masses on a filtered set sum to `≤ 2`, the rational witness masses sum to `≤ 1`. -/
private lemma sum_witness_le_one (P : Fin 27 → Prop) [DecidablePred P]
    (hb : (∑ i ∈ univ.filter P, w2 i) ≤ 2) :
    (∑ i ∈ univ.filter P, witness i) ≤ 1 := by
  have heq : (∑ i ∈ univ.filter P, witness i)
      = ((∑ i ∈ univ.filter P, w2 i : ℕ) : ℚ) / 2 := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => witness_eq_w2 i)
  rw [heq]
  have h2 : ((∑ i ∈ univ.filter P, w2 i : ℕ) : ℚ) ≤ 2 := by exact_mod_cast hb
  linarith

/-! ### Independence-number machinery (kernel-computable, over `ℕ` indices)

The conflict relation on the 27 objects is stored as a packed `27 × 27` bit table, so that the
kernel evaluates `conflict` with a single machine-backed `Nat` shift.  The table is certified
against the intended semantics (`opair`/`ohost`) by `conflict_bridge`, which is the only
property of it that the proofs below use. -/

/-- Packed conflict table: bit `27 * i + j` is set iff objects `i` and `j` conflict. -/
private def confBits : Nat :=
  2559262668571990658261079932200052203429928212798360803040341040034069012286586307968162725127333903885425830148192513099042048609799600377283733784279703538991916434940551494956847827727110711915541801811369212243871745

/-- Two objects conflict iff they realise the same pair, or share a host and a vertex; see
`conflict_bridge`. -/
private def conflict (i j : Nat) : Bool := (confBits >>> (27 * i + j)) &&& 1 == 1

/-- The packed table matches the intended semantics on `opair`/`ohost`. -/
private lemma conflict_bridge (i j : Fin 27) :
    conflict i.val j.val = true ↔
      opair i = opair j ∨ (ohost i = ohost j ∧ opair i ∩ opair j ≠ ∅) := by
  revert i j; decide

/-- The packed conflict table soundly over-approximates the conflict relation of `bkCS`. -/
private lemma conflict_sound : ∀ i ∈ List.range 27, ∀ j ∈ List.range 27,
    fv i ≠ fv j → conflict i j = true → bkCS.K (fv i) (fv j) := by
  intro i hi j hj hne hc
  rw [← fv_val hi, ← fv_val hj] at hc
  exact ⟨hne, (conflict_bridge (fv i) (fv j)).mp hc⟩

set_option maxHeartbeats 1000000 in
/-- Branch-and-bound certificate: the 27 objects carry no feasible packing of size `10`. -/
private lemma noPacking_all :
    PackingCert.NoPacking conflict (List.range 27).length 10 (List.range 27) = true := by decide

theorem nu_le_nine : nu ≤ 9 := by
  have h : PaperV.nu bkCS < 10 :=
    PackingCert.nu_lt_of_noPacking (C := bkCS) (f := fv) fv_surj conflict_sound noPacking_all
  rw [nu_eq_nu_bkCS]
  omega

/-- **BK (§6.1).** The witness is a nonnegative point respecting every defining master-LP
inequality (per-pair capacity, per-host degree, per-host odd-set) with total value `19/2`,
while `ν = 9`. Hence the matching-LP value exceeds `ν`: the integrality gap is `≥ 1/2 > 0`,
with `β = 2 < 3 = k`. -/
theorem bk_nu : nu = 9 := by
  apply Nat.le_antisymm nu_le_nine
  · have hR : Feasible ({0,1,4,5,10,13,14,21,26} : Finset (Fin 27)) :=
      (cFeasible_eq _).mp (by decide)
    have hm : ({0,1,4,5,10,13,14,21,26} : Finset (Fin 27)) ∈ univ.filter Feasible := by
      simp [hR]
    have hc : ({0,1,4,5,10,13,14,21,26} : Finset (Fin 27)).card = 9 := by decide
    have hle := Finset.le_sup (f := Finset.card) hm
    rw [hc] at hle
    exact hle

theorem bk_witness_value : lpValue witness = 19 / 2 := by
  unfold lpValue
  simp [Fin.sum_univ_succ, witness]
  norm_num

set_option maxHeartbeats 4000000 in
private lemma w2_pair : ∀ e : Finset (Fin 6),
    (∑ i ∈ univ.filter (fun i => opair i = e), w2 i) ≤ 2 := by decide

/-- Per-pair global capacity: for each coverable pair `e`, the witness mass on objects realising
`e` is `≤ 1`. -/
theorem bk_witness_pair_cap :
    ∀ e : Finset (Fin 6), (∑ i ∈ univ.filter (fun i => opair i = e), witness i) ≤ 1 :=
  fun e => sum_witness_le_one _ (w2_pair e)

set_option maxHeartbeats 4000000 in
private lemma w2_deg : ∀ (j : Fin 8) (a : Fin 6),
    (∑ i ∈ univ.filter (fun i => ohost i = j ∧ a ∈ opair i), w2 i) ≤ 2 := by decide

/-- Per-host degree: for each host `j` and vertex `a`, the witness mass on objects at host `j`
whose pair contains `a` is `≤ 1`. -/
theorem bk_witness_degree :
    ∀ (j : Fin 8) (a : Fin 6),
      (∑ i ∈ univ.filter (fun i => ohost i = j ∧ a ∈ opair i), witness i) ≤ 1 :=
  fun j a => sum_witness_le_one _ (w2_deg j a)

set_option maxHeartbeats 8000000 in
private lemma w2_odd : ∀ (j : Fin 8) (S : Finset (Fin 6)), S.card = 3 →
    (∑ i ∈ univ.filter (fun i => ohost i = j ∧ opair i ⊆ S), w2 i) ≤ 2 := by decide

/-- Per-host odd-set (blossom) inequality: for each host `j` and each `3`-element subset `S` of
its palette, the witness mass on objects `(j,e)` with `e ⊆ S` is `≤ 1 = (3−1)/2`. (Palettes have
size ≤ 4, so the only odd sets with `|S| ≥ 3` are the 3-subsets.) These are exactly the master-LP
constraints beyond degree/capacity; without them the witness would only certify the weaker
resource LP. -/
theorem bk_witness_oddset :
    ∀ (j : Fin 8) (S : Finset (Fin 6)), S.card = 3 →
      (∑ i ∈ univ.filter (fun i => ohost i = j ∧ opair i ⊆ S), witness i) ≤ 1 :=
  fun j S hS => sum_witness_le_one _ (w2_odd j S hS)

/-- Nonnegativity of the witness. -/
theorem bk_witness_nonneg : ∀ i, 0 ≤ witness i := by
  intro i
  fin_cases i <;> simp [witness]

/-- Gap positivity, assembled: the witness value `19/2` exceeds `ν = 9`. -/
theorem bk_gap_pos : (9 : ℚ) < lpValue witness := by
  rw [bk_witness_value]; norm_num

/-- The set of coverable pairs (image of all objects' pairs); `|cov| = 12`. -/
def cov : Finset (Finset (Fin 6)) := univ.image opair

set_option maxHeartbeats 4000000 in
theorem bk_cov_card : cov.card = 12 := by decide

/-! ### Pair codes

The pair `{a, b} ⊆ Fin 6` of an object is encoded as the 6-bit mask `2^a + 2^b`, and all 27 masks
are packed into a single `Nat`, so that the kernel reads a pair code off with one shift. Equality
and disjointness of pairs become `Nat` operations; `pc_eq_iff` and `pc_disj_iff` certify the
encoding against `opair`. -/

/-- Packed pair table: bits `6 * t … 6 * t + 5` hold the pair mask of object `t`. -/
private def pcBits : Nat := 4431984508640085516034434145677894359215736230467

/-- The pair of object `t`, as a 6-bit mask. -/
private def pc (t : Nat) : Nat := (pcBits >>> (6 * t)) &&& 63

/-- The 12 coverable pairs, as masks (`cov` in coded form). -/
private def covL : List Nat := [12, 5, 6, 18, 20, 9, 24, 40, 3, 17, 33, 48]

private lemma pc_eq_iff (i j : Fin 27) : pc i.val = pc j.val ↔ opair i = opair j := by
  revert i j; decide

private lemma pc_disj_iff (i j : Fin 27) :
    pc i.val &&& pc j.val = 0 ↔ Disjoint (opair i) (opair j) := by
  revert i j; decide

private lemma pc_mem_covL (i : Fin 27) : pc i.val ∈ covL := by revert i; decide

/-! ### Clique-cover certificates

A cheap certificate for "no feasible packing of size `m + 1` inside `l`": a colouring of `l` by
`m` colours in which any two distinct objects of the same colour conflict (i.e. a cover of `l` by
`m` cliques of the conflict graph).  A feasible packing meets each colour class at most once.
Colourings are packed nibble-wise into a single `Nat`. -/

/-- Colour of object `t` under the packed colouring `d`. -/
private def col (d t : Nat) : Nat := (d >>> (4 * t)) &&& 15

/-- `colChk d l` says that `d` colours `l` with colours `< 8`, any two distinct objects of `l`
sharing a colour being in conflict. -/
private def colChk (d : Nat) (l : List Nat) : Bool :=
  l.all fun i => decide (col d i < 8) &&
    l.all fun j => (i == j) || (col d i != col d j) || conflict i j

private lemma colChk_lt {d : Nat} {l : List Nat} (h : colChk d l = true) :
    ∀ i ∈ l, col d i < 8 := by
  intro i hi
  have := (List.all_eq_true.mp h) i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

private lemma colChk_conflict {d : Nat} {l : List Nat} (h : colChk d l = true) :
    ∀ i ∈ l, ∀ j ∈ l, i ≠ j → col d i = col d j → conflict i j = true := by
  intro i hi j hj hij hcol
  have h1 := (List.all_eq_true.mp h) i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  have h2 := (List.all_eq_true.mp h1.2) j hj
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
  rcases h2 with (h2 | h2) | h2
  · exact absurd h2 hij
  · exact absurd hcol h2
  · exact h2

/-- A feasible packing indexed inside a list carrying an `8`-colouring has at most `8` elements:
the colouring is a cover by `8` conflict-cliques, so `PackingCert.card_le_of_colouring` applies. -/
private lemma feasible_card_le_of_colChk {d : Nat} {l : List Nat} (hl : ∀ i ∈ l, i ∈ List.range 27)
    (h : colChk d l = true) (R : Finset (Fin 27)) (hsub : ∀ i ∈ R, i.val ∈ l) (hR : Feasible R) :
    R.card ≤ 8 := by
  refine PackingCert.card_le_of_colouring (f := fv) (col := col d)
    (fun i hi => colChk_lt h i hi) (fun i hi j hj hne hcol => ?_) (fun o ho => ?_)
    ((feasible_iff_csFeasible R).mp hR)
  · have hij : i ≠ j := by rintro rfl; exact hne rfl
    have hc : conflict (fv i).val (fv j).val = true := by
      rw [fv_val (hl i hi), fv_val (hl j hj)]
      exact colChk_conflict h i hi j hj hij hcol
    exact ⟨hne, (conflict_bridge (fv i) (fv j)).mp hc⟩
  · exact List.mem_map.mpr ⟨o.val, hsub o ho,
      by simp [fv, Nat.mod_eq_of_lt o.isLt]⟩

/-- The seven `8`-clique covers used by `three_uncovered_bound`, packed nibble-wise. -/
private def colTbl : List Nat :=
  [161390057905900874196552942296848, 306137433891006427625177835700239,
   144752007385059378426733374140944, 307093144217159536512544399299056,
   161310763246277283920673515712272, 145703052459047525898876892672528,
   143638170765525539140896116830223]

set_option maxHeartbeats 4000000 in
/-- Removing all objects realising any of three pairwise-disjoint coverable pairs leaves a set of
objects covered by `8` conflict-cliques, hence carrying no feasible packing of size `9`. -/
private lemma three_uncovered_bound :
    ∀ a ∈ covL, ∀ b ∈ covL, ∀ c ∈ covL,
      a &&& b = 0 → a &&& c = 0 → b &&& c = 0 →
      ∃ d ∈ colTbl, colChk d ((List.range 27).filter fun t =>
        (pc t != a) && (pc t != b) && (pc t != c)) = true := by
  decide

/-- `β < k`: with `k = |cov| − ν = 3`, no maximum packing leaves three pairwise vertex-disjoint
coverable pairs uncovered (so its residual matching number `α' ≤ 2 < 3 = k`). This is `β = 2 < k`. -/
theorem bk_beta_lt_k :
    ∀ R : Finset (Fin 27), Feasible R → R.card = nu →
      ¬ ∃ a b c : Finset (Fin 6),
        a ∈ cov ∧ b ∈ cov ∧ c ∈ cov ∧
        a ∉ R.image opair ∧ b ∉ R.image opair ∧ c ∉ R.image opair ∧
        Disjoint a b ∧ Disjoint a c ∧ Disjoint b c := by
  intro R hR hcard
  rw [bk_nu] at hcard
  intro hex
  rcases hex with ⟨a, b, c, ha, hb, hc, hna, hnb, hnc, hab, hac, hbc⟩
  simp only [cov, mem_image, mem_univ, true_and] at ha hb hc
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, rfl⟩ := hc
  have hsub : ∀ x ∈ R, x.val ∈ (List.range 27).filter fun t =>
      (pc t != pc i.val) && (pc t != pc j.val) && (pc t != pc k.val) := by
    intro x hx
    have hxr : x.val ∈ List.range 27 := List.mem_range.mpr x.isLt
    simp only [List.mem_filter, hxr, true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro he; exact hna (mem_image.mpr ⟨x, hx, (pc_eq_iff x i).mp he⟩)
    · intro he; exact hnb (mem_image.mpr ⟨x, hx, (pc_eq_iff x j).mp he⟩)
    · intro he; exact hnc (mem_image.mpr ⟨x, hx, (pc_eq_iff x k).mp he⟩)
  obtain ⟨d, -, hd⟩ := three_uncovered_bound (pc i.val) (pc_mem_covL i) (pc j.val) (pc_mem_covL j)
    (pc k.val) (pc_mem_covL k) ((pc_disj_iff i j).mpr hab) ((pc_disj_iff i k).mpr hac)
    ((pc_disj_iff j k).mpr hbc)
  have hle := feasible_card_le_of_colChk (fun _ hx => List.mem_of_mem_filter hx) hd R hsub hR
  omega

/-- **BK (§6.1) refutation.** With `ν = 9` (so `k = |cov| − ν = 12 − 9 = 3`) and `β = 2 < 3 = k`,
the master matching LP still attains value `19/2 > 9 = ν` at the feasible `witness` (all defining
inequalities hold): nonnegativity, per-pair capacity, per-host degree, and the odd-set
inequalities. Hence `μ*_mat − ν ≥ 1/2 > 0`, refuting `β < k ⇒ gap = 0`. -/
theorem bk_false :
    (∀ i, 0 ≤ witness i) ∧
    (∀ e : Finset (Fin 6), (∑ i ∈ univ.filter (fun i => opair i = e), witness i) ≤ 1) ∧
    (∀ (j : Fin 8) (a : Fin 6),
        (∑ i ∈ univ.filter (fun i => ohost i = j ∧ a ∈ opair i), witness i) ≤ 1) ∧
    (∀ (j : Fin 8) (S : Finset (Fin 6)), S.card = 3 →
        (∑ i ∈ univ.filter (fun i => ohost i = j ∧ opair i ⊆ S), witness i) ≤ 1) ∧
    lpValue witness = 19 / 2 ∧ nu = 9 := by
  exact ⟨bk_witness_nonneg, bk_witness_pair_cap, bk_witness_degree, bk_witness_oddset,
         bk_witness_value, bk_nu⟩

end BK
end PaperV
