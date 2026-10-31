/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper IV — §4.2, Proposition 4.3 (pure profile). Ledger node L-7.

If all `m` hosts share palette `Fin s` (s ≥ 2), then ν = μ*_mat = min(m·⌊s/2⌋, C(s,2)).

Split into small, independent lemmas (so each is a light Aristotle job, not a monolith):
  nu_le_host  : ν ≤ m·⌊s/2⌋           (per-host degree bound)
  nu_le_pair  : ν ≤ C(s,2)            (global pair capacity)
  nu_ge_min   : min(m·⌊s/2⌋, C(s,2)) ≤ ν   (χ'(K_s) factor matchings; the construction)
  prop43_nu   : ν = min(...)          (assembles the three)
  muMat_ge    : (min ... : ℝ) ≤ μ*_mat   (integral optimum embeds as a 0/1 LP point)
  muMat_le    : μ*_mat ≤ (min ... : ℝ)   (LP defining inequalities)
  prop43_muMat: μ*_mat = min(...)     (so ν = μ*_mat)

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpRw

import Mathlib.Tactic.Choose

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import Mathlib.Data.Nat.Cast.Order.Field

@[expose] public section
open Finset

namespace PaperV
namespace PureProfile

variable (m s : ℕ)

/-- Objects: a host `Fin m` and a 2-element pair from the common palette `Fin s`. -/
abbrev Obj (m s : ℕ) := Fin m × {e : Finset (Fin s) // e.card = 2}

/-- Pairs at a common host are vertex-disjoint, and each global pair is used at most once. -/
def Feasible (R : Finset (Obj m s)) : Prop :=
  (∀ x ∈ R, ∀ y ∈ R, x ≠ y → x.1 = y.1 → (x.2.1 ∩ y.2.1) = ∅) ∧
  (∀ x ∈ R, ∀ y ∈ R, x.2.1 = y.2.1 → x.1 = y.1)

open Classical in
noncomputable instance : DecidablePred (Feasible m s) := Classical.decPred _

/-- The integral packing number `ν`. -/
noncomputable def nu : ℕ := (univ.filter (Feasible m s)).sup Finset.card

/-- Master-LP feasibility of a ℚ-weighting: nonneg; per-host degree ≤ 1; per-host odd-set
`∑_{e ⊆ S} x ≤ (|S|−1)/2` (odd `|S| ≥ 3`); global pair capacity ≤ 1. -/
def MasterFeasible (x : Obj m s → ℝ) : Prop :=
  (∀ o, 0 ≤ x o) ∧
  (∀ (j : Fin m) (a : Fin s), (∑ o ∈ univ.filter (fun o => o.1 = j ∧ a ∈ o.2.1), x o) ≤ 1) ∧
  (∀ (j : Fin m) (S : Finset (Fin s)), Odd S.card → 3 ≤ S.card →
      (∑ o ∈ univ.filter (fun o => o.1 = j ∧ o.2.1 ⊆ S), x o) ≤ (S.card - 1 : ℝ) / 2) ∧
  (∀ e : {e : Finset (Fin s) // e.card = 2},
      (∑ o ∈ univ.filter (fun o => o.2 = e), x o) ≤ 1)

/-- The master matching-LP optimum `μ*_mat` (over `ℝ`; `ℚ` has no `sSup`). -/
noncomputable def muMat : ℝ :=
  sSup { v : ℝ | ∃ x : Obj m s → ℝ, MasterFeasible m s x ∧ v = ∑ o, x o }

-- ν upper bounds ---------------------------------------------------------------

/-- The number of 2-element subsets of `Fin s` is `C(s,2)`. -/
theorem card_two_subsets : Fintype.card {e : Finset (Fin s) // e.card = 2} = s.choose 2 := by
  rw [Fintype.card_subtype]
  have : (univ.filter (fun e : Finset (Fin s) => e.card = 2)) = powersetCard 2 univ := by
    ext e; simp [Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard]; simp

/-- Per-host degree bound: `ν ≤ m·⌊s/2⌋`. -/
theorem nu_le_host : nu m s ≤ m * (s / 2) := by
  apply Finset.sup_le
  intro R hR
  rw [mem_filter] at hR
  obtain ⟨-, hmatch, -⟩ := hR
  have hfib : R.card = ∑ j : Fin m, (R.filter (fun o => o.1 = j)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun o : Obj m s => o.1)
      (t := (univ : Finset (Fin m))) (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  rw [hfib]
  have hbound : ∀ j : Fin m, (R.filter (fun o : Obj m s => o.1 = j)).card ≤ s / 2 := by
    intro j
    set F := R.filter (fun o : Obj m s => o.1 = j) with hF
    have hdisj : (F : Set (Obj m s)).PairwiseDisjoint (fun o => o.2.1) := by
      intro x hx y hy hxy
      simp only [hF, coe_filter, Set.mem_setOf_eq] at hx hy
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hmatch x hx.1 y hy.1 hxy (hx.2.trans hy.2.symm)
    have hcard : (F.biUnion (fun o => o.2.1)).card = 2 * F.card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun o _ => o.2.2),
        Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hle : (F.biUnion (fun o => o.2.1)).card ≤ s := by
      calc (F.biUnion (fun o => o.2.1)).card
            ≤ (univ : Finset (Fin s)).card := Finset.card_le_card (subset_univ _)
        _ = s := by simp
    rw [hcard] at hle; omega
  calc ∑ j : Fin m, (R.filter (fun o => o.1 = j)).card
      ≤ ∑ _j : Fin m, (s / 2) := Finset.sum_le_sum (fun j _ => hbound j)
    _ = m * (s / 2) := by rw [Finset.sum_const, smul_eq_mul]; simp

/-- Global pair-capacity bound: `ν ≤ C(s,2)`. -/
theorem nu_le_pair : nu m s ≤ s.choose 2 := by
  apply Finset.sup_le
  intro R hR
  rw [mem_filter] at hR
  obtain ⟨-, -, huniq⟩ := hR
  have hinj : Set.InjOn (fun o : Obj m s => o.2) R := by
    intro x hx y hy hxy
    have hxy' : x.2 = y.2 := hxy
    have h1 : x.2.1 = y.2.1 := by rw [hxy']
    have h2 : x.1 = y.1 := huniq x hx y hy h1
    exact Prod.ext h2 hxy'
  calc R.card = (R.image (fun o : Obj m s => o.2)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (univ : Finset {e : Finset (Fin s) // e.card = 2}).card :=
          Finset.card_le_card (Finset.subset_univ _)
    _ = s.choose 2 := by rw [Finset.card_univ, card_two_subsets]

-- ν lower bound (construction) -------------------------------------------------

/-- Assembly: any family of `k ≤ m` colour classes that are matchings (`hmatch`) whose edges
determine their colour (`hcolour`) yields a feasible packing of size `k·⌊s/2⌋`, hence a lower
bound on `ν`. -/
theorem factors_to_nu (k : ℕ) (hk : k ≤ m)
    (edge : Fin k → Fin (s/2) → {e : Finset (Fin s) // e.card = 2})
    (hmatch : ∀ (i : Fin k) (t t' : Fin (s/2)), t ≠ t' → Disjoint (edge i t).1 (edge i t').1)
    (hcolour : ∀ (i : Fin k) (t : Fin (s/2)) (i' : Fin k) (t' : Fin (s/2)),
        edge i t = edge i' t' → i = i') :
    k * (s / 2) ≤ nu m s := by
  classical
  set h : Fin k → Fin m := Fin.castLE hk with hh
  set φ : Fin k × Fin (s/2) → Obj m s := fun p => (h p.1, edge p.1 p.2) with hφ
  have hti : ∀ (i : Fin k) (t t' : Fin (s/2)), edge i t = edge i t' → t = t' := by
    intro i t t' he
    by_contra hne
    have := hmatch i t t' hne
    rw [he] at this
    have hcard := (edge i t').2
    rw [Finset.disjoint_self_iff_empty] at this
    rw [this] at hcard; simp at hcard
  have hinj : Function.Injective φ := by
    rintro ⟨i, t⟩ ⟨i', t'⟩ heq
    simp only [hφ, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hii : i = i' := Fin.castLE_injective hk h1
    subst hii
    have : t = t' := hti i t t' h2
    subst this; rfl
  set R : Finset (Obj m s) := (univ : Finset (Fin k × Fin (s/2))).image φ with hR
  have hcardR : R.card = k * (s/2) := by
    rw [hR, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  have hfeas : Feasible m s R := by
    constructor
    · rintro x hx y hy hxy hxy1
      simp only [hR, mem_image, mem_univ, true_and] at hx hy
      obtain ⟨⟨i, t⟩, rfl⟩ := hx
      obtain ⟨⟨i', t'⟩, rfl⟩ := hy
      simp only [hφ] at hxy1 ⊢
      have hii : i = i' := Fin.castLE_injective hk hxy1
      subst hii
      have htt : t ≠ t' := by rintro rfl; exact hxy rfl
      have := hmatch i t t' htt
      rwa [Finset.disjoint_iff_inter_eq_empty] at this
    · rintro x hx y hy hxy1
      simp only [hR, mem_image, mem_univ, true_and] at hx hy
      obtain ⟨⟨i, t⟩, rfl⟩ := hx
      obtain ⟨⟨i', t'⟩, rfl⟩ := hy
      simp only [hφ] at hxy1 ⊢
      have hedge : edge i t = edge i' t' := Subtype.ext hxy1
      have := hcolour i t i' t' hedge
      subst this; rfl
  calc k * (s/2) = R.card := hcardR.symm
    _ ≤ nu m s := Finset.le_sup (f := Finset.card)
        (by rw [mem_filter]; exact ⟨mem_univ _, hfeas⟩)

/-- Near-1-factorization of `K_s` for odd `s` (rotation on `ZMod s`): `s` colour classes,
each a matching of `⌊s/2⌋` vertex-disjoint edges, the colour of an edge `{a,b}` being `(a+b)/2`. -/
theorem exists_factorization_odd (hodd : Odd s) (hs : 2 ≤ s) :
    ∃ (chi : ℕ) (edge : Fin chi → Fin (s/2) → {e : Finset (Fin s) // e.card = 2}),
      chi * (s/2) = s.choose 2 ∧
      (∀ (i : Fin chi) (t t' : Fin (s/2)), t ≠ t' → Disjoint (edge i t).1 (edge i t').1) ∧
      (∀ (i : Fin chi) (t : Fin (s/2)) (i' : Fin chi) (t' : Fin (s/2)),
          edge i t = edge i' t' → i = i') := by
  haveI : NeZero s := ⟨by omega⟩
  set r := s / 2 with hr
  have hs2r : s = 2 * r + 1 := by rcases hodd with ⟨k, hk⟩; omega
  set q : ZMod s → Fin s := ⇑(ZMod.finEquiv s).symm with hq
  have hqinj : Function.Injective q := (ZMod.finEquiv s).symm.injective
  set e2z : Fin s → ZMod s := ⇑(ZMod.finEquiv s) with he2z
  have he2zinj : Function.Injective e2z := (ZMod.finEquiv s).injective
  have hqe2z : ∀ u : ZMod s, e2z (q u) = u := fun u => (ZMod.finEquiv s).apply_symm_apply u
  set a : Fin r → ZMod s := fun t => (((t : ℕ) + 1 : ℕ) : ZMod s) with ha
  have ha_lt : ∀ t : Fin r, (t : ℕ) + 1 < s := fun t => by have := t.2; omega
  have hnz : ∀ k : ℕ, 0 < k → k < s → ((k : ℕ) : ZMod s) ≠ 0 := by
    intro k hk0 hks h
    have h1 := (CharP.cast_eq_zero_iff (ZMod s) s k).mp h
    have := Nat.le_of_dvd hk0 h1; omega
  have hsum : ∀ t t' : Fin r, a t + a t' ≠ 0 := by
    intro t t'
    have : a t + a t' = (((t:ℕ)+1 + ((t':ℕ)+1) : ℕ) : ZMod s) := by rw [ha]; push_cast; ring
    rw [this]; exact hnz _ (by omega) (by have := t.2; have := t'.2; omega)
  have hval : ∀ t t' : Fin r, a t = a t' → t = t' := by
    intro t t' h
    rw [ha, ZMod.natCast_eq_natCast_iff] at h
    have := Nat.ModEq.eq_of_lt_of_lt h (ha_lt t) (ha_lt t')
    exact Fin.ext (by omega)
  have hne : ∀ (ci : ZMod s) (t : Fin r), q (ci + a t) ≠ q (ci - a t) := by
    intro ci t hcon
    have h := hqinj hcon
    rw [sub_eq_add_neg, add_right_inj] at h
    have h2 : a t + a t = 0 := by nth_rewrite 2 [h]; ring
    exact hsum t t h2
  refine ⟨s, fun i t => ⟨{q (e2z i + a t), q (e2z i - a t)}, Finset.card_pair (hne _ _)⟩, ?_, ?_, ?_⟩
  · rw [Nat.choose_two_right]
    have hmul : s * (s - 1) = 2 * (s * r) := by rw [hs2r]; simp only [Nat.add_sub_cancel]; ring
    rw [hmul, Nat.mul_div_cancel_left _ (by norm_num)]
  · intro i t t' htt
    simp only []
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;>
      have hz := hqinj hcon
    · exact htt (hval t t' (add_left_cancel hz))
    · rw [sub_eq_add_neg] at hz
      exact hsum t t' (add_eq_zero_iff_eq_neg.mpr (add_left_cancel hz))
    · rw [sub_eq_add_neg] at hz
      have := add_left_cancel hz
      exact hsum t t' (by linear_combination -this)
    · exact htt (hval t t' (sub_right_inj.mp hz))
  · intro i t i' t' he
    have hset : ({q (e2z i + a t), q (e2z i - a t)} : Finset (Fin s))
        = {q (e2z i' + a t'), q (e2z i' - a t')} := congrArg Subtype.val he
    have hsum_eq : (∑ x ∈ ({q (e2z i + a t), q (e2z i - a t)} : Finset (Fin s)), e2z x)
        = ∑ x ∈ ({q (e2z i' + a t'), q (e2z i' - a t')} : Finset (Fin s)), e2z x := by rw [hset]
    rw [Finset.sum_pair (hne _ _), Finset.sum_pair (hne _ _)] at hsum_eq
    simp only [hqe2z] at hsum_eq
    have h2 : (2 : ZMod s) * e2z i = 2 * e2z i' := by linear_combination hsum_eq
    have h2u : IsUnit (2 : ZMod s) := by
      have : IsUnit ((2:ℕ) : ZMod s) :=
        (ZMod.isUnit_iff_coprime 2 s).mpr (by simpa [Nat.coprime_two_left] using hodd)
      simpa using this
    exact he2zinj (h2u.mul_left_cancel h2)

/-- 1-factorization of `K_s` for even `s` (circle method with `∞ = s-1` and rotation on
`ZMod (s-1)`): `s-1` colour classes, each a perfect matching of `s/2` edges. -/
theorem exists_factorization_even (hev : Even s) (hs : 2 ≤ s) :
    ∃ (chi : ℕ) (edge : Fin chi → Fin (s/2) → {e : Finset (Fin s) // e.card = 2}),
      chi * (s/2) = s.choose 2 ∧
      (∀ (i : Fin chi) (t t' : Fin (s/2)), t ≠ t' → Disjoint (edge i t).1 (edge i t').1) ∧
      (∀ (i : Fin chi) (t : Fin (s/2)) (i' : Fin chi) (t' : Fin (s/2)),
          edge i t = edge i' t' → i = i') := by
  set n := s - 1 with hn
  haveI : NeZero n := ⟨by omega⟩
  set r := s / 2 with hr
  have hsr : s = 2 * r := by rcases hev with ⟨k,hk⟩; omega
  have hrpos : 1 ≤ r := by omega
  have hrn : r ≤ n := by omega
  have hns1 : s = n + 1 := by omega
  have h2r : n + 1 = 2 * r := by omega
  set p : ZMod n → Fin s := fun u => Fin.castLE (by omega) ((ZMod.finEquiv n).symm u) with hp
  have hp_lt : ∀ u, (p u).val < n := by intro u; simp [hp, Fin.castLE]
  have hpinj : Function.Injective p :=
    (Fin.castLE_injective (show n ≤ s by omega)).comp (ZMod.finEquiv n).symm.injective
  set inf : Fin s := ⟨n, by omega⟩ with hinf
  have hp_ne_inf : ∀ u, p u ≠ inf := by
    intro u h; have := hp_lt u; rw [h] at this; simp [hinf] at this
  set ci : Fin n → ZMod n := ⇑(ZMod.finEquiv n) with hci
  have hciinj : Function.Injective ci := (ZMod.finEquiv n).injective
  set b : Fin r → ZMod n := fun t => ((t : ℕ) : ZMod n) with hb
  have hnz : ∀ k : ℕ, 0 < k → k < n → ((k : ℕ) : ZMod n) ≠ 0 := by
    intro k hk0 hks h
    have h1 := (CharP.cast_eq_zero_iff (ZMod n) n k).mp h
    have := Nat.le_of_dvd hk0 h1; omega
  have h2u : IsUnit (2 : ZMod n) := by
    have hodd : Odd n := ⟨r-1, by omega⟩
    have : IsUnit ((2:ℕ) : ZMod n) :=
      (ZMod.isUnit_iff_coprime 2 n).mpr (by simpa [Nat.coprime_two_left] using hodd)
    simpa using this
  have hb_ne : ∀ t : Fin r, (t:ℕ) ≠ 0 → b t ≠ 0 := by
    intro t ht; rw [hb]; exact hnz _ (by omega) (by have := t.2; omega)
  have hbsum : ∀ t t' : Fin r, (t:ℕ) ≠ 0 → (t':ℕ) ≠ 0 → b t + b t' ≠ 0 := by
    intro t t' ht ht'
    have : b t + b t' = (((t:ℕ) + (t':ℕ) : ℕ) : ZMod n) := by rw [hb]; push_cast; ring
    rw [this]; exact hnz _ (by omega) (by have := t.2; have := t'.2; omega)
  have hval : ∀ t t' : Fin r, b t = b t' → t = t' := by
    intro t t' h
    rw [hb, ZMod.natCast_eq_natCast_iff] at h
    have := Nat.ModEq.eq_of_lt_of_lt h (by have := t.2; omega) (by have := t'.2; omega)
    exact Fin.ext this
  have hne_int : ∀ (c : ZMod n) (t : Fin r), (t:ℕ) ≠ 0 → p (c + b t) ≠ p (c - b t) := by
    intro c t ht hcon
    have h := hpinj hcon
    rw [sub_eq_add_neg, add_right_inj] at h
    have h2 : b t + b t = 0 := by nth_rewrite 2 [h]; ring
    exact hbsum t t ht ht h2
  set pinv : Fin s → ZMod n := fun x => ci ⟨x.val % n, Nat.mod_lt _ (by omega)⟩ with hpinv
  have hpinv_p : ∀ u, pinv (p u) = u := by
    intro u
    simp only [hpinv, hp, hci, Fin.castLE]
    conv_rhs => rw [← (ZMod.finEquiv n).apply_symm_apply u]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt ((ZMod.finEquiv n).symm u).2)
  refine ⟨n, fun i t => if h : (t:ℕ) = 0 then ⟨{inf, p (ci i)}, Finset.card_pair (hp_ne_inf _).symm⟩
      else ⟨{p (ci i + b t), p (ci i - b t)}, Finset.card_pair (hne_int _ _ h)⟩, ?_, ?_, ?_⟩
  · rw [Nat.choose_two_right]
    have h1 : s * (s-1) = 2 * (n * r) := by rw [hns1]; simp only [Nat.add_sub_cancel]; rw [h2r]; ring
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num)]
  · intro i t t' htt
    by_cases ht : (t:ℕ) = 0 <;> by_cases ht' : (t':ℕ) = 0
    · exact absurd (Fin.ext (ht.trans ht'.symm)) htt
    · simp only [dif_pos ht, dif_neg ht']
      rw [Finset.disjoint_iff_ne]; intro x hx y hy hcon
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst hx <;> subst hy
      · exact hp_ne_inf _ hcon.symm
      · exact hp_ne_inf _ hcon.symm
      · exact hb_ne t' ht' (left_eq_add.mp (hpinj hcon))
      · have := hpinj hcon; rw [eq_comm, sub_eq_self] at this; exact hb_ne t' ht' this
    · simp only [dif_neg ht, dif_pos ht']
      rw [Finset.disjoint_iff_ne]; intro x hx y hy hcon
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst hx <;> subst hy
      · exact hp_ne_inf _ hcon
      · exact hb_ne t ht (left_eq_add.mp (hpinj hcon).symm)
      · exact hp_ne_inf _ hcon
      · have := hpinj hcon; rw [sub_eq_self] at this; exact hb_ne t ht this
    · simp only [dif_neg ht, dif_neg ht']
      rw [Finset.disjoint_iff_ne]; intro x hx y hy hcon
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst hx <;> subst hy <;> have hz := hpinj hcon
      · exact htt (hval t t' (add_left_cancel hz))
      · rw [sub_eq_add_neg] at hz; exact hbsum t t' ht ht' (add_eq_zero_iff_eq_neg.mpr (add_left_cancel hz))
      · rw [sub_eq_add_neg] at hz; have := add_left_cancel hz
        exact hbsum t t' ht ht' (by linear_combination -this)
      · exact htt (hval t t' (sub_right_inj.mp hz))
  · intro i t i' t' he
    by_cases ht : (t:ℕ) = 0 <;> by_cases ht' : (t':ℕ) = 0
    · simp only [dif_pos ht, dif_pos ht'] at he
      have hset : ({inf, p (ci i)} : Finset (Fin s)) = {inf, p (ci i')} := congrArg Subtype.val he
      have hmem : p (ci i) ∈ ({inf, p (ci i')} : Finset (Fin s)) := by rw [← hset]; simp
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h|h
      · exact absurd h (hp_ne_inf _)
      · exact hciinj (hpinj h)
    · exfalso
      simp only [dif_pos ht, dif_neg ht'] at he
      have hset : ({inf, p (ci i)} : Finset (Fin s)) = {p (ci i'+b t'), p (ci i'-b t')} :=
        congrArg Subtype.val he
      have hin : inf ∈ ({p (ci i'+b t'), p (ci i'-b t')} : Finset (Fin s)) := by rw [← hset]; simp
      simp only [mem_insert, mem_singleton] at hin
      rcases hin with h|h <;> exact hp_ne_inf _ h.symm
    · exfalso
      simp only [dif_neg ht, dif_pos ht'] at he
      have hset : ({p (ci i+b t), p (ci i-b t)} : Finset (Fin s)) = {inf, p (ci i')} :=
        congrArg Subtype.val he
      have hin : inf ∈ ({p (ci i+b t), p (ci i-b t)} : Finset (Fin s)) := by rw [hset]; simp
      simp only [mem_insert, mem_singleton] at hin
      rcases hin with h|h <;> exact hp_ne_inf _ h.symm
    · simp only [dif_neg ht, dif_neg ht'] at he
      have hset : ({p (ci i+b t), p (ci i-b t)} : Finset (Fin s))
          = {p (ci i'+b t'), p (ci i'-b t')} := congrArg Subtype.val he
      have hsum_eq : (∑ x ∈ ({p (ci i+b t), p (ci i-b t)} : Finset (Fin s)), pinv x)
          = ∑ x ∈ ({p (ci i'+b t'), p (ci i'-b t')} : Finset (Fin s)), pinv x := by rw [hset]
      rw [Finset.sum_pair (hne_int _ _ ht), Finset.sum_pair (hne_int _ _ ht')] at hsum_eq
      simp only [hpinv_p] at hsum_eq
      have h2 : (2:ZMod n) * ci i = 2 * ci i' := by linear_combination hsum_eq
      exact hciinj (h2u.mul_left_cancel h2)

/-- Combined factorization existence for `s ≥ 2` (either parity). -/
theorem exists_factorization (hs : 2 ≤ s) :
    ∃ (chi : ℕ) (edge : Fin chi → Fin (s/2) → {e : Finset (Fin s) // e.card = 2}),
      chi * (s/2) = s.choose 2 ∧
      (∀ (i : Fin chi) (t t' : Fin (s/2)), t ≠ t' → Disjoint (edge i t).1 (edge i t').1) ∧
      (∀ (i : Fin chi) (t : Fin (s/2)) (i' : Fin chi) (t' : Fin (s/2)),
          edge i t = edge i' t' → i = i') := by
  rcases Nat.even_or_odd s with he | ho
  · exact exists_factorization_even s he hs
  · exact exists_factorization_odd s ho hs

/-- Construction: `χ'(K_s)` factor matchings attain `min(m·⌊s/2⌋, C(s,2)) ≤ ν`. -/
theorem nu_ge_min : min (m * (s / 2)) (s.choose 2) ≤ nu m s := by
  rcases lt_or_ge s 2 with hs | hs
  · have h0 : s.choose 2 = 0 := Nat.choose_eq_zero_of_lt hs
    have h1 : s / 2 = 0 := by omega
    simp [h0, h1]
  · obtain ⟨chi, edge, hC, hmatch, hcolour⟩ := exists_factorization s hs
    set k := min m chi with hk
    have hkm : k ≤ m := min_le_left m chi
    have hkchi : k ≤ chi := min_le_right m chi
    set edge' : Fin k → Fin (s/2) → {e : Finset (Fin s) // e.card = 2} :=
      fun i t => edge (Fin.castLE hkchi i) t with he'
    have hmatch' : ∀ (i : Fin k) (t t' : Fin (s/2)), t ≠ t' →
        Disjoint (edge' i t).1 (edge' i t').1 := fun i t t' h => hmatch _ t t' h
    have hcolour' : ∀ (i : Fin k) (t : Fin (s/2)) (i' : Fin k) (t' : Fin (s/2)),
        edge' i t = edge' i' t' → i = i' := by
      intro i t i' t' he
      exact Fin.castLE_injective hkchi (hcolour _ t _ t' he)
    have hle : k * (s/2) ≤ nu m s := factors_to_nu m s k hkm edge' hmatch' hcolour'
    have hmin : min (m * (s / 2)) (s.choose 2) = k * (s/2) := by
      rw [← hC]
      rcases le_total m chi with hmc | hmc
      · rw [min_eq_left (Nat.mul_le_mul_right _ hmc), hk, min_eq_left hmc]
      · rw [min_eq_right (Nat.mul_le_mul_right _ hmc), hk, min_eq_right hmc]
    rw [hmin]; exact hle

/-- **Proposition 4.3, integral half.** `ν = min(m·⌊s/2⌋, C(s,2))`. -/
theorem prop43_nu : nu m s = min (m * (s / 2)) (s.choose 2) := by
  exact le_antisymm (le_min (nu_le_host m s) (nu_le_pair m s)) (nu_ge_min m s)

-- μ*_mat = ν -------------------------------------------------------------------

/-
NOTE (statement correction).  As originally written, the goal
    `(min (m * (s / 2)) (s.choose 2) : ℝ) ≤ muMat m s`
is elaborated by Lean with **real** division `(↑s / 2)` (not the intended floor `⌊s/2⌋`):
the right-hand side is `min (↑m * (↑s / 2)) ↑(s.choose 2)`.  This statement is FALSE.
Counterexample `m = 1, s = 3`: the RHS is `min (1 * 3/2) 3 = 3/2`, but `muMat 1 3 = 1`
(the odd-set inequality for `S = univ` forces `∑ x ≤ (3-1)/2 = 1`, cf. `muMat_le_nat`).
The mathematically intended bound uses the natural-number `min` (with floor `⌊s/2⌋`) cast to `ℝ`;
the corrected, provable version `muMat_ge` is stated and proved below (after the LP helpers,
since it depends on them), and `prop43_muMat` is corrected accordingly.  (The original
real-division statement `(min (m * (s / 2)) (s.choose 2) : ℝ) ≤ muMat m s` was FALSE and has
been removed.)
-/

-- LP defining-inequality helpers ----------------------------------------------

/-- Double counting at a host: summing the per-vertex degree contributions counts every
object twice (each edge has two endpoints). -/
theorem host_degree_double (x : Obj m s → ℝ) (j : Fin m) :
    ∑ a : Fin s, (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o)
      = 2 * (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j), x o) := by
  have step : ∀ a : Fin s, (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o)
      = ∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j), (if a ∈ o.2.1 then x o else 0) := by
    intro a
    rw [show (univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1))
          = (univ.filter (fun o : Obj m s => o.1 = j)).filter (fun o => a ∈ o.2.1) from by
        rw [Finset.filter_filter], Finset.sum_filter]
  simp_rw [step]
  rw [Finset.sum_comm]
  have : ∀ o : Obj m s, (∑ a : Fin s, (if a ∈ o.2.1 then x o else 0)) = 2 * x o := by
    intro o
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, o.2.2]; ring
  rw [Finset.sum_congr rfl (fun o _ => this o), Finset.mul_sum]

/-- Per-host fractional matching bound `∑_{o.1=j} x o ≤ ⌊s/2⌋` (Edmonds: the degree and
odd-set inequalities bound the fractional matching value of `K_s` by `⌊s/2⌋`). -/
theorem hostsum_le (x : Obj m s → ℝ) (hx : MasterFeasible m s x) (j : Fin m) :
    (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j), x o) ≤ (↑(s / 2) : ℝ) := by
  obtain ⟨hnn, hdeg, hodd, -⟩ := hx
  by_cases hs : 2 ≤ s
  · rcases Nat.even_or_odd s with he | ho
    · have hsum : ∑ a : Fin s,
          (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o) ≤ (s : ℝ) := by
        calc ∑ a : Fin s, (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1), x o)
            ≤ ∑ _a : Fin s, (1:ℝ) := Finset.sum_le_sum (fun a _ => hdeg j a)
          _ = s := by simp
      rw [host_degree_double] at hsum
      obtain ⟨k, hk⟩ := he
      have hcast : (↑(s/2) : ℝ) = (s:ℝ)/2 := by
        have : s / 2 = k := by omega
        rw [this, hk]; push_cast; ring
      rw [hcast]; linarith
    · have hs3 : 3 ≤ s := by rcases ho with ⟨k, hk⟩; omega
      have hcard : (univ : Finset (Fin s)).card = s := by simp
      have := hodd j univ (by rw [hcard]; exact ho) (by rw [hcard]; exact hs3)
      rw [hcard] at this
      have heq : (univ.filter (fun o : Obj m s => o.1 = j ∧ o.2.1 ⊆ univ))
          = univ.filter (fun o : Obj m s => o.1 = j) := by
        apply Finset.filter_congr; intro o _; simp [Finset.subset_univ]
      rw [heq] at this
      have hcast : (↑(s/2) : ℝ) = ((s:ℝ) - 1)/2 := by
        obtain ⟨k, hk⟩ := ho
        have : s / 2 = k := by omega
        rw [this, hk]; push_cast; ring
      rw [hcast]; exact this
  · push_neg at hs
    have hsub : IsEmpty {e : Finset (Fin s) // e.card = 2} := by
      constructor; rintro ⟨e, he⟩
      have : e.card ≤ s := by
        calc e.card ≤ (univ : Finset (Fin s)).card := Finset.card_le_univ e
          _ = s := by simp
      omega
    haveI : IsEmpty (Obj m s) := ⟨fun o => hsub.false o.2⟩
    rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
    positivity

/-- Summing the per-host bounds: `∑ x ≤ m·⌊s/2⌋`. -/
theorem sum_le_host (x : Obj m s → ℝ) (hx : MasterFeasible m s x) :
    (∑ o, x o) ≤ (↑(m * (s / 2)) : ℝ) := by
  rw [← Finset.sum_fiberwise univ (fun o : Obj m s => o.1) x]
  calc ∑ j : Fin m, (∑ o ∈ univ.filter (fun o : Obj m s => o.1 = j), x o)
      ≤ ∑ _j : Fin m, (↑(s/2) : ℝ) := Finset.sum_le_sum (fun j _ => hostsum_le m s x hx j)
    _ = (↑(m * (s/2)) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

/-- Summing the global pair capacities: `∑ x ≤ C(s,2)`. -/
theorem sum_le_pair (x : Obj m s → ℝ) (hx : MasterFeasible m s x) :
    (∑ o, x o) ≤ (↑(s.choose 2) : ℝ) := by
  obtain ⟨-, -, -, hpair⟩ := hx
  rw [← Finset.sum_fiberwise univ (fun o : Obj m s => o.2) x]
  calc ∑ e : {e : Finset (Fin s) // e.card = 2},
          (∑ o ∈ univ.filter (fun o : Obj m s => o.2 = e), x o)
      ≤ ∑ _e : {e : Finset (Fin s) // e.card = 2}, (1:ℝ) := Finset.sum_le_sum (fun e _ => hpair e)
    _ = (↑(s.choose 2) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, card_two_subsets]; simp

/-- The LP value is at most `min(m·⌊s/2⌋, C(s,2))` (defining inequalities). -/
theorem muMat_le : muMat m s ≤ (min (m * (s / 2)) (s.choose 2) : ℝ) := by
  apply csSup_le
  · exact ⟨0, fun _ => (0:ℝ), ⟨fun _ => le_refl 0, fun j a => by simp,
      fun j S _ h3 => by
        simp only [Finset.sum_const_zero]
        nlinarith [show (3:ℝ) ≤ S.card from by exact_mod_cast h3],
      fun e => by simp⟩, by simp⟩
  · rintro v ⟨x, hx, rfl⟩
    apply le_min
    · calc (∑ o, x o) ≤ (↑(m * (s / 2)) : ℝ) := sum_le_host m s x hx
        _ ≤ (m:ℝ) * ((s:ℝ)/2) := by
              have h : ((s/2 : ℕ) : ℝ) ≤ (s:ℝ)/2 := Nat.cast_div_le (α := ℝ)
              push_cast; nlinarith [h, Nat.cast_nonneg (α := ℝ) m]
    · exact_mod_cast sum_le_pair m s x hx

-- Corrected `muMat_ge` / `prop43_muMat` (natural-number `min`, see NOTE above) ----

/-- The feasible set of the master LP is bounded above (by `C(s,2)`), so its `sSup` is meaningful. -/
theorem muMat_bddAbove :
    BddAbove { v : ℝ | ∃ x : Obj m s → ℝ, MasterFeasible m s x ∧ v = ∑ o, x o } := by
  refine ⟨(↑(s.choose 2) : ℝ), ?_⟩
  rintro v ⟨x, hx, rfl⟩
  exact sum_le_pair m s x hx

/-- The 0/1 indicator of a feasible packing is a master-LP feasible point. -/
theorem indicator_feasible (R : Finset (Obj m s)) (hR : Feasible m s R) :
    MasterFeasible m s (fun o => if o ∈ R then (1:ℝ) else 0) := by
  obtain ⟨hmatch, huniq⟩ := hR
  classical
  refine ⟨fun o => by dsimp only; split <;> norm_num, ?_, ?_, ?_⟩
  · intro j a
    rw [Finset.sum_boole]
    have hle : ((univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1)).filter (· ∈ R)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      by_contra hne
      have hinter := hmatch x hx.2 y hy.2 hne (hx.1.1.trans hy.1.1.symm)
      have : a ∈ x.2.1 ∩ y.2.1 := Finset.mem_inter.mpr ⟨hx.1.2, hy.1.2⟩
      rw [hinter] at this; simp at this
    exact_mod_cast hle
  · intro j S hodd h3
    rw [Finset.sum_boole]
    set F := (univ.filter (fun o : Obj m s => o.1 = j ∧ o.2.1 ⊆ S)).filter (· ∈ R) with hF
    have hdisj : (F : Set (Obj m s)).PairwiseDisjoint (fun o => o.2.1) := by
      intro x hx y hy hxy
      simp only [hF, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hmatch x hx.2 y hy.2 hxy (hx.1.1.trans hy.1.1.symm)
    have hsub : F.biUnion (fun o => o.2.1) ⊆ S := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨o, ho, hvo⟩ := hv
      simp only [hF, mem_filter, mem_univ, true_and] at ho
      exact ho.1.2 hvo
    have hcard : 2 * F.card = (F.biUnion (fun o => o.2.1)).card := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun o _ => o.2.2), Finset.sum_const,
        smul_eq_mul, Nat.mul_comm]
    have h2c : 2 * F.card ≤ S.card := by rw [hcard]; exact Finset.card_le_card hsub
    obtain ⟨kk, hkk⟩ := hodd
    have hFk : F.card ≤ kk := by omega
    calc (F.card : ℝ) ≤ (kk:ℝ) := by exact_mod_cast hFk
      _ = (S.card - 1 : ℝ)/2 := by rw [hkk]; push_cast; ring
  · intro e
    rw [Finset.sum_boole]
    have hle : ((univ.filter (fun o : Obj m s => o.2 = e)).filter (· ∈ R)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      have hxe : x.2.1 = y.2.1 := by rw [hx.1, hy.1]
      exact Prod.ext (huniq x hx.2 y hy.2 hxe) (by rw [hx.1, hy.1])
    exact_mod_cast hle

/-- The LP value is at most the natural-number optimum `↑(min(m·⌊s/2⌋, C(s,2)))` (tight bound). -/
theorem muMat_le_nat : muMat m s ≤ (↑(min (m * (s / 2)) (s.choose 2)) : ℝ) := by
  apply csSup_le
  · exact ⟨0, fun _ => (0:ℝ), ⟨fun _ => le_refl 0, fun j a => by simp,
      fun j S _ h3 => by
        simp only [Finset.sum_const_zero]
        nlinarith [show (3:ℝ) ≤ S.card from by exact_mod_cast h3],
      fun e => by simp⟩, by simp⟩
  · rintro v ⟨x, hx, rfl⟩
    rw [Nat.cast_min]
    exact le_min (sum_le_host m s x hx) (sum_le_pair m s x hx)

/-- **The LP value is at least the integral optimum** (embed a max packing as a 0/1 point).
Corrected statement of `muMat_ge`: uses the natural-number `min` (floor `⌊s/2⌋`) cast to `ℝ`. -/
theorem muMat_ge : (↑(min (m * (s / 2)) (s.choose 2)) : ℝ) ≤ muMat m s := by
  rw [← prop43_nu]
  have hne : (univ.filter (Feasible m s)).Nonempty :=
    ⟨∅, by rw [mem_filter]; exact ⟨mem_univ _, ⟨fun x hx => by simp at hx, fun x hx => by simp at hx⟩⟩⟩
  obtain ⟨R, hRmem, hRsup⟩ := Finset.exists_mem_eq_sup (univ.filter (Feasible m s)) hne Finset.card
  rw [mem_filter] at hRmem
  have hFeas : Feasible m s R := hRmem.2
  have hnu : nu m s = R.card := hRsup
  set x : Obj m s → ℝ := fun o => if o ∈ R then (1:ℝ) else 0 with hx
  have hMF : MasterFeasible m s x := indicator_feasible m s R hFeas
  have hsumx : (∑ o, x o) = (R.card : ℝ) := by
    simp only [hx, Finset.sum_boole]
    rw [Finset.filter_univ_mem]
  have hmem : (∑ o, x o) ∈ { v : ℝ | ∃ x : Obj m s → ℝ, MasterFeasible m s x ∧ v = ∑ o, x o } :=
    ⟨x, hMF, rfl⟩
  have hle := le_csSup (muMat_bddAbove m s) hmem
  rw [hsumx] at hle
  rw [hnu]; exact hle

/-- **Proposition 4.3, LP half.** `μ*_mat = ↑(min(m·⌊s/2⌋, C(s,2)))` (hence `ν = μ*_mat`).

NOTE: corrected from the original `muMat m s = (min (m * (s / 2)) (s.choose 2) : ℝ)`, whose RHS
Lean elaborates with real division `↑s / 2` and which is therefore false (see NOTE at `muMat_ge`).
The original line is preserved, commented out:

theorem prop43_muMat : muMat m s = (min (m * (s / 2)) (s.choose 2) : ℝ) := by
  exact le_antisymm (muMat_le m s) (muMat_ge m s)
-/
theorem prop43_muMat : muMat m s = (↑(min (m * (s / 2)) (s.choose 2)) : ℝ) :=
  le_antisymm (muMat_le_nat m s) (muMat_ge m s)

end PureProfile
end PaperV
