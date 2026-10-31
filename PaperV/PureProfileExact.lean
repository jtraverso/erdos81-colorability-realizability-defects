/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Paper V — Exact value of the degree-only LP on pure profiles, and tightness for every odd palette.

`PureProfileGap.lean` proves `μ*_res ≤ min(m·s/2, C(s,2))`. The exact sweep of the small profiles showed
the bound is attained, so this file supplies the missing direction by exhibiting the optimal point:

  * `m ≤ s − 1`: the uniform weighting `x ≡ 1/(s−1)` saturates every host degree and has value `m·s/2`;
  * `s − 1 ≤ m`: the uniform weighting `x ≡ 1/m` saturates every pair capacity and has value `C(s,2)`.

Consequences:

  * `muMatDeg_eq_min` — `μ*_res = min(m·s/2, C(s,2))`, an equality;
  * `nu_eq_frac_muMatDeg_of_odd` — for odd `s` and `m ≤ s − 1`, `ν = ((s−1)/s)·μ*_res` EXACTLY, so the
    factor of Proposition 7.1a is attained for every odd palette, not only at the triangle profile.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.PureProfileSharp

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV.PureProfile

variable (m s : ℕ)

/-! ### Counting -/

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hchoose : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
      have hk1 : k.choose 1 = k := Nat.choose_one_right k
      have : 2 * (k + 1).choose 2 = 2 * k + 2 * k.choose 2 := by rw [hchoose, hk1]; ring
      rw [this, ih]
      cases k with
      | zero => simp
      | succ t => simp [Nat.succ_sub_one]; ring

theorem card_objects : Fintype.card (Obj m s) = m * s.choose 2 := by
  rw [Fintype.card_prod, Fintype.card_fin, card_two_subsets]

/-- Objects carrying a fixed pair are exactly the `m` host copies of it. -/
theorem card_filter_pair (e : {e : Finset (Fin s) // e.card = 2}) :
    (univ.filter (fun o : Obj m s => o.2 = e)).card = m := by
  classical
  have hprod : univ.filter (fun o : Obj m s => o.2 = e)
      = (univ : Finset (Fin m)) ×ˢ ({e} : Finset {e : Finset (Fin s) // e.card = 2}) := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_singleton,
    mul_one]

/-- At a fixed host, the objects through a fixed vertex are at most `s − 1`: the pair is determined
by its other endpoint. -/
theorem card_filter_host_vertex_le (j : Fin m) (a : Fin s) :
    (univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1)).card ≤ s - 1 := by
  classical
  set T : Finset (Finset (Fin s)) :=
    ((univ : Finset (Fin s)).erase a).image (fun b => ({b} : Finset (Fin s))) with hT
  have hTcard : T.card = s - 1 := by
    rw [hT, Finset.card_image_of_injective _ (fun p q h => by simpa using h),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  rw [← hTcard]
  refine Finset.card_le_card_of_injOn (fun o => o.2.1.erase a) ?_ ?_
  · intro o ho
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at ho
    obtain ⟨hoj, hoa⟩ := ho
    have h1 : (o.2.1.erase a).card = 1 := by rw [Finset.card_erase_of_mem hoa, o.2.2]
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
    have hbmem : b ∈ o.2.1.erase a := by rw [hb]; exact Finset.mem_singleton_self b
    have _ := hoj
    show o.2.1.erase a ∈ (T : Set (Finset (Fin s)))
    rw [Finset.mem_coe, hT, hb]
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hbmem, Finset.mem_univ b⟩, rfl⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
    have hxy' : x.2.1.erase a = y.2.1.erase a := hxy
    have hpair : x.2.1 = y.2.1 := by
      rw [← Finset.insert_erase hx.2, ← Finset.insert_erase hy.2, hxy']
    exact Prod.ext (by rw [hx.1, hy.1]) (Subtype.ext hpair)

/-! ### The optimal uniform points -/

/-- Cast form of `2·C(s,2) = s(s−1)`. -/
theorem choose_two_real (hs : 1 ≤ s) : ((s.choose 2 : ℕ) : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
  have h : 2 * s.choose 2 = s * (s - 1) := two_mul_choose_two s
  have hcast : (2 : ℝ) * ((s.choose 2 : ℕ) : ℝ) = ((s : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    push_cast [Nat.cast_sub hs]; ring
  rw [hsub] at hcast
  linarith

/-- The uniform weighting is feasible as soon as it respects the two capacities. -/
theorem masterFeasibleDeg_const {c : ℝ} (hc : 0 ≤ c) (hdeg : c * ((s - 1 : ℕ) : ℝ) ≤ 1)
    (hpair : c * (m : ℝ) ≤ 1) : MasterFeasibleDeg m s (fun _ => c) := by
  refine ⟨fun _ => hc, ?_, ?_⟩
  · intro j a
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((univ.filter (fun o : Obj m s => o.1 = j ∧ a ∈ o.2.1)).card : ℝ) * c
        ≤ ((s - 1 : ℕ) : ℝ) * c :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_host_vertex_le m s j a) hc
      _ = c * ((s - 1 : ℕ) : ℝ) := by ring
      _ ≤ 1 := hdeg
  · intro e
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_pair]
    calc (m : ℝ) * c = c * (m : ℝ) := by ring
      _ ≤ 1 := hpair

theorem sum_const_obj (c : ℝ) : ∑ _o : Obj m s, c = ((m * s.choose 2 : ℕ) : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_objects, nsmul_eq_mul]

theorem le_muMatDeg_of_feasible {x : Obj m s → ℝ} (hx : MasterFeasibleDeg m s x) :
    (∑ o, x o) ≤ muMatDeg m s := by
  apply le_csSup
  · exact ⟨(s.choose 2 : ℝ), by rintro v ⟨y, hy, rfl⟩; exact sum_le_choose_of_deg m s y hy⟩
  · exact ⟨x, hx, rfl⟩

/-- **Scarce hosts:** with `m ≤ s − 1` the uniform point `1/(s−1)` attains `m·s/2`. -/
theorem muMatDeg_ge_of_le (hs : 2 ≤ s) (hm : m ≤ s - 1) : ((m : ℝ) * s / 2) ≤ muMatDeg m s := by
  have hs1 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    have : 1 ≤ s - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  set c : ℝ := 1 / ((s - 1 : ℕ) : ℝ) with hcdef
  have hfeas : MasterFeasibleDeg m s (fun _ => c) := by
    refine masterFeasibleDeg_const m s (by positivity) ?_ ?_
    · rw [hcdef, div_mul_eq_mul_div, one_mul, div_self (ne_of_gt hs1)]
    · rw [hcdef, div_mul_eq_mul_div, one_mul, div_le_one hs1]
      exact_mod_cast hm
  have hval := le_muMatDeg_of_feasible m s hfeas
  rw [sum_const_obj] at hval
  have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ s := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hcard : ((m * s.choose 2 : ℕ) : ℝ) = (m : ℝ) * ((s : ℝ) * ((s : ℝ) - 1) / 2) := by
    push_cast
    rw [choose_two_real s (by omega)]
  rw [hcard, hcdef, hsub] at hval
  have hne : ((s : ℝ) - 1) ≠ 0 := by rw [← hsub]; exact ne_of_gt hs1
  calc (m : ℝ) * s / 2 = (m : ℝ) * ((s : ℝ) * ((s : ℝ) - 1) / 2) * (1 / ((s : ℝ) - 1)) := by
        field_simp
    _ ≤ muMatDeg m s := hval

/-- **Abundant hosts:** with `s − 1 ≤ m` the uniform point `1/m` attains `C(s,2)`. -/
theorem muMatDeg_ge_of_ge (hs : 2 ≤ s) (hm : s - 1 ≤ m) (hm0 : 1 ≤ m) :
    ((s.choose 2 : ℕ) : ℝ) ≤ muMatDeg m s := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  set c : ℝ := 1 / (m : ℝ) with hcdef
  have hfeas : MasterFeasibleDeg m s (fun _ => c) := by
    refine masterFeasibleDeg_const m s (by positivity) ?_ ?_
    · rw [hcdef, div_mul_eq_mul_div, one_mul, div_le_one hmpos]
      exact_mod_cast hm
    · rw [hcdef, div_mul_eq_mul_div, one_mul, div_self (ne_of_gt hmpos)]
  have hval := le_muMatDeg_of_feasible m s hfeas
  rw [sum_const_obj, hcdef] at hval
  calc ((s.choose 2 : ℕ) : ℝ) = ((m * s.choose 2 : ℕ) : ℝ) * (1 / (m : ℝ)) := by
        push_cast; field_simp
    _ ≤ muMatDeg m s := hval

/-- **The degree-only optimum, exactly.** -/
theorem muMatDeg_eq_min (hs : 2 ≤ s) (hm0 : 1 ≤ m) :
    muMatDeg m s = min ((m : ℝ) * s / 2) ((s.choose 2 : ℕ) : ℝ) := by
  refine le_antisymm (muMatDeg_le_min m s) ?_
  have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ s := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hchoose := choose_two_real s (by omega)
  rcases le_total m (s - 1) with h | h
  · have h1 := muMatDeg_ge_of_le m s hs h
    have h2 : (m : ℝ) * s / 2 ≤ ((s.choose 2 : ℕ) : ℝ) := by
      rw [hchoose]
      have : (m : ℝ) ≤ (s : ℝ) - 1 := by rw [← hsub]; exact_mod_cast h
      have hspos : (0 : ℝ) ≤ (s : ℝ) := by positivity
      nlinarith
    rw [min_eq_left h2]; exact h1
  · have hge : s - 1 ≤ m := h
    have h1 := muMatDeg_ge_of_ge m s hs hge hm0
    have h2 : ((s.choose 2 : ℕ) : ℝ) ≤ (m : ℝ) * s / 2 := by
      rw [hchoose]
      have : (s : ℝ) - 1 ≤ (m : ℝ) := by rw [← hsub]; exact_mod_cast hge
      have hspos : (0 : ℝ) ≤ (s : ℝ) := by positivity
      nlinarith
    rw [min_eq_right h2]; exact h1

/-- **The factor of Proposition 7.1a is attained for every odd palette.** For odd `s ≥ 3` and
`m ≤ s − 1`, `ν = ((s−1)/s)·μ*_res` exactly; the triangle profile is the case `(m, s) = (1, 3)`. -/
theorem nu_eq_frac_muMatDeg_of_odd (hodd : Odd s) (hs : 3 ≤ s) (hm0 : 1 ≤ m) (hm : m ≤ s - 1) :
    (nu m s : ℝ) = ((s : ℝ) - 1) / s * muMatDeg m s := by
  have hspos : (0 : ℝ) < (s : ℝ) := by positivity
  have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ s := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hchoose := choose_two_real s (by omega)
  have hmle : (m : ℝ) ≤ (s : ℝ) - 1 := by rw [← hsub]; exact_mod_cast hm
  -- the LP value is `m·s/2`
  have hmu : muMatDeg m s = (m : ℝ) * s / 2 := by
    rw [muMatDeg_eq_min m s (by omega) hm0, min_eq_left]
    rw [hchoose]; nlinarith
  -- the integral value is `m·(s−1)/2`
  have hhalf : ((s / 2 : ℕ) : ℝ) = ((s : ℝ) - 1) / 2 := by
    have h2 : 2 * (s / 2) = s - 1 := by obtain ⟨k, hk⟩ := hodd; omega
    have hcast : (2 : ℝ) * ((s / 2 : ℕ) : ℝ) = ((s - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [hsub] at hcast
    linarith
  have hnu : (nu m s : ℝ) = (m : ℝ) * (((s : ℝ) - 1) / 2) := by
    rw [prop43_nu]
    push_cast [hhalf]
    rw [min_eq_left]
    rw [hchoose]
    nlinarith
  rw [hnu, hmu]
  field_simp

end PaperV.PureProfile
