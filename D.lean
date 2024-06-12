/-
Copyright (c) 2020 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bjørn Kjos-Hanssen.
Zulip chat help from:
  Alex J. Best, Johan Commelin, Kyle Miller, Pedro Minicz, Reid Barton, Scott Morrison, Heather Macbeth.
Code contribution and definition of D improvement from:
  Jason Greuling

Lean 4 version from 2024.
-/
-- import data.Finset  -- finite set
-- import data.set -- to make backslash work as set difference
import Mathlib.Data.Finset.Basic
-- import topology.metric_space.basic

-- import data.real.basic

import Myproject.delta

-- import data.set.basic

--set_option profiler true

--set_option pp.all true -- this makes tactic proofs look weird, like has_mem.mem instead of just ∈

/-!
# A theorem on metrics based on min and max
In this file we give a formal proof that in terms of
d(X,Y)= m min(|X\Y|, |Y\X|) + M max(|X\Y|, |Y\X|)
the function
D(X,Y) = d(X,Y)/(|X ∩ Y|+d(X,Y))
is a metric if and only if m ≤ M and 1 ≤ M.
In particular, taking m=M=1, the Jaccard distance is a metric on Finset ℕ.
## Main results
- `noncomputable instance jaccard_nid.metric_space`: the proof of the main result described above.
- `noncomputable instance jaccard.metric_space`: the special case of the Jaccard distance.
## Notation
 - `|_|` : Notation for cardinality.
## References
See [KNYHLM20] for the original proof (https://math.hawaii.edu/~bjoern/nid-walcom.pdf).
-/

open Finset

variable {m M : ℝ} -- in delta.lean but can't import variables


-- section jaccard_nid

variable {α : Type*} [DecidableEq α]

-- --#check δ

-- /-- using Lean's "group with zero" to hand the case 0/0=0 -/
noncomputable def D : ℝ → ℝ → Finset α → (Finset α → ℝ) :=
  λ m M x y ↦ (δ m M x y) / (|x ∩ y| + δ m M x y)



lemma cap_sdiff (X Y Z : Finset α): X ∩ Z  ⊆  X ∩ Y ∪ Z \ Y :=
  have h: ∀ a : α, a ∈ X ∩ Z → a ∈ X ∩ Y ∪ Z \ Y := by intro a;simp;tauto
  (subset_iff.mpr) h

lemma sdiff_cap (X Y Z : Finset α): (X ∩ Z) \ Y ⊆ Z \ Y := by
  intros a a_1;  simp at *; tauto

-- --#print sdiff_cap

theorem twelve_end (X Y Z : Finset α) : |X ∩ Z| ≤ |X ∩ Y| + max (|Z \ Y|) (|Y \ Z|) := by
  let z_y := |Z \ Y|
  let y_z := |Y \ Z|
  let y := |Y|
  let z := |Z|
  cases (em (y ≤ z)) with
  |inl h =>
    calc |X ∩ Z| ≤ |X ∩ Y  ∪  Z \ Y| := card_le_card (cap_sdiff X Y Z)
    _ ≤ |X ∩ Y| + |Z \ Y| := card_union_le (X ∩ Y) (Z \ Y)
    _ = |X ∩ Y| + max z_y y_z := by rw[max_eq_left (sdiff_card Z Y h)]
  |inr h =>
    have h1: z ≤ y := le_of_lt ((lt_iff_not_ge _ _).mpr h)
    have h_diff: z_y ≤ y_z := sdiff_card Y Z h1
    let x110 := |(X ∩ Y) \ Z|
    let x010 := |(Y \ X) \ Z|
    let x111 := |X ∩ Y ∩ Z|
    let x101 := |(X ∩ Z) \ Y|
    let xz := |X ∩ Z|
    let xy := |X ∩ Y|
    let xz_y := |(X ∩ Z) \ Y|
    have r: xz_y ≤ z_y := card_le_card (sdiff_cap X Y Z)
    have uni_xz:  X ∩ Z = ((X ∩ Z) \ Y) ∪ (X ∩ Y ∩ Z) := by
      ext;simp;tauto
    have uni_xy:  ((X ∩ Y) \ Z) ∪ (X ∩ Y ∩ Z) = X ∩ Y := by ext;simp;tauto
    have uni_y_z: ((X ∩ Y) \ Z) ∪ ((Y \ X) \ Z) = Y \ Z := by ext;simp;tauto
    have dis_xz:  Disjoint ((X ∩ Z) \ Y) ((X ∩ Y) ∩ Z) := by rw [disjoint_iff];ext;simp;tauto
    have dis_xy:  Disjoint ((X ∩ Y) \ Z) (X ∩ Y ∩ Z) := by rw [disjoint_iff];ext;simp;tauto
    have dis_y_z: Disjoint ((X ∩ Y) \ Z) ((Y \ X) \ Z) := by rw [disjoint_iff];ext;simp;tauto
    have sum_xz: xz = x101 + x111 := calc
                xz = (((X ∩ Z) \ Y) ∪ (X ∩ Y ∩ Z)).card := congr_arg card uni_xz
                _ = x101 + x111 := card_union_of_disjoint dis_xz
    have sum_xy:  x110 + x111 = xy := calc
                  x110 + x111 = (((X ∩ Y) \ Z) ∪ (X ∩ Y ∩ Z)).card := by
                    rw [card_union_of_disjoint];apply dis_xy
                  _ = xy := (congr_arg card uni_xy)
    have sum_y_z: x110 + x010 = y_z := calc
                  x110 + x010 = (((X ∩ Y) \ Z) ∪ ((Y \ X) \ Z)).card := (card_union_of_disjoint dis_y_z).symm
                  _ = y_z := congr_arg card uni_y_z
    have prelim: x101 ≤ x110 + x110 + x010 := calc
                x101 ≤ y_z                 := by exact le_trans r h_diff
                  _ = x110 + x010          := by rw[sum_y_z]
                  _ = 0 + (x110 + x010)    := by ring
                  _ ≤ x110 + (x110 + x010) := add_le_add_right (Nat.zero_le x110) (x110 + x010)
                  _ = x110 + x110 + x010   := by ring
    calc xz = x101 + x111                  := sum_xz
        _ ≤ x110 + x110 + x010 + x111     := add_le_add_right prelim x111
        _ = (x110 + x111) + (x110 + x010) := by ring
        _ = xy            + max z_y y_z   := by rw[sum_xy,sum_y_z,max_eq_right h_diff]

theorem twelve_middle (hm: 0 ≤ m) (hM: 0 < M) (X Y Z : Finset α) :
  let y_z := |Y\Z|
  let z_y := |Z\Y|
  let xy := |X ∩ Y|
  (|X ∩ Z|:ℝ) ≤ (xy:ℝ) + (max z_y y_z:ℝ) + (m/M) * (min z_y y_z:ℝ) :=
  let y_z := |Y\Z|
  let z_y := |Z\Y|
  let xy := |X ∩ Y|
  let xz := |X ∩ Z|
  have b: 0 ≤ m/M ↔ 0*M ≤ m := le_div_iff hM
  have a: 0*M ≤ m := calc
          0*M = 0 := by ring
          _ ≤ m := hm
  have g:0 ≤ m/M := (b.mpr) a
  have e:0 ≤ min z_y y_z := le_min (Nat.zero_le z_y) (Nat.zero_le y_z)
  have f:0 ≤ (min z_y y_z:ℝ) := by norm_cast
  let maxzy := (max z_y y_z:ℝ)
  calc
  (xz:ℝ) ≤ (xy:ℝ) + (max z_y y_z:ℝ) := by norm_cast;exact (twelve_end X Y Z)
  _ = (xy:ℝ) + maxzy + 0                       := by ring
  _ ≤ (xy:ℝ) + maxzy + (m/M) * (min z_y y_z:ℝ) :=
            add_le_add_left (mul_nonneg g f) ((xy:ℝ) + maxzy)


theorem jn_self  (X : Finset α): D m M X X = 0 := by
    show (δ m M X X) / (|X ∩ X| + δ m M X X) = 0
    rw[delta_self,zero_div]

theorem delta_nonneg {x y : Finset α} (hm: 0 ≤ m) (hM: m ≤ M): 0 ≤ δ m M x y :=
  have : 0 ≤ 2 * δ m M x y := calc
     0 = δ m M x x := by rw[delta_self]
     _ ≤ δ m M x y + δ m M y x := seventeen_right hm hM
     _ = 2 * δ m M x y := by rw [delta_comm, two_mul]
  nonneg_of_mul_nonneg_right this zero_lt_two

theorem jn_comm (X Y : Finset α): D m M X Y = D m M Y X := by
    show (δ m M X Y) / (|X ∩ Y| + δ m M X Y)  = (δ m M Y X) / (|Y ∩ X| + δ m M Y X)
    rw[delta_comm,delta_comm,inter_comm]

lemma card_inter_nonneg (X Y : Finset α):
  0 ≤ (|X ∩ Y|:ℝ) := by norm_cast; exact Nat.zero_le (|X ∩ Y|)

lemma D_denom_nonneg (X Y : Finset α) (hm: 0 ≤ m) (hM: m ≤ M):
  0 ≤ (|X ∩ Y|:ℝ) + δ m M X Y := add_nonneg (card_inter_nonneg X Y) (delta_nonneg hm hM)


theorem eq_of_jn_eq_zero (hm: 0 < m) (hM: m ≤ M) (X Y : Finset α) (h: D m M X Y = 0) : X = Y := by
    have h1: (δ m M X Y) = 0 ∨ ((|X ∩ Y|:ℝ) + δ m M X Y) = 0 :=
      ((div_eq_zero_iff).mp) h
    cases h1 with
    |inl g =>
        exact eq_of_delta_eq_zero hm hM X Y g
    |inr g =>
        have denom:  0 = δ m M X Y + |X ∩ Y| := by rw [add_comm] at g; exact g.symm
        have nonneg: 0 ≤ δ m M X Y := delta_nonneg (le_of_lt hm) hM
        have zero:   0 = δ m M X Y :=
            eq_zero_of_nonneg_of_nonneg_of_add_zero nonneg (card_inter_nonneg X Y) denom
        exact eq_of_delta_eq_zero hm hM X Y (Eq.symm zero)

theorem D_nonneg (X Y : Finset α) (hm: 0 ≤ m) (hM: m ≤ M): 0 ≤ D m M X Y := by
  have hc: 0 ≤ δ m M X Y := delta_nonneg hm hM
  by_cases hd : (0 < (|X ∩ Y|:ℝ) + δ m M X Y)
  . calc
    0 = 0         / ((|X ∩ Y|:ℝ) + δ m M X Y) := by rw[zero_div]
    _ ≤ δ m M X Y / ((|X ∩ Y|:ℝ) + δ m M X Y) := div_le_div hc hc hd (le_refl _)
  . have hd2: 0 ≤ (|X ∩ Y|:ℝ) + δ m M X Y := D_denom_nonneg X Y hm hM
    have hdd: 0 = (|X ∩ Y|:ℝ) + δ m M X Y :=
      by_contra (
        λ hh: ¬ 0 = (|X ∩ Y|:ℝ) + δ m M X Y ↦
        hd ((lt_iff_le_and_ne.mpr) (And.intro hd2 hh))
      )
    calc 0 ≤ 0 := le_refl 0
    _ = δ m M X Y / 0 := by rw[div_zero]
    _ = δ m M X Y / ((|X ∩ Y|:ℝ) + δ m M X Y) := by rw[hdd]

theorem D_empty_1 (m M : ℝ) {X Y : Finset α} (hm: 0 < m) (hM: m ≤ M)
  (hx : X = ∅) (hy : Y ≠ ∅) : D m M X Y = 1 := by
    have hhh: X ∩ Y = ∅ := calc
              X ∩ Y = ∅ ∩ Y := by rw [hx]
              _ = ∅         := empty_inter Y
    have h: |X ∩ Y| = 0 :=
      calc |X∩ Y|=|(∅:Finset α)| := by rw [hhh]
      _ = 0 := card_empty
    have h1: X ≠ Y := by
      intro h2
      have h3: Y = ∅ := Eq.trans h2.symm hx
      exact hy h3
    have h0: δ m M X Y ≠ 0 := by
      intro h2
      have h3: X = Y := eq_of_delta_eq_zero (hm) hM X Y h2
      exact h1 h3
    have hh: (|X ∩ Y|:ℝ) = 0 := by norm_cast
    calc
    (δ m M X Y)/(|X ∩ Y| + δ m M X Y) = (δ m M X Y)/(0 + δ m M X Y) := by rw[hh]
    _ = (δ m M X Y)/(δ m M X Y)     := by rw[zero_add]
    _ = 1                           := div_self h0

theorem D_empty_2  (m M : ℝ) {X Y : Finset α} (hm: 0 < m) (hM: m ≤ M)
  (hx : X ≠ ∅) (hy : Y = ∅) : D m M X Y = 1 :=
  let dxy := δ m M X Y
  calc
  dxy / (|X ∩ Y| + dxy) = (δ m M Y X)/(|Y ∩ X| + δ m M Y X) := by rw[delta_comm,inter_comm]
  _ = 1                                 := D_empty_1 m M hm hM hy hx



theorem D_bounded (m M : ℝ) (X Y : Finset α) (hm: 0 ≤ m) (hM: m ≤ M): D m M X Y ≤ 1 := by
  by_cases h0 : ((0 = (|X ∩ Y|:ℝ) + δ m M X Y))
  . calc
    (δ m M X Y)/(|X ∩ Y| + δ m M X Y) = (δ m M X Y)/0 := by rw[h0]
                                  _ = 0 := div_zero (δ m M X Y)
                                  _ ≤ 1 := zero_le_one
  .
    let dxy := δ m M X Y
    have hd2: 0 ≤ (|X ∩ Y|:ℝ) + dxy := D_denom_nonneg X Y hm hM

    have pos: 0 < (|X ∩ Y|:ℝ) + dxy := (lt_iff_le_and_ne.mpr) (And.intro hd2 h0)
    have h: dxy ≤ |X ∩ Y| + dxy :=
       calc dxy =    0    + dxy := by rw[zero_add]
       _ ≤ |X ∩ Y| + dxy := add_le_add_right (card_inter_nonneg X Y) (dxy)
    show dxy /(|X ∩ Y| + dxy) ≤ 1
    exact calc
    dxy /(|X ∩ Y| + dxy) ≤ (|X ∩ Y| + dxy)/(|X ∩ Y| + dxy) := by apply div_le_div;tauto;tauto;tauto;exact le_refl _
    _ ≤ 1 := div_self_le_one (|X ∩ Y| + dxy)

theorem intersect_cases (m M : ℝ) (Y Z : Finset α) (hm: 0< m) (hM: m≤ M) (hy: Y ≠ ∅):
    let ayz := (|Z ∩ Y|:ℝ)
    let dyz :=  (δ m M Z Y)
    0 < (ayz + dyz) := by

      let ayz := (|Z ∩ Y|:ℝ)
      let dyz :=  (δ m M Z Y)

      by_cases hxy : ((Y ∩ Z = ∅))
      . have decompose: Y = Y ∩ Z ∪ Y \ Z := by
            ext;simp;tauto
        have non_empty: ∅ ≠ Y \ Z := by
          intro h
          have h1:Y = ∅ :=
            calc Y = Y ∩ Z ∪ Y \ Z := decompose
                _ =   ∅   ∪   ∅   := by rw[hxy,h]
                _ =       ∅       := by rw [union_empty]
          exact hy h1
        have ne_prelim: Z ≠ Y := by
          intro h
          have h0: Y \ Z = ∅ := by calc
            Y \ Z = Z \ Z := by rw[h]
            _     = ∅     := by apply sdiff_self
          have h1: ∅ = Y \ Z := h0.symm
          exact non_empty h1
        have ne: 0 ≠ dyz :=
          λ zero_eq_delta: 0 = dyz ↦
          have eq: Z = Y := eq_of_delta_eq_zero hm hM Z Y zero_eq_delta.symm
          ne_prelim eq
        have le: 0 ≤ dyz := delta_nonneg (le_of_lt hm) hM
        calc 0 <       dyz := (lt_iff_le_and_ne.mpr) (And.intro le ne)
            _ =  0  + dyz := by rw[zero_add]
            _ ≤ ayz + dyz := add_le_add_right (card_inter_nonneg Z Y) dyz
      . have card_zero: |Y ∩ Z| = 0 ↔ Y ∩ Z = ∅ := card_eq_zero
        have ne_nat: |Y ∩ Z| ≠ 0 :=
          λ h: |Y ∩ Z| = 0 ↦
          hxy ((card_zero.mp) h)
        have le: 0 ≤ (|Y ∩ Z|:ℝ) := card_inter_nonneg Y Z
        have ne: 0 ≠ (|Y ∩ Z|:ℝ) := by norm_cast;exact ne_nat.symm
        calc 0 < (|Y ∩ Z|:ℝ) := (lt_iff_le_and_ne.mpr) (And.intro le ne)
          _ = ayz      := by rw[inter_comm]
          _ = ayz +  0 := by rw[add_zero]
          _ ≤ ayz + dyz := add_le_add_left (delta_nonneg (le_of_lt hm) hM) ayz


lemma four_immediate_from (m M : ℝ) (X Y Z : Finset α)
  (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M)
  (hz: Z ≠ ∅):
  let axy := (|X ∩ Y|:ℝ)
  let dxz := δ m M X Z
  let dyz := δ m M Z Y
  let axz := (|X ∩ Z|:ℝ)
  let denom := axy+dxz+dyz
  dxz/denom ≤ dxz/(axz + dxz) :=

  let axy := (|X ∩ Y|:ℝ)
  let dxz := δ m M X Z
  let dyz :=  (δ m M Z Y)
  let axz := (|X ∩ Z|:ℝ)
  let y_z : ℕ := (Y \ Z).card
  let z_y : ℕ := (Z \ Y).card
  let xy : ℕ := (X ∩ Y).card
  let xz : ℕ := (X ∩ Z).card
  let mini := (min (|Z \ Y|) (|Y \ Z|) : ℝ)
  let maxi := (max (|Z \ Y|) (|Y \ Z|) : ℝ)
  let denom := (axy+dxz+dyz)
  have twelve_end_real: (xz:ℝ) ≤ (xy:ℝ) + max (|Z \ Y| : ℝ) (|Y \ Z| : ℝ) := by
    have ddd: xz ≤ xy + max ((Z \ Y).card) ((Y \ Z).card) := twelve_end X Y Z
    norm_cast
  have max_nonneg_real: 0 ≤ (max (|Z \ Y|) (|Y \ Z|) : ℝ) := by
    have : 0 ≤ max z_y y_z := Nat.zero_le (max z_y y_z)
    norm_cast
  have min_nonneg_real: 0 ≤ (min (|Z \ Y|) (|Y \ Z|) : ℝ) := by
    have : 0 ≤ min z_y y_z := Nat.zero_le (min z_y y_z)
    norm_cast
  have mmin_nonneg : 0 ≤ m * mini := mul_nonneg (le_of_lt hm) min_nonneg_real
  have use_h1M: 1 * maxi ≤ M * maxi := mul_le_mul_of_nonneg_right h1M max_nonneg_real
  have four_would_follow_from : axz ≤ axy + dyz := calc
      axz ≤ (xy:ℝ) +     maxi           := twelve_end_real
      _ = (xy:ℝ) + 1 * maxi             := by ring
      _ ≤ (xy:ℝ) + M * maxi             := add_le_add_left use_h1M (xy:ℝ)
      _ = (xy:ℝ) + M * maxi + 0         := by rw[add_zero]
      _ ≤ (xy:ℝ) + M * maxi + m * mini  := add_le_add_left mmin_nonneg ((xy:ℝ) + M * maxi)
      _ = (xy:ℝ) + (M * (max (|Z \ Y|) (|Y \ Z|) : ℝ) + m * (min (|Z \ Y|) (|Y \ Z|) : ℝ)):=
        by rw[add_assoc]
      _ = (|X ∩ Y|:ℝ)    + (δ m M Z Y) := by unfold δ;simp
  have le_denom:(axz + dxz) ≤ denom :=
      calc axz + dxz ≤ axy + dyz + dxz := add_le_add_right four_would_follow_from dxz
      _ = axy + dxz + dyz := by ring
  have denom_pos : 0 < (axz + dxz) := intersect_cases m M Z X hm hM hz
  have d_nonneg: 0 ≤ dxz := delta_nonneg (le_of_lt hm) hM
  div_le_div_of_nonneg_left d_nonneg denom_pos le_denom

 lemma four_immediate_from_and  (m M : ℝ) (X Y Z : Finset α)
  (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M) (hz: Z ≠ ∅):
  (δ m M Z Y)/((|X ∩ Y|:ℝ) + δ m M X Z + δ m M Z Y) ≤ (δ m M Z Y)/((|Z ∩ Y|:ℝ) + δ m M Z Y) :=

  let dzy := δ m M Z Y
  let dyz := δ m M Y Z
  let dxz := δ m M X Z
  let dzx := δ m M Z X
  have S: (dyz) / ((|Y ∩ X|:ℝ) + (dyz) + (dzx)) ≤ (dyz) / ((|Y ∩ Z|:ℝ) + dyz) :=
    four_immediate_from m M Y X Z hm hM h1M hz
  have dzy_comm: dzy = dyz := delta_comm _ _
  have dxz_comm: dxz = dzx := delta_comm _ _
  have ring_in_denom: (|Y ∩ X|:ℝ) + dzx + dyz = (|Y ∩ X|:ℝ) + dyz + dzx := by ring
  calc   dzy / ((|X ∩ Y|:ℝ) + dxz + dzy)
       = dyz / ((|Y ∩ X|:ℝ) + dyz + dzx) := by rw[inter_comm,dxz_comm,dzy_comm,ring_in_denom]
   _ ≤ dyz / ((|Y ∩ Z|:ℝ) + dyz)       := S
   _ = dzy / ((|Z ∩ Y|:ℝ) + dzy)       := by rw[inter_comm,dzy_comm]



lemma mul_le_mul_rt {a b c : ℝ} (h : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right hab h

lemma abc_lemma {a b c : ℝ} (h : 0 ≤ a) (hb : a ≤ b) (hc : 0 ≤ c) : (a/(a+c)) ≤ (b/(b+c)) := by
  by_cases ha : 0 = a
  . by_cases hhb : 0 = b
    . calc  a/(a+c)
          = 0/(0+c):= by rw [ha]
      _ ≤ 0/(0+c):= le_refl (0/(0+c))
      _ = b/(b+c):= by rw [hhb]
    . have g0: 0 ≤ b := (le_trans h hb)
      have g: 0 ≤ b + c := add_nonneg g0 hc
      calc  a/(a+c)
          = 0/(a+c):= by rw [ha]
      _ = 0 := by rw [zero_div]
      _ ≤ b/(b+c) := div_nonneg g0 g
  .
    have ha: 0 < a := (lt_iff_le_and_ne.mpr) (And.intro h ha)
    have numer : a*(b+c) ≤ b*(a+c) := calc
      a*(b+c) = a*b + a*c := by rw [left_distrib]
      _ ≤ a*b + b*c := add_le_add_left (mul_le_mul_rt hc hb) (a*b)
      _ = b * (a+c) := by ring
    have h6 : 0 < a+c := lt_add_of_pos_of_le ha hc
    have h7 : 0 < b+c := lt_add_of_pos_of_le (gt_of_ge_of_gt hb ha) hc
    exact ((div_le_div_iff h6 h7).mpr) numer


theorem three (X Y Z : Finset ℕ) (hm: 0 < m) (hM: m ≤ M):
  let axy := (|X ∩ Y| : ℝ)
  let dxy := δ m M X Y
  let dxz := δ m M X Z
  let dyz := δ m M Z Y
  let denom := (axy+dxz+dyz)
  dxy/(axy + dxy) ≤ (dxz+dyz)/denom :=

  let dxy := δ m M X Y
  let dxz := δ m M X Z
  let dzy := δ m M Y Z
  let dyz := δ m M Z Y
  let axy := (|X ∩ Y| : ℝ)

  have hd : 0 ≤ δ m M X Y := delta_nonneg (le_of_lt hm) hM
  have h0 : δ m M Z Y = δ m M Y Z := by rw [delta_comm]
  have h1 : dxy ≤ dxz + dzy := calc
    dxy ≤ dxz + δ m M Z Y := delta_triangle X Z Y hm hM
    _ = dxz + δ m M Y Z := by rw [h0]
  have h2: dxz + dyz + axy = axy + dxz + dyz := by ring
    calc  dxy / (axy + dxy)
        = dxy / (dxy + axy)                         := by rw [add_comm axy dxy]
    _ ≤ (dxz + δ m M Y Z) / (dxz + dzy + axy)       := abc_lemma hd h1 (card_inter_nonneg X Y)
    _ = (dxz + δ m M Z Y) / (dxz + δ m M Z Y + axy) := by rw [h0]
    _ = (dxz + δ m M Z Y) / (axy + dxz + δ m M Z Y) := by rw [h2]


 theorem jn_triangle_nonempty
  (m M : ℝ) (X Y Z : Finset ℕ) (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M)
  (hz: Z ≠ ∅): D m M X Y ≤ D m M X Z + D m M Z Y :=
  let dxy := (δ m M X Y)
  let axy := (|X ∩ Y|:ℝ)
  let dxz := δ m M X Z
  let dyz :=  (δ m M Z Y)
  let ayz := (|Z ∩ Y|:ℝ)
  let axz := (|X ∩ Z|:ℝ)
  let denom := (axy+dxz+dyz)
    have three: dxy/(axy + dxy) ≤ (dxz+dyz)/denom := three X Y Z hm hM
    have four: (dxz+dyz)/denom ≤ dxz/(axz + dxz) + dyz/(ayz + dyz) := calc
      (dxz+dyz)/denom = dxz/denom + dyz/denom := add_div dxz dyz denom
      _ ≤ dxz/(axz + dxz)   + dyz/denom :=
        add_le_add_right
        (four_immediate_from m M X Y Z hm hM h1M hz)
        ((dyz)/denom)
      _ ≤ dxz/(axz + dxz)   + dyz/(ayz + dyz)  :=
        add_le_add_left
        (four_immediate_from_and m M X Y Z hm hM h1M hz)
        (dxz/(axz + dxz))
    le_trans three four

theorem jn_triangle (m M : ℝ) (X Y Z : Finset ℕ)
(hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M): D m M X Y ≤ D m M X Z + D m M Z Y := by
  by_cases hx : X = ∅
  .
    by_cases hy : Y = ∅
    .
      have h1: X = Y := Eq.trans hx hy.symm
      calc
      D m M X Y = D m M X X           := by rw[h1]
            _ = 0                     := jn_self X
            _ ≤             D m M Z Y := D_nonneg Z Y (le_of_lt hm) hM
            _ = 0         + D m M Z Y := Eq.symm (zero_add (D m M Z Y))
            _ ≤ D m M X Z + D m M Z Y :=
              add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) (D m M Z Y)
    .
      by_cases hz : Z = ∅
      .
        have h3: D m M Z Y = 1 := D_empty_1 m M hm hM hz hy
        calc D m M X Y =             1 := D_empty_1 m M hm hM hx hy
        _ = 0         + 1 := by rw[zero_add]
        _ ≤ D m M X Z + 1 := add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) 1
        _ = D m M X Z + D m M Z Y := by rw[h3]
      .
        have h1: D m M X Y = 1 := D_empty_1 m M hm hM hx hy
        have h2: D m M X Z = 1 := D_empty_1 m M hm hM hx hz
        calc D m M X Y = 1 := h1
        _ = 1 + 0 := by rw[add_zero]
        _ ≤ 1 + D m M Z Y := add_le_add_left (D_nonneg Z Y (le_of_lt hm) hM) 1
        _ = D m M X Z + D m M Z Y := by rw[h2]
  . by_cases hy : Y = ∅
    . by_cases hz : Z = ∅
      .
        calc D m M X Y =     1                  := D_empty_2 m M hm hM hx hy
        _ =     1     +      0     := by rw[add_zero]
        _ ≤     1     +  D m M Z Y := add_le_add_left (D_nonneg Z Y (le_of_lt hm) hM) 1
        _ = D m M X Z +  D m M Z Y := by rw[D_empty_2 m M hm hM hx hz]

      .
        calc D m M X Y =                 1    := D_empty_2 m M hm hM hx hy
        _ =     0     +     1    := by rw[zero_add]
        _ ≤ D m M X Z +     1    := add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) 1
        _ = D m M X Z + D m M Z Y := by rw[D_empty_2 m M hm hM hz hy]

    . by_cases hz : Z = ∅
      .
        have h2: D m M X Z = 1 := D_empty_2 m M hm hM hx hz
        have h3: D m M Z Y = 1 := D_empty_1 m M hm hM hz hy
        calc D m M X Y ≤             1:= D_bounded m M X Y (le_of_lt hm) hM
        _ =         0 + 1:= by rw[zero_add]
        _ ≤         1 + 1:= add_le_add_right zero_le_one 1
        _ = D m M X Z + D m M Z Y := by rw[h2,h3]

      . exact jn_triangle_nonempty m M X Y Z hm hM h1M hz

noncomputable instance jaccard_nid.metric_space
(hm : 0 < m) (hM : m ≤ M) (h1M: 1 ≤ M): MetricSpace (Finset ℕ) := {
        dist               := λx y ↦ D m M x y,
        dist_self          := jn_self,
        eq_of_dist_eq_zero := eq_of_jn_eq_zero hm hM _ _,
        dist_comm          := λ x y ↦ jn_comm x y,
        dist_triangle      := λ x z y ↦ jn_triangle m M x y z hm hM h1M
        edist_dist         := (λ x y ↦ by exact (ENNReal.ofReal_eq_coe_nnreal _).symm)

    }

def J : Finset ℕ → (Finset ℕ → ℚ) :=
  λ X Y ↦ (|X \ Y| + |Y \ X|) / |X ∪ Y|

theorem J_characterization (X Y : Finset ℕ):
J X Y = D 1 1 X Y := by
  unfold J D δ
  simp
  have h : X = (X ∩ Y) ∪ (X \ Y) := by ext;simp;tauto
  suffices (X ∪ Y).card = (X ∩ Y).card + (X \ Y).card + (Y \ X).card by
    rw [this]
    norm_cast
    ring_nf
  suffices (X ∪ Y).card = X.card + (Y \ X).card
 by
    rw [this]
    refine Nat.add_right_cancel_iff.mpr ?_
    rw [h]
    simp
  have h₀ : X ∪ Y = X ∪ (Y \ X) := by ext;simp
  rw [h₀]
  apply card_union_of_disjoint
  exact disjoint_sdiff

noncomputable instance jaccard.metric_space
(hm : (0:ℝ) < (1:ℝ)) (hM : (1:ℝ) ≤ (1:ℝ)) (h1M: (1:ℝ) ≤ (1:ℝ)): MetricSpace (Finset ℕ) := {
        dist               := λx y ↦ D 1 1 x y,
        dist_self          := jn_self,
        eq_of_dist_eq_zero := eq_of_jn_eq_zero hm hM _ _,
        dist_comm          := λ x y ↦ jn_comm x y,
        dist_triangle      := λ x z y ↦ jn_triangle 1 1 x y z hm hM h1M
        edist_dist         := (λ x y ↦ by exact (ENNReal.ofReal_eq_coe_nnreal _).symm)
    }

-- end jaccard_nid
