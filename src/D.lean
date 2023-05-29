/-
Copyright (c) 2020 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bjørn Kjos-Hanssen.
Zulip chat help from:
  Alex J. Best, Johan Commelin, Kyle Miller, Pedro Minicz, Reid Barton, Scott Morrison, Heather Macbeth.
Code contribution and definition of D improvement from:
  Jason Greuling
-/
import data.finset  -- finite set
import data.set -- to make backslash work as set difference
import data.finset.basic
import topology.metric_space.basic
 
import data.real.basic

import delta

import data.set.basic

--set_option profiler true

--set_option pp.all true -- this makes tactic proofs look weird, like has_mem.mem instead of just ∈ 

/-!
# A theorem on metrics based on min and max
In this file we give a formal proof that in terms of
d(X,Y)= m min(|X\Y|, |Y\X|) + M max(|X\Y|, |Y\X|)
the function
D(X,Y) = d(X,Y)/(|X ∩ Y|+d(X,Y))
is a metric if and only if m ≤ M and 1 ≤ M.
In particular, taking m=M=1, the Jaccard distance is a metric on finset ℕ.
## Main results
- `noncomputable instance jaccard_nid.metric_space`: the proof of the main result described above.
- `noncomputable instance jaccard.metric_space`: the special case of the Jaccard distance.
## Notation
 - `|_|` : Notation for cardinality.
## References
See [KNYHLM20] for the original proof (https://math.hawaii.edu/~bjoern/nid-walcom.pdf).
-/


open finset

local notation (name := X.card) |X| := X.card

variables {m M : ℝ} -- in delta.lean but can't import variables


section jaccard_nid

variables {α : Type*} [decidable_eq α]
--#check δ

/-- using Lean's "group with zero" to hand the case 0/0=0 -/
noncomputable def D : ℝ → ℝ → finset α → (finset α → ℝ) :=
  λ m M x y, (δ m M x y) / (|x ∩ y| + δ m M x y)



lemma cap_sdiff (X Y Z : finset α): X ∩ Z  ⊆  X ∩ Y ∪ Z \ Y :=
  have h: ∀ a : α, a ∈ X ∩ Z → a ∈ X ∩ Y ∪ Z \ Y,
  by {intro a,intro g,rw mem_inter at g,rw[mem_union,mem_inter,mem_sdiff],by_cases (a ∈ Y),cc,cc,},
  (iff.elim_right subset_iff) h

lemma sdiff_cap (X Y Z : finset α): X ∩ Z \ Y ⊆ Z \ Y := -- by show_term{tidy} -- by tidy?
by {intros a a_1,  simp at *, cases a_1, cases a_1_left, split, assumption, assumption}

--#print sdiff_cap

theorem twelve_end (X Y Z : finset α) : |X ∩ Z| ≤ |X ∩ Y| + max (|Z \ Y|) (|Y \ Z|) :=
let z_y := |Z \ Y|, y_z := |Y \ Z|, y := |Y|, z := |Z| in
(em (y ≤ z)).elim(
  λ h: y ≤ z, calc |X ∩ Z| ≤ |X ∩ Y  ∪  Z \ Y|     : card_le_of_subset (cap_sdiff X Y Z)
                       ... ≤ |X ∩ Y| + |Z \ Y|     : card_union_le (X ∩ Y) (Z \ Y)
                       ... = |X ∩ Y| + max z_y y_z : by rw[max_eq_left (sdiff_card Z Y h)]
)(
  λ h: ¬ y ≤ z,
  have h1: z ≤ y, from le_of_lt ((lt_iff_not_ge _ _).mpr h),
  have h_diff: z_y ≤ y_z, from sdiff_card Y Z h1, let
    x110 := |X ∩ Y \ Z|, x111 := |X ∩ Y ∩ Z|, x010 := |Y \ X \ Z|,
    x111 := |X ∩ Y ∩ Z|, x101 := |X ∩ Z \ Y|, xz := |X ∩ Z|,
    xy := |X ∩ Y|, xz_y := |X ∩ Z \ Y| in
  have r: xz_y ≤ z_y, from card_le_of_subset (sdiff_cap X Y Z),
  have uni_xz:  X ∩ Z = (X ∩ Z \ Y) ∪ (X ∩ Y ∩ Z), by { tidy, by_cases h: a ∈ Y, cc, cc},
  have uni_xy:  (X ∩ Y \ Z) ∪ (X ∩ Y ∩ Z) = X ∩ Y, by { tidy, by_cases h: a ∈ Z, cc, cc},
  have uni_y_z: (X ∩ Y \ Z) ∪ (Y \ X \ Z) = Y \ Z, by { tidy, by_cases h: a ∈ X, cc, cc},
  have dis_xz:  disjoint (X ∩ Z \ Y) (X ∩ Y ∩ Z), by { rw disjoint_iff, tidy},
  have dis_xy:  disjoint (X ∩ Y \ Z) (X ∩ Y ∩ Z), by { rw disjoint_iff, tidy},
  have dis_y_z: disjoint (X ∩ Y \ Z) (Y \ X \ Z), by { rw disjoint_iff, tidy},
  have sum_xz: xz = x101 + x111, from calc
               xz = ((X ∩ Z \ Y) ∪ (X ∩ Y ∩ Z)).card : congr_arg card uni_xz
              ... = x101 + x111: card_disjoint_union dis_xz,
  have sum_xy:  x110 + x111 = xy, from calc
                x110 + x111 = ((X ∩ Y \ Z) ∪ (X ∩ Y ∩ Z)).card: (card_disjoint_union dis_xy).symm
                        ... = xy: (congr_arg card uni_xy),
  have sum_y_z: x110 + x010 = y_z, from calc
                x110 + x010 = ((X ∩ Y \ Z) ∪ (Y \ X \ Z)).card: (card_disjoint_union dis_y_z).symm
                        ... = y_z: congr_arg card uni_y_z,
  have prelim: x101 ≤ x110 + x110 + x010, from calc
               x101 ≤ y_z                 : le_trans r h_diff
                ... = x110 + x010          : by rw[sum_y_z]
                ... = 0 + (x110 + x010)    : by ring
                ... ≤ x110 + (x110 + x010) : add_le_add_right (nat.zero_le x110) (x110 + x010)
                ... = x110 + x110 + x010   : by ring,
  calc xz = x101 + x111                   : sum_xz
      ... ≤ x110 + x110 + x010 + x111     : add_le_add_right prelim x111
      ... = (x110 + x111) + (x110 + x010) : by ring
      ... = xy            + max z_y y_z   : by rw[sum_xy,sum_y_z,max_eq_right h_diff]
)

theorem twelve_middle (hm: 0 ≤ m) (hM: 0 < M) (X Y Z : finset α) :
let y_z := |Y\Z|, z_y := |Z\Y|, xy := |X ∩ Y|, xz := |X ∩ Z| in
(|X ∩ Z|:ℝ) ≤ (xy:ℝ) + (max z_y y_z:ℝ) + (m/M) * (min z_y y_z:ℝ) :=
let y_z := |Y\Z|, z_y := |Z\Y|, xy := |X ∩ Y|, xz := |X ∩ Z| in
    have b: 0 ≤ m/M ↔ 0*M ≤ m, from le_div_iff hM,
    have a: 0*M ≤ m, from calc
            0*M = 0 : by ring
            ... ≤ m : hm,
    have g:0 ≤ m/M, from (iff.elim_right b) a,
    have e:0 ≤ min z_y y_z, from le_min (nat.zero_le z_y) (nat.zero_le y_z),
    have f:0 ≤ (min z_y y_z:ℝ), begin norm_cast,exact e, end,
    let maxzy := (max z_y y_z:ℝ) in
    calc
    (xz:ℝ) ≤ (xy:ℝ) + (max z_y y_z:ℝ): by {norm_cast,exact (twelve_end X Y Z)}
       ... = (xy:ℝ) + maxzy + 0                       : by ring
       ... ≤ (xy:ℝ) + maxzy + (m/M) * (min z_y y_z:ℝ) :
              add_le_add_left (mul_nonneg g f) ((xy:ℝ) + maxzy)


theorem jn_self  (X : finset α): D m M X X = 0 :=
    show (δ m M X X) / (|X ∩ X| + δ m M X X) = 0, by rw[delta_self,zero_div]

theorem delta_nonneg {x y : finset α} (hm: 0 ≤ m) (hM: m ≤ M): 0 ≤ δ m M x y :=
  have alpha: δ m M x x ≤ δ m M x y + δ m M y x, from seventeen_right hm hM,
  have 0 ≤ 2 * δ m M x y, from calc
       0 = δ m M x x: by rw[delta_self]
     ... ≤ δ m M x y + δ m M y x: seventeen_right hm hM 
     ... = 2 * δ m M x y: by rw [delta_comm, two_mul],
  nonneg_of_mul_nonneg_right this zero_lt_two

theorem jn_comm (X Y : finset α): D m M X Y = D m M Y X :=
    show (δ m M X Y) / (|X ∩ Y| + δ m M X Y)  = (δ m M Y X) / (|Y ∩ X| + δ m M Y X), from
    by rw[delta_comm,delta_comm,inter_comm]

lemma card_inter_nonneg (X Y : finset α):
  0 ≤ (|X ∩ Y|:ℝ) := by { norm_cast, exact (nat.zero_le (|X ∩ Y|))}

lemma D_denom_nonneg (X Y : finset α) (hm: 0 ≤ m) (hM: m ≤ M):
  0 ≤ (|X ∩ Y|:ℝ) + δ m M X Y := add_nonneg (card_inter_nonneg X Y) (delta_nonneg hm hM)


theorem eq_of_jn_eq_zero (hm: 0 < m) (hM: m ≤ M) (X Y : finset α) (h: D m M X Y = 0) : X = Y :=
    have h1: (δ m M X Y) = 0 ∨ ((|X ∩ Y|:ℝ) + δ m M X Y) = 0, from
      (iff.elim_left (div_eq_zero_iff)) h,
    h1.elim(
        assume g: δ m M X Y = 0,
        eq_of_delta_eq_zero hm hM X Y g
    )(
        assume g: (|X ∩ Y|:ℝ) + δ m M X Y = 0,
        have denom:  0 = δ m M X Y + |X ∩ Y| , begin rw[add_comm] at g, exact g.symm, end,
        have nonneg: 0 ≤ δ m M X Y, from delta_nonneg (le_of_lt hm) hM,
        have zero:   0 = δ m M X Y, from
            eq_zero_of_nonneg_of_nonneg_of_add_zero nonneg (card_inter_nonneg X Y) denom,
        eq_of_delta_eq_zero hm hM X Y (eq.symm zero)
    )

theorem D_nonneg (X Y : finset α) (hm: 0 ≤ m) (hM: m ≤ M): 0 ≤ D m M X Y :=
have hc: 0 ≤ δ m M X Y, from delta_nonneg hm hM,
(em (0 < (|X ∩ Y|:ℝ) + δ m M X Y)).elim(
  λ hd: 0 < (|X ∩ Y|:ℝ) + δ m M X Y,
  calc
    0 = 0         / ((|X ∩ Y|:ℝ) + δ m M X Y) : by rw[zero_div]
  ... ≤ δ m M X Y / ((|X ∩ Y|:ℝ) + δ m M X Y) : div_le_div hc hc hd (le_refl _)
)(
  λ hd: ¬ 0 < (|X ∩ Y|:ℝ) + δ m M X Y,  -- in this case, X = Y = ∅
  have hd2: 0 ≤ (|X ∩ Y|:ℝ) + δ m M X Y, from D_denom_nonneg X Y hm hM,
  have hdd: 0 = (|X ∩ Y|:ℝ) + δ m M X Y, from
    by_contra (
      λ hh: ¬ 0 = (|X ∩ Y|:ℝ) + δ m M X Y,
      hd ((iff.elim_right lt_iff_le_and_ne) (and.intro hd2 hh))
    ),
  calc 0 ≤ 0: le_refl 0
  ... = δ m M X Y / 0: by rw[div_zero]
  ... = δ m M X Y / ((|X ∩ Y|:ℝ) + δ m M X Y): by rw[hdd]
)

theorem D_empty_1 (m M : ℝ) {X Y : finset α} (hm: 0 < m) (hM: m ≤ M):
  X = ∅ → Y ≠ ∅ → D m M X Y = 1 :=
λ hx: X = ∅, λ hy: Y ≠ ∅,
have hhh: X ∩ Y = ∅, from calc
          X ∩ Y = ∅ ∩ Y : by rw hx
            ... = ∅ :empty_inter Y,
have h: |X ∩ Y| = 0, from calc |X∩ Y|=|(∅:finset α)|: by rw hhh
... = 0: card_empty,
have h1: X ≠ Y, from
  assume h2: X = Y,
  have h3: Y = ∅, from eq.trans h2.symm hx,
  hy h3,
have h0: δ m M X Y ≠ 0, from
  assume h2: δ m M X Y = 0,
  have h3: X = Y, from eq_of_delta_eq_zero (hm) hM X Y h2,
  h1 h3,
have hh: (|X ∩ Y|:ℝ) = 0, begin norm_cast,exact h, end,
calc
(δ m M X Y)/(|X ∩ Y| + δ m M X Y) = (δ m M X Y)/(0 + δ m M X Y) : by rw[hh]
                              ... = (δ m M X Y)/(δ m M X Y)     : by rw[zero_add]
                              ... = 1                           : div_self h0 

theorem D_empty_2  (m M : ℝ) {X Y : finset α} (hm: 0 < m) (hM: m ≤ M):
  X ≠ ∅ → Y = ∅ → D m M X Y = 1
:= λ hx: X ≠ ∅, λ hy: Y = ∅, let dxy := δ m M X Y, dyx := δ m M Y X in calc
dxy / (|X ∩ Y| + dxy) = (δ m M Y X)/(|Y ∩ X| + δ m M Y X) : by rw[delta_comm,inter_comm]
                  ... = 1                                 : D_empty_1 m M hm hM hy hx



theorem D_bounded (m M : ℝ) (X Y : finset α) (hm: 0 ≤ m) (hM: m ≤ M): D m M X Y ≤ 1
  :=
  (em (0 = (|X ∩ Y|:ℝ) + δ m M X Y)).elim(
    λ h0: 0 = (|X ∩ Y|:ℝ) + δ m M X Y,
    calc
    (δ m M X Y)/(|X ∩ Y| + δ m M X Y) = (δ m M X Y)/0: by rw[h0]
                                  ... = 0: div_zero (δ m M X Y)
                                  ... ≤ 1: zero_le_one
  )(
    λ h0: 0 ≠ (|X ∩ Y|:ℝ) + δ m M X Y,
    let dxy := δ m M X Y in
    have hd2: 0 ≤ (|X ∩ Y|:ℝ) + dxy, from D_denom_nonneg X Y hm hM,

    have pos: 0 < (|X ∩ Y|:ℝ) + dxy, from (iff.elim_right lt_iff_le_and_ne) (and.intro hd2 h0),
    have h: dxy ≤ |X ∩ Y| + dxy, from
       calc dxy =    0    + dxy: by rw[zero_add]
            ... ≤ |X ∩ Y| + dxy: add_le_add_right (card_inter_nonneg X Y) (dxy),
    calc         dxy /(|X ∩ Y| + dxy)
    ≤ (|X ∩ Y| + dxy)/(|X ∩ Y| + dxy): div_le_div hd2 h pos (le_refl (|X ∩ Y| + dxy)) ...
    ≤ 1: div_self_le_one (|X ∩ Y| + dxy)
  )

theorem intersect_cases (m M : ℝ) (Y Z : finset α) (hm: 0<m) (hM: m≤ M) (hy: Y ≠ ∅) (hz: Z ≠ ∅):
    let ayz := (|Z ∩ Y|:ℝ), dyz :=  (δ m M Z Y) in 0 < (ayz + dyz) :=

    let ayz := (|Z ∩ Y|:ℝ), dyz :=  (δ m M Z Y) in

    (em (Y ∩ Z = ∅)).elim(
        λ hxy : Y ∩ Z = ∅,
        have decompose: Y = Y ∩ Z ∪ Y \ Z, begin tidy,by_cases (a ∈ Z),cc,cc, end,
        have non_empty: ∅ ≠ Y \ Z, from
          assume h: ∅ = Y \ Z,
          have h1:Y = ∅, from
            calc Y = Y ∩ Z ∪ Y \ Z : decompose
               ... =   ∅   ∪   ∅   : by rw[hxy,h]
               ... =       ∅       : by rw union_empty,
          hy h1,
        have ne_prelim: Z ≠ Y, from
          assume h: Z = Y,
          have h0: Y \ Z = ∅, from calc
                   Y \ Z = Z \ Z: by rw[h]
                     ... = ∅: sdiff_self Z,
          have h1: ∅ = Y \ Z, from h0.symm,
          non_empty h1,
        have ne: 0 ≠ dyz, from
          λ zero_eq_delta: 0 = dyz,
          have eq: Z = Y, from eq_of_delta_eq_zero hm hM Z Y zero_eq_delta.symm,
          ne_prelim eq,
        have le: 0 ≤ dyz, from delta_nonneg (le_of_lt hm) hM,
        calc 0 <       dyz: (iff.elim_right lt_iff_le_and_ne) (and.intro le ne)
           ... =  0  + dyz: by rw[zero_add]
           ... ≤ ayz + dyz: add_le_add_right (card_inter_nonneg Z Y) dyz
    )(
        λ hxy : Y ∩ Z ≠ ∅,
          have card_zero: |Y ∩ Z| = 0 ↔ Y ∩ Z = ∅, from card_eq_zero,
          have ne_nat: |Y ∩ Z| ≠ 0, from
            λ h: |Y ∩ Z| = 0,
            hxy ((iff.elim_left card_zero) h),
          have le: 0 ≤ (|Y ∩ Z|:ℝ), from card_inter_nonneg Y Z,
          have ne: 0 ≠ (|Y ∩ Z|:ℝ), begin norm_cast,exact ne_nat.symm, end,
          calc 0 < (|Y ∩ Z|:ℝ): (iff.elim_right lt_iff_le_and_ne) (and.intro le ne)
            ... = ayz      : by rw[inter_comm]
            ... = ayz +  0 : by rw[add_zero]
            ... ≤ ayz + dyz: add_le_add_left (delta_nonneg (le_of_lt hm) hM) ayz
    )


lemma four_immediate_from (m M : ℝ) (X Y Z : finset α)
  (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M)
  (hx: X ≠ ∅) (hz: Z ≠ ∅):
  let axy := (|X ∩ Y|:ℝ), dxz := δ m M X Z, dyz := δ m M Z Y,
      axz := (|X ∩ Z|:ℝ), denom := axy+dxz+dyz in

  dxz/denom ≤ dxz/(axz + dxz) :=

  let dxy := (δ m M X Y), axy := (|X ∩ Y|:ℝ), dxz := δ m M X Z,
    dyz :=  (δ m M Z Y), ayz := (|Z ∩ Y|:ℝ), axz := (|X ∩ Z|:ℝ),
    y_z : ℕ := (Y \ Z).card, z_y : ℕ := (Z \ Y).card,x_z : ℕ := (X \ Z).card,
    z_x : ℕ := (Z \ X).card, xy : ℕ := (X ∩ Y).card,
    xz : ℕ := (X ∩ Z).card,  yz : ℕ := (Y ∩ Z).card,
    mini := (min (|Z \ Y|) (|Y \ Z|) : ℝ), maxi := (max (|Z \ Y|) (|Y \ Z|) : ℝ),
    denom := (axy+dxz+dyz)
  in
  have twelve_end_real: (xz:ℝ) ≤ (xy:ℝ) + max (|Z \ Y| : ℝ) (|Y \ Z| : ℝ), from
    have ddd: xz ≤ xy + max ((Z \ Y).card) ((Y \ Z).card), from twelve_end X Y Z,
    begin norm_cast,exact ddd, end,
  have max_nonneg_real: 0 ≤ (max (|Z \ Y|) (|Y \ Z|) : ℝ), from
    have 0 ≤ max z_y y_z, from nat.zero_le (max z_y y_z),
    begin norm_cast, exact this,end,
  have min_nonneg_real: 0 ≤ (min (|Z \ Y|) (|Y \ Z|) : ℝ), from
    have 0 ≤ min z_y y_z, from nat.zero_le (min z_y y_z),
    begin norm_cast, exact this,end,
  have mmin_nonneg : 0 ≤ m * mini, from mul_nonneg (le_of_lt hm) min_nonneg_real, 
  have use_h1M: 1 * maxi ≤ M * maxi, from mul_le_mul_of_nonneg_right h1M max_nonneg_real,
  have four_would_follow_from : axz ≤ axy + dyz, from calc
      axz ≤ (xy:ℝ) +     maxi             : twelve_end_real
      ... = (xy:ℝ) + 1 * maxi             : by ring
      ... ≤ (xy:ℝ) + M * maxi             : add_le_add_left use_h1M (xy:ℝ)
      ... = (xy:ℝ) + M * maxi + 0         : by rw[add_zero]
      ... ≤ (xy:ℝ) + M * maxi + m * mini  : add_le_add_left mmin_nonneg ((xy:ℝ) + M * maxi)
      ... = (xy:ℝ) + (M * (max (|Z \ Y|) (|Y \ Z|) : ℝ) + m * (min (|Z \ Y|) (|Y \ Z|) : ℝ)):
        by rw[add_assoc]
      ... = (|X ∩ Y|:ℝ)    + (δ m M Z Y): begin norm_cast, end,
  have le_denom:(axz + dxz) ≤ denom, from
      calc axz + dxz ≤ axy + dyz + dxz : add_le_add_right four_would_follow_from dxz
                  ... = axy + dxz + dyz : by ring,
  have denom_pos : 0 < (axz + dxz), from intersect_cases m M Z X hm hM hz hx,
  have d_nonneg: 0 ≤ dxz, from delta_nonneg (le_of_lt hm) hM,
  div_le_div_of_le_left d_nonneg denom_pos le_denom

 lemma four_immediate_from_and  (m M : ℝ) (X Y Z : finset α)
  (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M)
  (hy: Y ≠ ∅) (hz: Z ≠ ∅):
  (δ m M Z Y)/((|X ∩ Y|:ℝ) + δ m M X Z + δ m M Z Y) ≤ (δ m M Z Y)/((|Z ∩ Y|:ℝ) + δ m M Z Y) :=
  
  let dzy := δ m M Z Y, dyz := δ m M Y Z, dxz := δ m M X Z, dzx := δ m M Z X in
  have S: (dyz) / ((|Y ∩ X|:ℝ) + (dyz) + (dzx)) ≤ (dyz) / ((|Y ∩ Z|:ℝ) + dyz), from
    four_immediate_from m M Y X Z hm hM h1M hy hz,
  have dzy_comm: dzy = dyz, from delta_comm,
  have dxz_comm: dxz = dzx, from delta_comm,
  have ring_in_denom: (|Y ∩ X|:ℝ) + dzx + dyz = (|Y ∩ X|:ℝ) + dyz + dzx, by ring,
  calc   dzy / ((|X ∩ Y|:ℝ) + dxz + dzy)
       = dyz / ((|Y ∩ X|:ℝ) + dyz + dzx) : by rw[inter_comm,dxz_comm,dzy_comm,ring_in_denom]
   ... ≤ dyz / ((|Y ∩ Z|:ℝ) + dyz)       : S
   ... = dzy / ((|Z ∩ Y|:ℝ) + dzy)       : by rw[inter_comm,dzy_comm]



lemma mul_le_mul_rt {a b c : ℝ} (h : 0 ≤ c) : a ≤ b → a * c ≤ b * c :=
(em (0 = c)).elim(
  λ h0: 0 = c,
  λ hab: a ≤ b,
  calc a* c = a * 0: by rw h0
  ... = 0: mul_zero a
  ... ≤ 0: le_refl 0
  ... = b * 0: by rw[mul_zero b]
  ... = b * c: by rw h0
)(
  λ h0: 0 ≠ c,
  λ hab: a ≤ b,
  have h1: 0 < c, from (iff.elim_right lt_iff_le_and_ne) (and.intro h h0),
  (iff.elim_right (mul_le_mul_right h1)) hab
)

lemma abc_lemma {a b c : ℝ} (h : 0 ≤ a) (hb : a ≤ b) (hc : 0 ≤ c) : (a/(a+c)) ≤ (b/(b+c)) := 

(em (0 = a)).elim(
  λ ha: 0 = a,
  (em (0 = b)).elim(
    λ hhb: 0 = b, -- a=b=0
        calc  a/(a+c)
            = 0/(0+c): by rw ha
        ... ≤ 0/(0+c): le_refl (0/(0+c))
        ... = b/(b+c): by rw hhb
  )(
    λ hhb: 0 ≠ b, -- a=0, b ≠ 0
      have g0: 0 ≤ b, from (le_trans h hb),
      have g: 0 ≤ b + c, from add_nonneg g0 hc,
        calc  a/(a+c)
            = 0/(a+c): by rw ha
        ... = 0: by rw zero_div
        ... ≤ b/(b+c): div_nonneg g0 g
  )
)(
  λ hh: 0 ≠ a, -- then, since a ≤ b, b ≠ 0 as well
        have ha: 0 < a, from (iff.elim_right lt_iff_le_and_ne) (and.intro h hh),
        have numer : a*(b+c) ≤ b*(a+c), from calc
          a*(b+c) = a*b + a*c : by rw left_distrib
              ... ≤ a*b + b*c : add_le_add_left (mul_le_mul_rt hc hb) (a*b)
              ... = b * (a+c) : by ring, 
        have h6 : 0 < a+c, from lt_add_of_pos_of_le ha hc,
        have h7 : 0 < b+c, from lt_add_of_pos_of_le (has_lt.lt.trans_le ha hb) hc,
        (iff.elim_right (div_le_div_iff h6 h7)) numer
  )

theorem three (X Y Z : finset ℕ) (hm: 0 < m) (hM: m ≤ M):
let axy := (|X ∩ Y| : ℝ), dxy := δ m M X Y, dxz := δ m M X Z,
    dyz := δ m M Z Y, denom := (axy+dxz+dyz) in

  dxy/(axy + dxy) ≤ (dxz+dyz)/denom :=

let axy := (|X ∩ Y| : ℝ), dxy := δ m M X Y, dxz := δ m M X Z, dzy := δ m M Y Z, dyz := δ m M Z Y,
    axy := (|X ∩ Y| : ℝ), denom := (axy+dxz+dyz) in

  have hd : 0 ≤ δ m M X Y, from delta_nonneg (le_of_lt hm) hM,
  have h0 : δ m M Z Y = δ m M Y Z , by rw delta_comm,
  have h1 : dxy ≤ dxz + dzy, from calc
    dxy ≤ dxz + δ m M Z Y: delta_triangle X Z Y hm hM
    ... = dxz + δ m M Y Z: by {rw h0,},
  have h2: dxz + dyz + axy = axy + dxz + dyz, by ring,
    calc  dxy / (axy + dxy)
        = dxy / (dxy + axy)                           : by rw add_comm axy dxy
    ... ≤ (dxz + δ m M Y Z) / (dxz + dzy + axy)       : abc_lemma hd h1 (card_inter_nonneg X Y)
    ... = (dxz + δ m M Z Y) / (dxz + δ m M Z Y + axy) : by rw h0
    ... = (dxz + δ m M Z Y) / (axy + dxz + δ m M Z Y) : by rw h2


 theorem jn_triangle_nonempty
  (m M : ℝ) (X Y Z : finset ℕ) (hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M)
  (hx: X ≠ ∅) (hy: Y ≠ ∅) (hz: Z ≠ ∅): D m M X Y ≤ D m M X Z + D m M Z Y :=
  let dxy := (δ m M X Y), axy := (|X ∩ Y|:ℝ), dxz := δ m M X Z,
    dyz :=  (δ m M Z Y), ayz := (|Z ∩ Y|:ℝ), axz := (|X ∩ Z|:ℝ),
    denom := (axy+dxz+dyz)
  in
    have hzM: 0 < M, from calc
             0 < m: hm
           ... ≤ M: hM,
    have three: dxy/(axy + dxy) ≤ (dxz+dyz)/denom, from three X Y Z hm hM,
    have four: (dxz+dyz)/denom ≤ dxz/(axz + dxz) + dyz/(ayz + dyz), from calc
    (dxz+dyz)/denom = dxz/denom + dyz/denom: add_div dxz dyz denom
                ... ≤ dxz/(axz + dxz)   + dyz/denom:
                add_le_add_right
                (four_immediate_from m M X Y Z hm hM h1M hx hz)
                ((dyz)/denom)
                ... ≤ dxz/(axz + dxz)   + dyz/(ayz + dyz)  :
                add_le_add_left
                (four_immediate_from_and m M X Y Z hm hM h1M hy hz)
                (dxz/(axz + dxz)),
    le_trans three four

theorem jn_triangle (m M : ℝ) (X Y Z : finset ℕ)
(hm: 0 < m) (hM: m ≤ M) (h1M: 1 ≤ M): D m M X Y ≤ D m M X Z + D m M Z Y :=
let dxz := D m M X Z in
    (em (X=∅)).elim(
        λ hx: X = ∅,
        (em (Y=∅)).elim(
            λ hy: Y = ∅,
            have h1: X = Y, from eq.trans hx hy.symm, calc
            D m M X Y = D m M X X          : by rw[h1]
                  ... = 0                     : jn_self X
                  ... ≤             D m M Z Y : D_nonneg Z Y (le_of_lt hm) hM
                  ... = 0         + D m M Z Y : eq.symm (zero_add (D m M Z Y))
                  ... ≤ D m M X Z + D m M Z Y :
                  add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) (D m M Z Y)
        )(
            λ hy: Y ≠ ∅,
            (em (Z = ∅)).elim(
                λ hz: Z = ∅, -- 010 non Y nonempty
                have h3: D m M Z Y = 1, from D_empty_1 m M hm hM hz hy,
                calc D m M X Y =             1: D_empty_1 m M hm hM hx hy
                        ... = 0         + 1: by rw[zero_add]
                        ... ≤ D m M X Z + 1: add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) 1
                        ... = D m M X Z + D m M Z Y: by rw[h3]
            )(
                λ hz: Z ≠ ∅, -- 011 only X empty
                have h1: D m M X Y = 1, from D_empty_1 m M hm hM hx hy,
                have h2: D m M X Z = 1, from D_empty_1 m M hm hM hx hz,
                calc D m M X Y = 1: h1
                        ... = 1 + 0: by rw[add_zero]
                        ... ≤ 1 + D m M Z Y: add_le_add_left (D_nonneg Z Y (le_of_lt hm) hM) 1
                        ... = D m M X Z + D m M Z Y: by rw[h2]
            )
        )    
    )(
      λ hx: X ≠ ∅,
      (em (Y=∅)).elim(
        λ hy: Y = ∅,
        (em (Z = ∅)).elim(
          λ hz: Z = ∅, -- 100 only X nonempty
          calc D m M X Y =     1                  : D_empty_2 m M hm hM hx hy
                     ... =     1     +      0     : by rw[add_zero]
                     ... ≤     1     +  D m M Z Y : add_le_add_left (D_nonneg Z Y (le_of_lt hm) hM) 1
                     ... = D m M X Z +  D m M Z Y : by rw[D_empty_2 m M hm hM hx hz]
        )(
          λ hz: Z ≠ ∅, -- 101 only Y empty
          calc D m M X Y =                 1    : D_empty_2 m M hm hM hx hy
                     ... =     0     +     1    : by rw[zero_add]
                     ... ≤ D m M X Z +     1    : add_le_add_right (D_nonneg X Z (le_of_lt hm) hM) 1
                     ... = D m M X Z + D m M Z Y : by rw[D_empty_2 m M hm hM hz hy]
        )
      )(
        λ hy: Y ≠ ∅,
        (em (Z = ∅)).elim(
          λ hz: Z = ∅, -- 110 only Z is empty
          have h2: D m M X Z = 1, from D_empty_2 m M hm hM hx hz,
          have h3: D m M Z Y = 1, from D_empty_1 m M hm hM hz hy,
          calc D m M X Y ≤             1: D_bounded m M X Y (le_of_lt hm) hM
                     ... =         0 + 1: by rw[zero_add]
                     ... ≤         1 + 1: add_le_add_right zero_le_one 1
                     ... = D m M X Z + D m M Z Y: by rw[h2,h3]
        )(
            λ hz: Z ≠ ∅, -- 111
            jn_triangle_nonempty m M X Y Z hm hM h1M hx hy hz
        )
      )
    )

noncomputable instance jaccard_nid.metric_space
(hm : 0 < m) (hM : m ≤ M) (h1M: 1 ≤ M): metric_space (finset ℕ) := {
        dist               := λx y, D m M x y,
        dist_self          := jn_self,
        eq_of_dist_eq_zero := eq_of_jn_eq_zero hm hM,
        dist_comm          := λ x y, jn_comm x y,
        dist_triangle      := λ x z y, jn_triangle m M x y z hm hM h1M
    }

noncomputable def J : finset α → (finset α → ℝ) :=
  λ x y, (δ 1 1 x y) / ((|x ∩ y|:ℝ) + δ 1 1 x y)

--Easy but not done yet:
--theorem J_characterization (X Y : finset α):
--J X Y = ((|X \ Y|) + (|Y \ X|)) / (|X ∪ Y|) :=
--let dxy := (1:ℝ) * (max (|X \ Y|) (|Y \ X|):ℝ) + (1:ℝ) * (min (|X \ Y|) (|Y \ X|):ℝ) in
--calc dxy / ((|X ∩ Y|:ℝ) + dxy) = ((|X \ Y|) + (|Y \ X|)) / (|X ∪ Y|): sorry

noncomputable instance jaccard.metric_space
(hm : (0:ℝ) < (1:ℝ)) (hM : (1:ℝ) ≤ (1:ℝ)) (h1M: (1:ℝ) ≤ (1:ℝ)): metric_space (finset ℕ) := {
        dist               := λx y, D 1 1 x y,
        dist_self          := jn_self,
        eq_of_dist_eq_zero := eq_of_jn_eq_zero hm hM,
        dist_comm          := λ x y, jn_comm x y,
        dist_triangle      := λ x z y, jn_triangle 1 1 x y z hm hM h1M
    }

end jaccard_nid
