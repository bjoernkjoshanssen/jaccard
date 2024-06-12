/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bjørn Kjos-Hanssen.
Zulip chat help from:
Johan Commelin, Kyle Miller, Pedro Minicz, Reid Barton, Scott Morrison, Heather Macbeth.
This is a Lean 4 version of the 2020 project.
-/
-- import tactic.ring2
-- import data.Finset  -- finite set
-- import data.set -- to make backslash work as set difference
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
-- import data.real.basic

/-!
# A theorem on metrics based on min and max

In this file we give a formal proof of Theorem 17 from [KNYHLM20].
It asserts that d(X,Y)= m min(|X\Y|, |Y\X|) + M max(|X\Y|, |Y\X|) is a metric
if and only if m ≤ M.

## Main results

- `seventeen`: the proof of Theorem 17.
- `instance jaccard_numerator.metric_space`: the realization as a `metric_space` type.

## Notation

 - `|_|` : Notation for cardinality.

## References

See [KNYHLM20] for the original proof.
-/

open Finset

notation "|" X "|" => Finset.card X

-- -- Kyle Miller (start) although proofs of disj1, disj2 due to K-H

-- variable {α : Type*} [DecidableEq α]

lemma disj₁ {α : Type*} [DecidableEq α] (X Y Z : Finset α) : Disjoint ((X \ Y) ∪ (Y \ Z)) (Z \ X) := by
  rw [disjoint_iff];ext;simp;tauto

lemma disj₂ {α : Type*} [DecidableEq α] (X Y Z : Finset α) : Disjoint (X \ Y) (Y \ Z) := by
  rw [disjoint_iff];ext;simp;tauto

lemma union_rot_sdiff {α : Type*} [DecidableEq α] (X Y Z : Finset α) :
    (X \ Y) ∪ (Y \ Z) ∪ (Z \ X) = (X \ Z) ∪ (Z \ Y) ∪ (Y \ X) := by
  ext; simp only [union_assoc, mem_union, mem_sdiff];tauto


lemma card_rot {α : Type*} [DecidableEq α] (X Y Z : Finset α) : |X \ Y| + |Y \ Z| + |Z \ X| = |X \ Z| + |Z \ Y| + |Y \ X| := by
  let key := congrArg Finset.card (union_rot_sdiff X Y Z)
  rwa [
      card_union_of_disjoint (disj₁ X Y Z), card_union_of_disjoint (disj₁ X Z Y),
      card_union_of_disjoint (disj₂ X Y Z), card_union_of_disjoint (disj₂ X Z Y)
  ] at key

-- -- Kyle Miller (end)

lemma card_rot_cast {α : Type*} [DecidableEq α] (X Y Z : Finset α) : ((|X\Y| + |Y\Z| + |Z\X|):ℝ) = ((|X\Z| + |Z\Y| + |Y\X|):ℝ) := by
    have : |X\Y| + |Y\Z| + |Z\X| = |X\Z| + |Z\Y| + |Y\X|:= card_rot X Y Z
    norm_cast


-- variable {m M : ℝ}

noncomputable def δ {α : Type*} [DecidableEq α] : ℝ → ℝ → Finset α → (Finset α → ℝ) :=
    λ m M A B ↦ M *  ((max (|A\B| : ℝ) |B\A|)) + m *  (min (|A\B|) (|B\A|))

theorem delta_cast {α : Type*} [DecidableEq α] {m M:ℝ} {A B : Finset α} :
    δ m M A B = M * (max ↑(|A\B|) ↑(|B\A|)) + m * (min ↑(|A\B|) ↑(|B\A|)) := by
      unfold δ
      norm_cast

theorem delta_comm {α : Type*} [DecidableEq α] {m M : ℝ} (A B : Finset α): δ m M A B = δ m M B A := by
    unfold δ;rw[max_comm,min_comm]

theorem delta_self {α : Type*} [DecidableEq α] (X : Finset α): δ m M X X = 0 := by unfold δ;simp

lemma subseteq_of_card_zero {α : Type*} [DecidableEq α] (x y : Finset α) : |x \ y| = 0 → x ⊆ y := by
  intro h;simp at h;tauto

lemma card_zero_of_not_pos {α : Type*} [DecidableEq α] (X : Finset α) : ¬ 0 < |X| → |X| = 0 := by
  intro h;simp at h;rw [h];simp

lemma eq_zero_of_nonneg_of_nonneg_of_add_zero {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 = a + b → 0 = a := by
  intro h₀ h₁ h₂
  have : ¬ 0 < a := by
    intro hc
    have h₃: 0 < a + b := lt_add_of_lt_of_nonneg hc h₁
    rw [← h₂] at h₃
    exact (lt_self_iff_false 0).mp h₃
  apply eq_iff_le_not_lt.mpr
  tauto


theorem subset_of_delta_eq_zero {α : Type*} [DecidableEq α] (hm: 0 < m) (hM: m ≤ M) (X Y : Finset α) (h: δ m M X Y = 0) :
  X ⊆ Y := by
  unfold δ at h
  simp at h
  let x_y := |X \ Y|
  let y_x := |Y \ X|
  have δ_0: 0 = M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ) := by
    symm;norm_cast;simp;exact h
  have not_pos_δ: ¬ 0 < M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ) := by
    apply not_lt_iff_eq_or_lt.mpr;left;tauto
  have min_nonneg: 0 ≤ ((min x_y y_x):ℝ) := by
    norm_cast; exact (le_min (Nat.zero_le x_y) (Nat.zero_le y_x))
  have M_pos: 0 < M := calc
              0 < m := hm
              _ ≤ M := hM
  have pos_δ_of_pos_x: 0 < x_y → 0 < M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ):=
      λ h: 0 < x_y ↦
      have strict_x: 0 <  (max x_y y_x):= by apply lt_max_iff.mpr; tauto
      have cast_x  : 0 <  ((max x_y y_x):ℝ):= by norm_cast
      have Mx_pos  : 0 < (M * ((max x_y y_x):ℝ)):=
        mul_pos M_pos cast_x
      lt_add_of_lt_of_nonneg Mx_pos (mul_nonneg (le_of_lt hm) min_nonneg)
  have r0: ¬ 0 < x_y:= λ pos_x ↦ not_pos_δ (pos_δ_of_pos_x pos_x)
  exact subseteq_of_card_zero X Y (card_zero_of_not_pos (X\Y) r0)

 theorem eq_of_delta_eq_zero {α : Type*} [DecidableEq α] (hm: 0 < m) (hM: m ≤ M) (X Y : Finset α) (h: δ m M X Y = 0) :
 X = Y := by
  have g0: X ⊆ Y:= subset_of_delta_eq_zero hm hM X Y h
  have g: δ m M Y X = 0:= calc
    δ m M Y X = δ m M X Y := by rw[delta_comm]
    _         = 0 := h
  have g1: Y ⊆ X:= subset_of_delta_eq_zero hm hM Y X g
  exact Subset.antisymm g0 g1
-- -- UPDATED TO HERE


theorem sdiff_covering {α : Type*} [DecidableEq α] {A B C : Finset α}: A\C ⊆ (A\B) ∪ (B\C) := sdiff_triangle A B C

theorem sdiff_triangle' {α : Type*} [DecidableEq α] (A B C: Finset α): |A\C| ≤ |A\B| + |B\C| :=
    calc |A\C| ≤ |A\B  ∪ B\C| := Finset.card_le_card (sdiff_covering)
    _ = |A\B| + |B\C| := by rw [Finset.card_union_of_disjoint (disj₂ A B C)]

lemma venn {α : Type*} [DecidableEq α] (X Y : Finset α): X = X\Y ∪ (X ∩ Y) := by ext; simp; tauto

lemma venn_card {α : Type*} [DecidableEq α] (X Y : Finset α): |X| = |X\Y| + |X ∩ Y| := by
    have h: Disjoint (X\Y) (X ∩ Y):= disjoint_sdiff_inter X Y
    exact calc
    |X| = |X \ Y  ∪  X ∩ Y| := by rw [← (venn X Y)]
    _ = |X \ Y| + |X ∩ Y| := Finset.card_union_of_disjoint h


lemma sdiff_card {α : Type*} [DecidableEq α] (X Y : Finset α): |Y| ≤ |X| → |Y\X| ≤ |X\Y| := by
    intro h
    have h₀: |Y\X| + |Y ∩ X| ≤ |X\Y| + |X ∩ Y|:= by
            rw [venn_card X Y] at h
            rw [venn_card Y X] at h
            exact h
    have h₁: Y ∩ X = X ∩ Y:= inter_comm _ _
    have h₂: |Y ∩ X| = |X ∩ Y|:= by rw [h₁]
    have h₃: |Y\X| + |X ∩ Y| ≤ |X\Y| + |X ∩ Y|:= by
        rw [h₂] at h₀; exact h₀
    exact le_of_add_le_add_right h₃

    lemma maxmin_1 {α : Type*} [DecidableEq α] {X Y : Finset α}: |X| ≤ |Y| → δ m M X Y = M * |Y\X| + m * |X\Y| := by
      intro h₁
      have h₂: |X\Y| ≤ |Y\X|:= sdiff_card Y X h₁
      unfold δ
      rw [max_eq_right]
      rw [min_eq_left]
      tauto
      norm_cast

lemma maxmin_2 {α : Type*} [DecidableEq α] {X Y : Finset α}: |Y| ≤ |X| → δ m M X Y = M * |X\Y| + m * |Y\X| := by
    rw [delta_comm];apply maxmin_1

theorem casting {a b : ℕ}: a ≤ b → (a:ℝ) ≤ (b:ℝ) := by
    norm_cast; tauto

theorem mul_sdiff_tri {α : Type*} [DecidableEq α] (m : ℝ) (hm: 0 ≤ m) (X Y Z : Finset α):
    m * ↑ |X\Z| ≤ m * (↑ |X\Y| + ↑ |Y\Z|) := by
    calc m * ↑ (|X\Z|) ≤ m * ↑ ((|X\Y|) + (|Y\Z|)) := mul_le_mul_of_nonneg_left (casting (sdiff_triangle' X Y Z)) hm
    _ = m * ((|X\Y|:ℝ) + (|Y\Z|:ℝ)):= by norm_cast

def triangle_inequality {α : Type*} [DecidableEq α] (m M :ℝ) (X Y Z: Finset α) : Prop :=
    δ m M X Y ≤ δ m M X Z + δ m M Z Y

lemma seventeen_right_yzx {α : Type*} [DecidableEq α] {m M :ℝ} {X Y Z: Finset α} :
    0 ≤ m → m ≤ M → |Y| ≤ |Z| ∧ |Z| ≤ |X| → triangle_inequality m M X Y Z
    := by
    let x := |X|
    let y := |Y|
    let z := |Z|
    let x_z := |X\Z|
    let z_x := |Z\X|
    let y_z := |Y\Z|
    let z_y := |Z\Y|
    let x_y := |X\Y|
    let y_x := |Y\X|
    intro hm h h₀
    have hM : 0 ≤ M:= le_trans hm h
    have h₂: y ≤ z:= by tauto
    have h₃: z ≤ x:= by tauto
    have h₁: y ≤ x:= le_trans h₂ h₃
    have dxz: δ m M X Z = M * (x_z) + m * (z_x):= maxmin_2 h₃
    have dzy: δ m M Z Y = M * (z_y) + m * (y_z):= maxmin_2 h₂--used implicitly by a tactic

    have mst_yzx: m* ↑ (|Y\X|) ≤ m *  (↑ (y_z) + ↑ (z_x)):=
        mul_sdiff_tri m hm Y Z X
    have mst_xzy: M* ↑ (x_y) ≤ M *  (↑ (x_z) + ↑ (z_y)):=
        mul_sdiff_tri M hM X Z Y
    calc
    δ m M X Y = M * (x_y) + m * (|Y\X|)                 := by exact maxmin_2 h₁
          _ ≤ M * (x_y) + m * ((y_z) + (z_x))           := add_le_add_left mst_yzx (M * (x_y))
          _ ≤ M * (x_z + z_y) + m * (y_z + z_x)         := add_le_add_right mst_xzy (m * ((y_z) + (z_x)))
          _ = (M * x_z + m * z_x) + (M * z_y + m * y_z) := by ring
          _ = δ m M X Z                     + δ m M Z Y := by rw[dxz,dzy]

lemma co_sdiff {α : Type*} [DecidableEq α] (X Y U : Finset α):
X ⊆ U → Y ⊆ U → (U\X)\(U\Y) = Y\X := by exact fun _ a ↦ sdiff_sdiff_sdiff_cancel_left a

lemma co_sdiff_card {α : Type*} [DecidableEq α] (X Y U : Finset α):
X ⊆ U → Y ⊆ U → ((U\X)\(U\Y)).card = (Y\X).card :=
    λ hx: X ⊆ U ↦ λ hy: Y ⊆ U ↦ by
      rw [co_sdiff X Y U]
      exact hx
      exact hy

lemma co_sdiff_card_max {α : Type*} [DecidableEq α] (X Y U : Finset α):
X ⊆ U → Y ⊆ U → max (|(U\Y)\(U\X)|) (|(U\X)\(U\Y)|) = max (|X\Y|) (|Y\X|) :=
    λ hx: X ⊆ U ↦ λ hy: Y ⊆ U ↦ by
    rw[co_sdiff_card X Y U hx hy,co_sdiff_card Y X U hy hx]

lemma co_sdiff_card_min {α : Type*} [DecidableEq α] (X Y U : Finset α):
X ⊆ U → Y ⊆ U → min (|(U\Y)\(U\X)|) (|(U\X)\(U\Y)|) = min (|X\Y|) (|Y\X|) :=
    λ hx hy ↦
    by rw[co_sdiff_card X Y U hx hy,co_sdiff_card Y X U hy hx]

theorem delta_complement {α : Type*} [DecidableEq α] (X Y U : Finset α):
    X ⊆ U → Y ⊆ U → δ m M X Y = δ m M (U\Y) (U\X) :=
    λ hx hy ↦ by
      let Y' := U\Y
      let X' := U\X
      have co1: |X'\Y'| = |Y\X|:= co_sdiff_card X Y U hx hy
      have co2: |Y'\X'| = |X\Y|:= co_sdiff_card Y X U hy hx
      have co3: max (|Y'\X'|) (|X'\Y'|) = max (|X\Y|) (|Y\X|):=
          co_sdiff_card_max X Y U hx hy
      have co4: min (|Y'\X'|) (|X'\Y'|) = min (|X\Y|) (|Y\X|):=
          co_sdiff_card_min X Y U hx hy
      have defi: δ m M Y' X' = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|Y'\X'|) (|X'\Y'|)) := by
        unfold δ;rw [co1,co2,];norm_cast
      calc δ m M X Y = M * ↑ (max (|X\Y|) (|Y\X|)) + m * ↑ (min (|X\Y|) (|Y\X|)) := by
            unfold δ
            norm_cast
      _ = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|X\Y|) (|Y\X|)):= by rw [co3]
      _ = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|Y'\X'|) (|X'\Y'|)) := by rw [co4]
      _ =  δ m M Y' X' := by rw [defi]


theorem seventeen_right_yxz {α : Type*} [DecidableEq α] {m M : ℝ} {X Y Z : Finset α}:
    0 ≤ m → m ≤ M → |Y| ≤ |X| ∧ |X| ≤ |Z| → triangle_inequality m M X Y Z := by
    let x := |X|
    let y := |Y|
    let z := |Z|
    let x_z := |X\Z|
    let z_x := |Z\X|
    let y_z := |Y\Z|
    let z_y := |Z\Y|
    let x_y := |X\Y|
    let y_x := |Y\X|
    intro hm h h₀
    have hyz: y ≤ z:= le_trans h₀.1 h₀.2
    have gxz: x_z ≤ z_x:= sdiff_card Z X (h₀.2)
    have gyz: y_z ≤ z_y:= sdiff_card Z Y hyz
    have dxy: δ m M X Y = M * x_y + m * y_x:= maxmin_2 (h₀.1)
    have dzy: δ m M Z Y = M * z_y + m * y_z:= maxmin_2 hyz
    have dxz: δ m M X Z = M * z_x + m * x_z:= calc
                δ m M X Z = δ m M Z X                 := delta_comm _ _
                _ = M * (z_x) + m * (x_z) := maxmin_2 (h₀.2)
    have Mmpos: M-m ≥ 0:=
      calc M - m  ≥ m - m := sub_le_sub_right h _
      _ = 0 := sub_self _
    have h02: 0 ≤ (2:ℝ):= by norm_cast
    have h2m: 0 ≤ 2*m:= mul_nonneg h02 hm
    have tri_1:   2 * m * y_x ≤ 2 * m * (y_z + z_x):= mul_sdiff_tri (2*m) h2m Y Z X
    have tri_2: (M-m) * x_y ≤ (M-m) * (x_z + z_y):= mul_sdiff_tri (M-m) Mmpos X Z Y

    have tri_3:  (M-m) * x_z ≤ (M-m) * z_x:= mul_le_mul_of_nonneg_left (casting (gxz)) Mmpos
    have triangle_add: (δ m M X Y) + (m * y_x) ≤ (δ m M X Z + δ m M Z Y) + (m * y_x):= by
        let term_1 := (M * x_y)
        let term_2 := (m*(x_z+z_y+y_x) + m*(y_z+z_x))
        let term_3 := (m*(x_z +z_y +y_x) + (M-m) * z_y + m*z_x + m*y_z)
        calc   (δ m M X Y)     + (m * y_x)
            = (M * x_y + m * y_x) + (m * y_x)                           := by rw [dxy]
        _ = M * x_y + 2 * m * y_x                                       := by ring
        _ ≤ M * x_y + 2 * m * (y_z+z_x)                                 := add_le_add_left tri_1 term_1
        _ = m*(x_y+y_z+z_x) + m*(y_z+z_x) + (M-m)*x_y                   := by ring
        _ = m*(x_z+z_y+y_x) + m*(y_z+z_x) + (M-m)*x_y                   := by rw [card_rot_cast]
        _ ≤ m*(x_z+z_y+y_x) + m*(y_z+z_x) + (M-m)*(x_z+ z_y)            := add_le_add_left tri_2 term_2
        _ = m*(x_z+z_y+y_x) + (M-m) * z_y + m*z_x + m*y_z + (M-m) * x_z := by ring
        _ ≤ m*(x_z+z_y+y_x) + (M-m) * z_y + m*z_x + m*y_z + (M-m) * z_x := add_le_add_left tri_3 term_3
        _ = (M * z_x + m * x_z)        + (M * z_y + m * y_z) + (m * y_x):= by ring
        _ = (δ m M X Z                 +          δ m M Z Y) + (m * y_x):= by rw[dxz,dzy]
    exact le_of_add_le_add_right triangle_add

lemma sdiff_card_le {α : Type*} [DecidableEq α] (X Y U : Finset α) (hx: X ⊆ U) (hy: Y ⊆ U) (h:|X| ≤ |Y|):
    |U \ Y| ≤ |U \ X| := by
    have hu: |U| - |Y| ≤ |U| - |X| := Nat.sub_le_sub_left h _
    calc
        |U \ Y| = |U| - |Y| := card_sdiff hy
        _ ≤ |U| - |X| := hu
        _ = |U \ X|   := by rw[card_sdiff hx]

theorem seventeen_right_zyx {α : Type*} [DecidableEq α] {m M : ℝ} {X Y Z : Finset α}:
    0 ≤ m → m ≤ M → |Z| ≤ |Y| ∧ |Y| ≤ |X| → triangle_inequality m M X Y Z := by
    intro hm hM h
    let U := X ∪ Y ∪ Z
    let Z' : Finset α := (X ∪ Y ∪ Z) \ Z
    let Y' : Finset α := (X ∪ Y ∪ Z) \ Y
    let X' : Finset α := (X ∪ Y ∪ Z) \ X
    have hx: X ⊆ U:= by intro a ha;show a ∈ X ∪ Y ∪ Z;simp;tauto

    have hy: Y ⊆ U:= by intro a ha;show a ∈ X ∪ Y ∪ Z;simp;tauto
    have hz: Z ⊆ U:= by intro a ha;show a ∈ X ∪ Y ∪ Z;simp;tauto

    have and1: |X'| ≤ |Y'|:= sdiff_card_le Y X U hy hx h.right
    have and2: |Y'| ≤ |Z'|:= sdiff_card_le Z Y U hz hy h.left
    have hh: |X'| ≤ |Y'| ∧ |Y'| ≤ |Z'|:= by tauto
    have h1: δ m M X' Z' = δ m M Z X:= (delta_complement Z X U hz hx).symm
    have h2: δ m M Z' Y' = δ m M Y Z:= (delta_complement Y Z U hy hz).symm
    have h3: δ m M Y Z = δ m M Z Y:= delta_comm _ _
    calc δ m M X Y = δ m M Y' X'               := delta_complement X Y U hx hy
    _ ≤ δ m M Y' Z' + δ m M Z' X' := seventeen_right_yxz hm hM hh
    _ = δ m M X' Z' + δ m M Z' Y' := by rw[delta_comm,add_comm,delta_comm]
    _ = δ m M Z  X  + δ m M Z' Y' := by rw[h1]
    _ = δ m M X  Z  + δ m M Z' Y' := by rw[delta_comm]
    _ = δ m M X  Z  + δ m M Y  Z  := by rw[h2]
    _ = δ m M X  Z  + δ m M Z  Y  := by rw[h3]


theorem seventeen_right_zxy {α : Type*} [DecidableEq α] {X Y Z : Finset α}:
    0 ≤ m → m ≤ M → |Z| ≤ |X| ∧ |X| ≤ |Y| → triangle_inequality m M X Y Z := by
    intro hm h hyp
    calc
    δ m M X Y = δ m M Y X             := delta_comm _ _
    _ ≤ δ m M Y Z + δ m M Z X := seventeen_right_zyx hm h hyp
    _ = δ m M Z X + δ m M Y Z := add_comm (δ m M Y Z) (δ m M Z X)
    _ = δ m M X Z + δ m M Z Y := by rw[delta_comm,delta_comm Y Z]


theorem three_places {x y z : ℕ} :
    y ≤ x → (z ≤ y ∧ y ≤ x) ∨ (y ≤ z ∧ z ≤ x) ∨ (y ≤ x ∧ x ≤ z) := by
    intro hyx
    have := le_total z y
    have := le_total z x
    tauto

theorem seventeen_right_y_le_x {α : Type*} [DecidableEq α] {m M : ℝ} {X Y Z : Finset α} :
    |Y| ≤ |X| → 0 ≤ m → m ≤ M → triangle_inequality m M X Y Z := by
    let z := |Z|
    intro h hm hmM
    have := @three_places _ _ z h
    let R := @seventeen_right_zyx α _ m M X Y Z hm hmM --_  hm hmM
    let S := @seventeen_right_yxz α _ m M X Y Z hm hmM --_  hm hmM
    let T := @seventeen_right_yzx α _ m M X Y Z hm hmM --_  hm hmM
    tauto

theorem seventeen_right_x_le_y {α : Type*} [DecidableEq α] {m M : ℝ} {X Y Z : Finset α} :
    |X| ≤ |Y| → 0 ≤ m → m ≤ M → triangle_inequality m M X Y Z := by
    intro h hm hmM
    calc
    δ m M X Y = δ m M Y X := delta_comm _ _
    _ ≤ δ m M Y Z + δ m M Z X := seventeen_right_y_le_x h hm hmM
    _ = δ m M Z X + δ m M Y Z := add_comm (δ m M Y Z) (δ m M Z X)
    _ = δ m M X Z + δ m M Z Y:= by rw[delta_comm,delta_comm Y Z]


theorem seventeen_right {α : Type*} [DecidableEq α] {m M : ℝ} { X Y Z : Finset α}:
    0 ≤ m → m ≤ M → triangle_inequality m M X Y Z := by
    intro hm h
    cases (le_total (|X|) (|Y|)) with
    |inl h1 => exact seventeen_right_x_le_y h1 hm h
    |inr h1 => exact seventeen_right_y_le_x h1 hm h


def s_0 : Finset ℕ := {0}
def s_1 : Finset ℕ := {1}
def s01 : Finset ℕ := {0,1}

theorem seventeen:
    0 ≤ m → (m ≤ M ↔ ∀ X Y Z : Finset ℕ, triangle_inequality m M X Y Z) :=

    λ hm: 0 ≤ m ↦
    have h₀: m ≤ M → ∀ X Y Z : Finset ℕ, triangle_inequality m M X Y Z:=
        λ h: m ≤ M ↦ λ X Y Z ↦ seventeen_right hm h
    have h₁: (∀ X Y Z : Finset ℕ, triangle_inequality m M X Y Z) → m ≤ M:=
        λ hyp: (∀ X Y Z : Finset ℕ, triangle_inequality m M X Y Z) ↦
        have hh: δ m M {0} {1} ≤ δ m M {0} {0,1} + δ m M {0,1} {1}:= hyp {0} {1} {0,1}
        have : s_0\s_1 = {0} := by decide
        have : s_1\s_0 = {1} := by decide
        have : s_0\s01 =   ∅ := by decide
        have : s01\s_0 = {1} := by decide
        have : s_1\s01 =  ∅  := by decide
        have : s01\s_1 = {0} := by decide
        -- finish actually uses the unnamed hypotheses


        have cyxN: (|s_1\s_0|:Nat) = (1:Nat):= by decide
        -- have cxzN: (|s_0\s01|:Nat) = (0:Nat):= by decide,
        have czxN: (|s01\s_0|:Nat) = (1:Nat):= by decide
        have czyN: (|s01\s_1|:Nat) = (1:Nat):= by decide
        -- have cyzN: (|s_1\s01|:Nat) = (0:Nat):= by decide,
        have cxyN: (|s_0\s_1|:Nat) = (1:Nat):= by decide

        have cyx: (|s_1\s_0|:ℝ) = (1:ℝ) := by {norm_num;exact cyxN}
        have cxz: (|s_0\s01|:ℝ) = (0:ℝ) := by {norm_num;decide}
        have czx: (|s01\s_0|:ℝ) = (1:ℝ) := by {norm_num;exact czxN}
        have czy: (|s01\s_1|:ℝ) = (1:ℝ) := by {norm_num;exact czyN}
        have cyz: (|s_1\s01|:ℝ) = (0:ℝ) := by {norm_num;decide}
        have cxy: (|s_0\s_1|:ℝ) = (1:ℝ) := by {norm_num;exact cxyN}
        have dxy: δ m M s_0 s_1 = M + m := calc
            δ m M s_0 s_1 = M * max ↑(|s_0\s_1|) ↑(|s_1\s_0|)
                          + m * min ↑(|s_0\s_1|) ↑(|s_1\s_0|):= delta_cast
            _ = M * max    (1:ℝ)  (1:ℝ)   + m * min (1:ℝ) (1:ℝ) := by rw[cxy,cyx]
            _ = M + m := by simp
        have dxz: δ m M s_0 s01 = M:= calc
                  δ m M s_0 s01 = M * max (|s_0\s01|) (|s01\s_0|)
                                + m * min (|s_0\s01|) (|s01\s_0|) := by
                                rw [delta_cast]
                                norm_num
                  _ = M * max 0 1 + m * min 0 1 := by
                    norm_num;
                    rw[cxz,czx];norm_num
                  _ = M  := by simp
        have dzy: δ m M s01 s_1 = M:= calc
                  δ m M s01 s_1 = M * max (|s01\s_1|) (|s_1\s01|)
                                + m * min (|s01\s_1|) (|s_1\s01|) := by rw [delta_cast];norm_num
                  _ = M * max 1 0 + m * min (1) 0 := by
                    norm_num
                    rw [czy,cyz]
                    simp
                  _ = M  := by simp
        have add_le_add_left : M + m ≤ M + M:= calc
            M + m = δ m M s_0 s_1 := by rw[dxy]
            _ ≤  δ m M s_0 s01 + δ m M s01 s_1 := hh
            _ = M + M:= by rw[dxz,dzy]
        le_of_add_le_add_left
              add_le_add_left
    Iff.intro h₀ h₁

    def delta_triangle (X Y Z: Finset ℕ) (hm: 0 < m) (hM: m ≤ M):
    triangle_inequality m M X Z Y
    --δ m M X Y ≤ δ m M X Z + δ m M Z Y
    :=
    (seventeen (le_of_lt hm)).mp hM X Z Y

    -- section jaccard_numerator
    /-- Instantiate Finset ℕ as a metric space. -/

    -- def protein {m M : ℝ} (hm : 0 < m) (hM : m ≤ M) := Finset α


    noncomputable instance {m M : ℝ} (hm : 0 < m) (hM : m ≤ M) :
      MetricSpace (Finset ℕ) := {
        dist               := λ A B ↦ M *  ((max (|A\B| : ℝ) |B\A|)) + m *  (min (|A\B|) (|B\A|)),
        dist_self          := delta_self, -- have to give proof that d(x,x)=0
        eq_of_dist_eq_zero := eq_of_delta_eq_zero hm hM _ _, -- a_of_b_of_c means b → c → a
        dist_comm          := λ x y ↦ calc @δ ℕ _ m M x y = @δ ℕ _ m M y x := delta_comm _ _,
        dist_triangle      := λ x y z ↦ (((seventeen (le_of_lt hm))).mp hM) x z y
        edist_dist         := (λ x y ↦ by exact (ENNReal.ofReal_eq_coe_nnreal _).symm)
    }
-- end jaccard_numerator
