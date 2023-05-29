/-
Copyright (c) 2020 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bjørn Kjos-Hanssen.
Zulip chat help from:
Johan Commelin, Kyle Miller, Pedro Minicz, Reid Barton, Scott Morrison, Heather Macbeth.
-/
import tactic.ring2
import data.finset  -- finite set
import data.set -- to make backslash work as set difference
import data.finset.basic
import topology.metric_space.basic
 
import data.real.basic

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

open finset

local notation (name := X.card) |X| := X.card

-- Kyle Miller (start) although proofs of disj1, disj2 due to K-H

variables {α : Type*} [decidable_eq α]

lemma disj₁ (X Y Z : finset α) : disjoint ((X \ Y) ∪ (Y \ Z)) (Z \ X) := by { rw disjoint_iff, tidy}
lemma disj₂ (X Y Z : finset α) : disjoint (X \ Y) (Y \ Z) := by { rw disjoint_iff, tidy}

lemma union_rot_sdiff (X Y Z : finset α) :
    (X \ Y) ∪ (Y \ Z) ∪ (Z \ X) = (X \ Z) ∪ (Z \ Y) ∪ (Y \ X) :=
    by { tidy, by_cases h: a∈ Z,cc,cc,by_cases h:a ∈ X,cc,cc,by_cases h: a ∈ Y, cc, cc, 
    by_cases h: a ∈ Y, cc, cc, by_cases h: a ∈ X, cc, cc, by_cases h: a ∈ Z, cc, cc, 
    }
    --by { ext, simp only [mem_union, mem_sdiff, union_assoc], tauto! }

lemma card_rot (X Y Z : finset α) : |X \ Y| + |Y \ Z| + |Z \ X| = |X \ Z| + |Z \ Y| + |Y \ X| := by {
    have key := congr_arg card (union_rot_sdiff X Y Z),
    -- how is have := different from let := in?
    rwa [
        card_disjoint_union (disj₁ X Y Z), card_disjoint_union (disj₁ X Z Y),
        card_disjoint_union (disj₂ X Y Z), card_disjoint_union (disj₂ X Z Y)
    ] at key,
}

-- Kyle Miller (end)

lemma card_rot_cast (X Y Z : finset α) : ((|X\Y| + |Y\Z| + |Z\X|):ℝ) = ((|X\Z| + |Z\Y| + |Y\X|):ℝ) :=
    have |X\Y| + |Y\Z| + |Z\X| = |X\Z| + |Z\Y| + |Y\X|, from card_rot X Y Z,
    by { norm_cast,exact this }

variables {m M : ℝ}

def δ : ℝ → ℝ → finset α → (finset α → ℝ) :=
    λ m M A B, M * ↑ (max (|A\B|) (|B\A|)) + m * ↑ (min (|A\B|) (|B\A|))

theorem delta_cast {m M:ℝ} {A B : finset α} :
    δ m M A B = M * (max ↑(|A\B|) ↑(|B\A|)) + m * (min ↑(|A\B|) ↑(|B\A|)) := by norm_cast

theorem delta_comm {m M : ℝ} {A B : finset α}: δ m M A B = δ m M B A :=
    calc δ m M A B =
          M * max (|A\B|) (|B\A|) + m * min (|A\B|) (|B\A|): by {unfold δ,norm_cast,}
    ... = M * max (|B\A|) (|A\B|) + m * min (|B\A|) (|A\B|): by begin rw[max_comm,min_comm] end
    ... = δ m M B A: by {unfold δ,norm_cast,}


theorem delta_self (X : finset α): δ m M X X = 0 :=
    let x_x := |X \ X| in
    have used_by_finish: x_x = 0, from card_eq_zero.mpr (sdiff_self X),
    calc  δ m M X X = M * ((max x_x x_x):ℝ) + m * ((min x_x x_x):ℝ): by norm_cast
                ... = M * ((max 0 0):ℝ) + m * ((min 0 0):ℝ): by {repeat{rw used_by_finish},norm_cast,}
                ... = 0: by {rw max_self,rw min_self,rw mul_zero,rw mul_zero,rw add_zero,}
--#print delta_self
lemma subseteq_of_card_zero (x y : finset α) : |x \ y| = 0 → x ⊆ y :=  
    λ h : |x \ y| = 0,
    have v: x \ y = ∅, from (iff.elim_left (finset.card_eq_zero)) h,
    (iff.elim_left finset.sdiff_eq_empty_iff_subset) v
    

lemma card_zero_of_not_pos (X : finset α) : ¬ 0 < |X| → |X| = 0 :=
    λ h: ¬ 0 < |X|,
    eq.symm ((iff.elim_right eq_iff_le_not_lt) (and.intro (nat.zero_le (|X|)) h))

-- how about a lemma like: a+b = 0, 0 ≤ a, 0 ≤ b → 0 = b
--#check lt_add_of_lt_of_nonneg -- 0 < b → 0 ≤ a → 0 < b + a
--#check eq_iff_le_not_lt -- 0 = b ↔ 0 ≤ b ∧ ¬ 0 < b
--#check lt_add_of_lt_of_nonneg'

lemma eq_zero_of_nonneg_of_nonneg_of_add_zero {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 = a + b → 0 = a :=
    λ ha: 0 ≤ a, λ hb: 0 ≤ b, λ h: 0 = a + b,
    have h1: ¬ 0 < a, from
        assume h2: 0 < a,
        have h4: 0 < a + b, from lt_add_of_lt_of_nonneg h2 hb,
        have h3: 0 ≤ a + b ∧ ¬ 0 < a + b, from (iff.elim_left eq_iff_le_not_lt) h,
        h3.elim_right h4,
    have h0: 0 ≤ a ∧ ¬ 0 < a, from and.intro ha h1,
    (iff.elim_right eq_iff_le_not_lt) h0 

 

theorem subset_of_delta_eq_zero (hm: 0 < m) (hM: m ≤ M) (X Y : finset α) (h: δ m M X Y = 0) : X ⊆ Y :=
    let x_y := |X \ Y| in let y_x := |Y \ X| in
    /- The following interacts poorly with casting
    let maxN := max x_y y_x in let minN := min x_y y_x in
    let maxR := (maxN : ℝ) in let minR := (minN : ℝ) in
    -/
    have used_by_finish: δ m M X Y =  M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ), from by { norm_cast },
    have δ_0: 0 = M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ), from by {unfold δ at h,apply eq.symm,norm_cast,exact h,},
    have not_pos_δ: ¬ 0 < M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ), from
        (iff.elim_right (not_lt_iff_eq_or_lt)) (or.inl δ_0),
    have min_nonneg: 0 ≤ ((min x_y y_x):ℝ), from
        begin norm_cast, exact (le_min (nat.zero_le x_y) (nat.zero_le y_x)) end,
    have M_pos: 0 < M, from calc
                0 < m : hm
              ... ≤ M : hM,

    have pos_δ_of_pos_x: 0 < x_y → 0 < M * ((max x_y y_x):ℝ) + m * ((min x_y y_x):ℝ), from
        λ h: 0 < x_y,
        have strict_x: 0 <  (max x_y y_x), from
            (iff.elim_right lt_max_iff) (or.inl h),
        have cast_x: 0 <  ((max x_y y_x):ℝ), from
            begin norm_cast, exact strict_x end,
        have Mx_pos: 0 < (M * ((max x_y y_x):ℝ)), from
            mul_pos M_pos cast_x,
        lt_add_of_lt_of_nonneg Mx_pos (mul_nonneg (le_of_lt hm) min_nonneg),

    have r0: ¬ 0 < x_y, from λ pos_x, not_pos_δ (pos_δ_of_pos_x pos_x),

    subseteq_of_card_zero X Y (card_zero_of_not_pos (X\Y) r0)

 theorem eq_of_delta_eq_zero (hm: 0 < m) (hM: m ≤ M) (X Y : finset α) (h: δ m M X Y = 0) :
 X = Y :=
    let x_y := |X \ Y| in let y_x := |Y \ X| in
 have g0: X ⊆ Y, from subset_of_delta_eq_zero hm hM X Y h,
 have g: δ m M Y X = 0, from calc δ m M Y X = δ m M X Y: by rw[delta_comm]
 ... = 0: h,
 have g1: Y ⊆ X, from subset_of_delta_eq_zero hm hM Y X g,
     finset.subset.antisymm g0 g1

-- UPDATED TO HERE


theorem sdiff_covering {A B C : finset α}: A\C ⊆ (A\B) ∪ (B\C) := sdiff_triangle A B C

theorem sdiff_triangle' (A B C: finset α): |A\C| ≤ |A\B| + |B\C| :=
    calc |A\C| ≤ |A\B  ∪ B\C|: finset.card_le_of_subset (sdiff_covering)
           ... = |A\B| + |B\C| : by rw (finset.card_disjoint_union (disj₂ A B C))

lemma venn (X Y : finset α): X = X\Y ∪ (X ∩ Y) := begin ext, simp, tauto! end

lemma venn_card (X Y : finset α): |X| = |X\Y| + |X ∩ Y| :=
    have h: disjoint (X\Y) (X ∩ Y), from disjoint_sdiff_inter X Y,
    calc
    |X| = |X \ Y  ∪  X ∩ Y| : by rw ← (venn X Y)
    ... = |X \ Y| + |X ∩ Y| : finset.card_disjoint_union h


lemma sdiff_card (X Y : finset α): |Y| ≤ |X| → |Y\X| ≤ |X\Y| :=
    assume h: |Y| ≤ |X|,
    have h₀: |Y\X| + |Y ∩ X| ≤ |X\Y| + |X ∩ Y|, from
        begin
            rw (venn_card X Y) at h,
            rw (venn_card Y X) at h,
            exact h
        end, -- rw means rewrite using ... at ...
    have h₁: Y ∩ X = X ∩ Y, from inter_comm _ _,
    have h₂: |Y ∩ X| = |X ∩ Y|, from begin rw h₁ end,
    have h₃: |Y\X| + |X ∩ Y| ≤ |X\Y| + |X ∩ Y|, from
        begin rw h₂ at h₀, exact h₀ end,
    le_of_add_le_add_right h₃

    lemma maxmin_1 {X Y : finset α}: |X| ≤ |Y| → δ m M X Y = M * |Y\X| + m * |X\Y| :=
    let x_y := |X\Y| in let y_x := |Y\X| in
    assume h₁: |X| ≤ |Y|,
        have h₂: x_y ≤ y_x, from sdiff_card Y X h₁,
        calc δ m M X Y = M * ↑ (max x_y y_x) + m * ↑(min x_y y_x) : rfl
                   ... = M * ↑ y_x            + m * ↑ x_y : by rw[max_eq_right h₂,min_eq_left h₂]

lemma maxmin_2 {X Y : finset α}: |Y| ≤ |X| → δ m M X Y = M * |X\Y| + m * |Y\X| :=
-- resolve max and min
    let x_y := |X\Y| in let y_x := |Y\X| in
    assume h₁: |Y| ≤ |X|,
        have h₂: y_x ≤ x_y, from sdiff_card X Y h₁,
        calc δ m M X Y = M * ↑ (max x_y y_x) + m * ↑(min x_y y_x) : rfl
                   ... = M * ↑ x_y            + m * ↑y_x : by rw[max_eq_left h₂,min_eq_right h₂]

theorem casting {a b : ℕ}: a ≤ b → (a:ℝ) ≤ (b:ℝ) :=
    begin intro h, norm_cast, exact h end

theorem mul_sdiff_tri (m : ℝ) (hm: 0 ≤ m) (X Y Z : finset α):
    m * ↑ |X\Z| ≤ m * (↑ |X\Y| + ↑ |Y\Z|) :=
    calc m * ↑ (|X\Z|)
       ≤ m * ↑ ((|X\Y|) + (|Y\Z|)) : mul_le_mul_of_nonneg_left (casting(sdiff_triangle' X Y Z)) hm
   ... = m * ((|X\Y|:ℝ) + (|Y\Z|:ℝ)): by norm_cast
 
def triangle_inequality (m M :ℝ) (X Y Z: finset α) : Prop :=
    δ m M X Y ≤ δ m M X Z + δ m M Z Y

lemma seventeen_right_yzx {m M :ℝ} {X Y Z: finset α} :
    0 ≤ m → m ≤ M → |Y| ≤ |Z| ∧ |Z| ≤ |X| → triangle_inequality m M X Y Z
    :=
    let x := |X| in let y := |Y| in let z := |Z| in
    let x_z := |X\Z| in let z_x := |Z\X| in let y_z := |Y\Z| in
    let z_y := |Z\Y| in let x_y := |X\Y| in let y_x := |Y\X| in
    λ hm : 0 ≤ m, λ h: m ≤ M,
    have hM : 0 ≤ M, from le_trans hm h,
    assume h₀: y ≤ z ∧ z ≤ x,
    have h₂: y ≤ z, from and.elim_left h₀,
    have h₃: z ≤ x, from and.elim_right h₀,
    have h₁: y ≤ x, from le_trans h₂ h₃,
    have dxz: δ m M X Z = M * (x_z) + m * (z_x), from maxmin_2 h₃,
    have dzy: δ m M Z Y = M * (z_y) + m * (y_z), from maxmin_2 h₂,--used implicitly by a tactic

    have mst_yzx: m* ↑ (|Y\X|) ≤ m *  (↑ (y_z) + ↑ (z_x)), from
        mul_sdiff_tri m hm Y Z X,
    have mst_xzy: M* ↑ (x_y) ≤ M *  (↑ (x_z) + ↑ (z_y)), from
        mul_sdiff_tri M hM X Z Y,
    calc
    δ m M X Y = M * (x_y) + m * (|Y\X|)                   : maxmin_2 h₁
          ... ≤ M * (x_y) + m * ((y_z) + (z_x))           : add_le_add_left mst_yzx (M * (x_y))
          ... ≤ M * (x_z + z_y) + m * (y_z + z_x)         : add_le_add_right mst_xzy (m * ((y_z) + (z_x)))
          ... = (M * x_z + m * z_x) + (M * z_y + m * y_z) : by ring2
          ... = δ m M X Z                     + δ m M Z Y : by rw[dxz,dzy]

lemma co_sdiff (X Y U : finset α):
X ⊆ U → Y ⊆ U → (U\X)\(U\Y) = Y\X := by tidy

lemma co_sdiff_card (X Y U : finset α):
X ⊆ U → Y ⊆ U → ((U\X)\(U\Y)).card = (Y\X).card :=
    λ hx: X ⊆ U, λ hy: Y ⊆ U,
    by {rw co_sdiff X Y U, exact hx,exact hy,}

lemma co_sdiff_card_max (X Y U : finset α):
X ⊆ U → Y ⊆ U → max (|(U\Y)\(U\X)|) (|(U\X)\(U\Y)|) = max (|X\Y|) (|Y\X|) :=
    λ hx: X ⊆ U, λ hy: Y ⊆ U,
    by {rw[co_sdiff_card X Y U hx hy,co_sdiff_card Y X U hy hx],}

lemma co_sdiff_card_min (X Y U : finset α):
X ⊆ U → Y ⊆ U → min (|(U\Y)\(U\X)|) (|(U\X)\(U\Y)|) = min (|X\Y|) (|Y\X|) :=
    λ hx: X ⊆ U, λ hy: Y ⊆ U,
    by {rw[co_sdiff_card X Y U hx hy,co_sdiff_card Y X U hy hx],}

theorem delta_complement (X Y U : finset α):
    X ⊆ U → Y ⊆ U → δ m M X Y = δ m M (U\Y) (U\X) :=
    λ hx: X ⊆ U, λ hy: Y ⊆ U,
    let Y' := U\Y, X' := U\X in
    have co1: |X'\Y'| = |Y\X|, from co_sdiff_card X Y U hx hy,
    have co2: |Y'\X'| = |X\Y|, from co_sdiff_card Y X U hy hx,
    have co3: max (|Y'\X'|) (|X'\Y'|) = max (|X\Y|) (|Y\X|), from
        co_sdiff_card_max X Y U hx hy,
    have co4: min (|Y'\X'|) (|X'\Y'|) = min (|X\Y|) (|Y\X|), from
        co_sdiff_card_min X Y U hx hy,
    have defi: δ m M Y' X' = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|Y'\X'|) (|X'\Y'|)),
    from refl (δ m M Y' X'),
    calc δ m M X Y = M * ↑ (max (|X\Y|) (|Y\X|)) + m * ↑ (min (|X\Y|) (|Y\X|)): refl (δ m M X Y)
    ... = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|X\Y|) (|Y\X|)): by rw co3
    ... = M * ↑ (max (|Y'\X'|) (|X'\Y'|)) + m * ↑ (min (|Y'\X'|) (|X'\Y'|)): by rw co4
    ... =  δ m M Y' X': by rw defi


theorem seventeen_right_yxz {X Y Z : finset α}:
    0 ≤ m → m ≤ M → |Y| ≤ |X| ∧ |X| ≤ |Z| → triangle_inequality m M X Y Z :=
    let x := |X| in let y := |Y| in let z := |Z| in
    let x_z := |X\Z| in let z_x := |Z\X| in let y_z := |Y\Z| in
    let z_y := |Z\Y| in let x_y := |X\Y| in let y_x := |Y\X| in
    λ hm: 0 ≤ m, λ h: m ≤ M, λ h₀: y ≤ x ∧ x ≤ z,
    have hyz: y ≤ z, from le_trans (and.elim_left h₀) (and.elim_right h₀),
    have gxz: x_z ≤ z_x, from sdiff_card Z X (and.elim_right h₀),
    have gyz: y_z ≤ z_y, from sdiff_card Z Y hyz,
    have dxy: δ m M X Y = M * x_y + m * y_x, from maxmin_2 (and.elim_left h₀),
    have dzy: δ m M Z Y = M * z_y + m * y_z, from maxmin_2 hyz,
    have dxz: δ m M X Z = M * z_x + m * x_z, from calc
                δ m M X Z = δ m M Z X                 : delta_comm
                    ... = M * (z_x) + m * (x_z) : maxmin_2 (and.elim_right h₀), 
    have Mmpos: M-m ≥ 0, from 
calc M - m  ≥ m - m: sub_le_sub_right h _ 
        ... = 0 : sub_self _ ,
    have h02: 0 ≤ (2:ℝ), from by {have zt: 0 ≤ 2, from nat.zero_le 2, norm_cast, exact zt, },
    have h2m: 0 ≤ 2*m, from mul_nonneg h02 hm,
    have tri_1:   2 * m * y_x ≤ 2 * m * (y_z + z_x), from mul_sdiff_tri (2*m) h2m Y Z X,
    have tri_2: (M-m) * x_y ≤ (M-m) * (x_z + z_y), from mul_sdiff_tri (M-m) Mmpos X Z Y,

    have tri_3:  (M-m) * x_z ≤ (M-m) * z_x, from mul_le_mul_of_nonneg_left (casting(gxz)) Mmpos,
    have triangle_add: (δ m M X Y) + (m * y_x) ≤ (δ m M X Z + δ m M Z Y) + (m * y_x), from
        let
            term_1 := (M * x_y),
            term_2 := (m*(x_z+z_y+y_x) + m*(y_z+z_x)),
            term_3 := (m*(x_z +z_y +y_x) + (M-m) * z_y + m*z_x + m*y_z)
        in calc   (δ m M X Y)     + (m * y_x)
            = (M * x_y + m * y_x) + (m * y_x)                             : by rw dxy
        ... = M * x_y + 2 * m * y_x                                       : by ring2
        ... ≤ M * x_y + 2 * m * (y_z+z_x)                                 : add_le_add_left tri_1 term_1
        ... = m*(x_y+y_z+z_x) + m*(y_z+z_x) + (M-m)*x_y                   : by ring
        ... = m*(x_z+z_y+y_x) + m*(y_z+z_x) + (M-m)*x_y                   : by rw card_rot_cast
        ... ≤ m*(x_z+z_y+y_x) + m*(y_z+z_x) + (M-m)*(x_z+ z_y)            : add_le_add_left tri_2 term_2
        ... = m*(x_z+z_y+y_x) + (M-m) * z_y + m*z_x + m*y_z + (M-m) * x_z : by ring2
        ... ≤ m*(x_z+z_y+y_x) + (M-m) * z_y + m*z_x + m*y_z + (M-m) * z_x : add_le_add_left tri_3 term_3
        ... = (M * z_x + m * x_z)        + (M * z_y + m * y_z) + (m * y_x): by ring
        ... = (δ m M X Z                 +          δ m M Z Y) + (m * y_x): by rw[dxz,dzy],
    le_of_add_le_add_right triangle_add
    -- so instead of 0 ≤ m ≤ M, 1 ≤ M we could have m=u, M=u+v and then 0≤ u, 0≤ v, u+v≥ 1.
    -- with Jaccard being u=1, v=0 and NID being u=0, v=1
    -- then we would only be dealing with max, no mins
    -- so beta alpha = u and beta - beta alpha = u + v, so beta = 2u+v, alpha=u/(2u+v)
    -- This suggest u=v=1/2 as interesting. That would be beta=3/2, alpha=1/3 actually.
    -- December 11, 2020
    --let r_yz := (y_z+z_x:ℝ) in -- need to cast first
    --let u := m in let v := M-m in

lemma sdiff_card_le (X Y U : finset α) (hx: X ⊆ U) (hy: Y ⊆ U) (h:|X| ≤ |Y|):
    |U \ Y| ≤ |U \ X| :=
    have hu: |U| - |Y| ≤ |U| - |X|, from nat.sub_le_sub_left (|U|) h,-- important to use nat.!
    calc
        |U \ Y| = |U| - |Y| : card_sdiff hy
            ... ≤ |U| - |X| : hu
            ... = |U \ X|   : by rw[card_sdiff hx]

theorem seventeen_right_zyx{m M : ℝ} {X Y Z : finset α}:
    0 ≤ m → m ≤ M → |Z| ≤ |Y| ∧ |Y| ≤ |X| → triangle_inequality m M X Y Z := 
    λ hm, λ hM, λ h,
    let
        U := X ∪ Y ∪ Z,
        Z' : finset α := (X ∪ Y ∪ Z) \ Z,
        Y' : finset α := (X ∪ Y ∪ Z) \ Y,
        X' : finset α := (X ∪ Y ∪ Z) \ X
    in
    have hx: X ⊆ U, from by {tidy,cc},
    have hy: Y ⊆ U, from by {tidy,cc},
    have hz: Z ⊆ U, from by {tidy,cc},
    
    have and1: |X'| ≤ |Y'|, from sdiff_card_le Y X U hy hx h.right,
    have and2: |Y'| ≤ |Z'|, from sdiff_card_le Z Y U hz hy h.left,
    have hh: |X'| ≤ |Y'| ∧ |Y'| ≤ |Z'|, from and.intro and1 and2,
    have h1: δ m M X' Z' = δ m M Z X, from (delta_complement Z X U hz hx).symm,
    have h2: δ m M Z' Y' = δ m M Y Z, from (delta_complement Y Z U hy hz).symm,
    have h3: δ m M Y Z = δ m M Z Y, from delta_comm,
    calc δ m M X Y = δ m M Y' X'               : delta_complement X Y U hx hy
               ... ≤ δ m M Y' Z' + δ m M Z' X' : seventeen_right_yxz hm hM hh
               ... = δ m M X' Z' + δ m M Z' Y' : by rw[delta_comm,add_comm,delta_comm]
               ... = δ m M Z  X  + δ m M Z' Y' : by rw[h1]
               ... = δ m M X  Z  + δ m M Z' Y' : by rw[delta_comm]
               ... = δ m M X  Z  + δ m M Y  Z  : by rw[h2]
               ... = δ m M X  Z  + δ m M Z  Y  : by rw[h3]
    -- within X ∪ Y ∪ Z: for some f satisfying f(a,b)=f(b,a), 
    -- δ (Xᶜ, Yᶜ ) = f(Xᶜ \ Yᶜ , Yᶜ \ Xᶜ ) = f(Y \ X, X \ Y) = f(X \ Y, Y \ X) = δ (X, Y).

theorem seventeen_right_zxy {X Y Z : finset α}:
    0 ≤ m → m ≤ M → |Z| ≤ |X| ∧ |X| ≤ |Y| → triangle_inequality m M X Y Z :=
    λ hm: 0 ≤ m, λ h: m ≤ M, λ hyp: |Z| ≤ |X| ∧ |X| ≤ |Y|,
    have hyz: δ m M Y Z = δ m M Z Y, from delta_comm,
    have hzx: δ m M Z X = δ m M X Z, from delta_comm,
    calc
    δ m M X Y = δ m M Y X             : delta_comm
          ... ≤ δ m M Y Z + δ m M Z X : seventeen_right_zyx hm h hyp
          ... = δ m M Z X + δ m M Y Z : add_comm (δ m M Y Z) (δ m M Z X)
          ... = δ m M X Z + δ m M Z Y : by rw[hyz,hzx]


theorem three_places {x y z : ℕ} :
    y ≤ x → (z ≤ y ∧ y ≤ x) ∨ (y ≤ z ∧ z ≤ x) ∨ (y ≤ x ∧ x ≤ z) :=
    assume hyx : y ≤ x,
    (le_total z y).elim(
        assume h: z ≤ y, or.inl (and.intro h hyx)
    )(
        assume h: y ≤ z,
        (le_total z x).elim(
            assume h1: z ≤ x, or.inr (or.inl (and.intro h h1))
        )(
            assume h1: x ≤ z, or.inr (or.inr (and.intro hyx h1))
    ))

theorem seventeen_right_y_le_x {m M : ℝ} {X Y Z : finset α} :
    |Y| ≤ |X| → 0 ≤ m → m ≤ M → triangle_inequality m M X Y Z :=
    let x := |X| in let y := |Y| in let z := |Z| in -- November 30, 2020
    λ h: y ≤ x, λ hm: 0 ≤ m, λ hmM: m ≤ M,
    (three_places h).elim(
        λ h1, seventeen_right_zyx hm hmM h1
    )(
        λ h1: y≤ z ∧ z ≤ x ∨ y ≤ x ∧ x ≤ z,
        h1.elim(
            λ h2, seventeen_right_yzx hm hmM h2
        )(
            λ h2, seventeen_right_yxz hm hmM h2
        )
    )

theorem seventeen_right_x_le_y {m M : ℝ} {X Y Z : finset α} :
    |X| ≤ |Y| → 0 ≤ m → m ≤ M → triangle_inequality m M X Y Z :=
    λ h: |X| ≤ |Y|, λ hm: 0 ≤ m, λ hmM: m ≤ M,
    have hh: δ m M Y Z = δ m M Z Y, from delta_comm,
    have gg: δ m M Z X = δ m M X Z, from delta_comm,
    calc
    δ m M X Y = δ m M Y X : delta_comm
        ... ≤ δ m M Y Z + δ m M Z X : seventeen_right_y_le_x h hm hmM
        ... = δ m M Z X + δ m M Y Z : add_comm (δ m M Y Z) (δ m M Z X)
        ... = δ m M X Z + δ m M Z Y: by rw[hh,gg]


theorem seventeen_right {m M : ℝ} { X Y Z : finset α}:
    0 ≤ m → m ≤ M → triangle_inequality m M X Y Z :=
    λ hm: 0 ≤ m, λ h: m ≤ M,
    (le_total (|X|) (|Y|)).elim (
        λ h1: |X| ≤ |Y|, seventeen_right_x_le_y h1 hm h
    )(
        λ h1: |Y| ≤ |X|, seventeen_right_y_le_x h1 hm h
    )

def s_0 : finset ℕ := ({0}: finset ℕ)
def s_1 : finset ℕ := ({1}: finset ℕ)
def s01 : finset ℕ := ({0,1} : finset ℕ)
theorem seventeen:
    0 ≤ m → (m ≤ M ↔ ∀ X Y Z : finset ℕ, triangle_inequality m M X Y Z) :=

    λ hm: 0 ≤ m,
    have h₀: m ≤ M → ∀ X Y Z : finset ℕ, triangle_inequality m M X Y Z, from
        λ h: m ≤ M, λ X Y Z, seventeen_right hm h,
    have h₁: (∀ X Y Z : finset ℕ, triangle_inequality m M X Y Z) → m ≤ M, from
        assume hyp: (∀ X Y Z : finset ℕ, triangle_inequality m M X Y Z),
        have hh: δ m M {0} {1} ≤ δ m M {0} {0,1} + δ m M {0,1} {1}, from hyp {0} {1} {0,1},
        have s_0\s_1 = {0}, from by dec_trivial, have s_1\s_0 = {1}, from by dec_trivial,
        have s_0\s01 =   ∅, from by dec_trivial, have s01\s_0 = {1}, from by dec_trivial,
        have s_1\s01 =  ∅ , from by dec_trivial, have s01\s_1 = {0}, from by dec_trivial,
        -- finish actually uses the unnamed hypotheses


        have cyxN: (|s_1\s_0|:nat) = (1:nat), from by dec_trivial,
        -- have cxzN: (|s_0\s01|:nat) = (0:nat), from by dec_trivial,
        have czxN: (|s01\s_0|:nat) = (1:nat), from by dec_trivial,
        have czyN: (|s01\s_1|:nat) = (1:nat), from by dec_trivial,
        -- have cyzN: (|s_1\s01|:nat) = (0:nat), from by dec_trivial,
        have cxyN: (|s_0\s_1|:nat) = (1:nat), from by dec_trivial,

        have cyx: (|s_1\s_0|:ℝ) = (1:ℝ), by {norm_num,exact cyxN,},
        have cxz: (|s_0\s01|:ℝ) = (0:ℝ), by {norm_num,dec_trivial,},
        have czx: (|s01\s_0|:ℝ) = (1:ℝ), by {norm_num,exact czxN,},
        have czy: (|s01\s_1|:ℝ) = (1:ℝ), by {norm_num,exact czyN,},
        have cyz: (|s_1\s01|:ℝ) = (0:ℝ), by {norm_num,dec_trivial,},
        have cxy: (|s_0\s_1|:ℝ) = (1:ℝ), by {norm_num,exact cxyN,},
        have dxy: δ m M s_0 s_1 = M + m , from calc
            δ m M s_0 s_1 = M * max ↑(|s_0\s_1|) ↑(|s_1\s_0|)
                          + m * min ↑(|s_0\s_1|) ↑(|s_1\s_0|): delta_cast
                      ... = M * max    (1:ℝ)  (1:ℝ)   + m * min (1:ℝ)    (1:ℝ): by rw[cxy,cyx]
                      ... = M + m : by tidy,
        have dxz: δ m M s_0 s01 = M, from calc
                  δ m M s_0 s01 = M * max (|s_0\s01|) (|s01\s_0|)
                                + m * min (|s_0\s01|) (|s01\s_0|): delta_cast
                            ... = M * max 0 1 + m * min 0 1: by rw[cxz,czx]
                            ... = M  : by tidy,
        have dzy: δ m M s01 s_1 = M, from calc
                  δ m M s01 s_1 = M * max (|s01\s_1|) (|s_1\s01|)
                                + m * min (|s01\s_1|) (|s_1\s01|): delta_cast
                            ... = M * max 1 0 + m * min (1) 0: by rw[czy,cyz]
                            ... = M  : by tidy,
        have add_le_add_left : M + m ≤ M + M, from calc
            M + m = δ m M s_0 s_1 : by rw[dxy] 
              ... ≤  δ m M s_0 s01 + δ m M s01 s_1: hh
              ... = M + M: by begin rw[dxz,dzy] end,
        le_of_add_le_add_left
              add_le_add_left,
    iff.intro h₀ h₁

    def delta_triangle (X Y Z: finset ℕ) (hm: 0 < m) (hM: m ≤ M):
    triangle_inequality m M X Z Y
    --δ m M X Y ≤ δ m M X Z + δ m M Z Y
    :=
    ((iff.elim_left (seventeen (le_of_lt hm))) hM) X Z Y

    section jaccard_numerator
    /-- Instantiate finset ℕ as a metric space. -/

    def protein {m M : ℝ} (hm : 0 < m) (hM : m ≤ M) := finset α


    instance jaccard_numerator.metric_space (hm : 0 < m) (hM : m ≤ M): metric_space (protein hm hM) := {
        dist               := λx y, δ m M x y,
        dist_self          := delta_self, -- have to give proof that d(x,x)=0
        eq_of_dist_eq_zero := eq_of_delta_eq_zero hm hM, -- a_of_b_of_c means b → c → a
        dist_comm          := λ x y, calc δ m M x y = δ m M y x: delta_comm,
        dist_triangle      := λ x y z, ((iff.elim_left (seventeen (le_of_lt hm))) hM) x z y
    }
end jaccard_numerator 


