/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Xavier Généreux.
-/


import analysis.analytic.basic
import analysis.complex.abs_max
import analysis.complex.re_im_topology
import analysis.calculus.diff_cont_on_cl
import data.real.cardinality
import analysis.normed_space.operator_norm
import topology.metric_space.baire
import topology.algebra.module.basic
import data.complex.basic

/-!
# Hadamard three-lines Theorem

In this file we present a proof of a special case Hadamard' three-lines Theorem.
This result generalises well by a change of variables.

## Main result

- 'Hadamard_three_lines_theorem_on_zero_one' : The theorem on the strip {0 ≤ z.re ∧ z.re ≤ 1}

## Notation

- 'strip a b' : The vertical strip defined by : re ⁻¹' Ioo a b

- 'closed_strip a b' : The vertical strip defined by : re ⁻¹' Icc a b

- 'bdd_strip a b' : The rectangle defined by : re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

- 'closed_bdd_strip a b' : The rectangle defined by : re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

- ' M x' : The supremum function on vertical lines defined by : sup {|f(z)| : z.re = x}

## References

This proof follows loosely the proof found on the wiki page:
[wiki](https://en.wikipedia.org/wiki/Hadamard_three-lines_theorem)

-/


open set metric filter function complex
open_locale interval nnreal ennreal 

local attribute [-simp] div_eq_zero_iff

namespace complex
variables (a b : ℝ)(z : ℂ) 

-- Definitions of the strip a ≤ z.re ∧ z.re ≤ b

def strip (a: ℝ) (b: ℝ) := re ⁻¹' Ioo a b

def closed_strip (a: ℝ) (b: ℝ) := re ⁻¹' Icc a b

def bdd_strip (a: ℝ) (b: ℝ) (T: ℝ) :=  re ⁻¹' Ioo a b ∩ im ⁻¹' Ioo (-T) T

def closed_bdd_strip (a: ℝ) (b: ℝ) (T: ℝ) :=  re ⁻¹' Icc a b ∩ im ⁻¹' Icc (-T) T

/- 
**Hadamard three-lines Theorem**
Let f be a diff_cont_on_cl function on (strip a b), then
if M(x) := sup {|f(z)| : z.re = x}, log M(x) is convex on [a b].
-/ 

noncomputable def M (f : ℂ → ℂ) (x : ℝ) :=  Sup ((abs ∘ f) '' (re ⁻¹' {x})) 

noncomputable def g (f : ℂ → ℂ) (z : ℂ): ℂ := 
  if (M f 0) = 0 ∨ (M f 1) = 0
    then 0
    else (M f 0)^(z-1) * (M f 1)^(-z)

noncomputable def F (f : ℂ → ℂ) := λ z, f z • g f z

noncomputable def F' (n: ℕ) (f: ℂ → ℂ) := λ z, F f z • exp ((z^2-1) * (n : ℝ)⁻¹) 

-- Small lemma: Sup of abs is nonneg

lemma M_nonneg (f : ℂ → ℂ) (x : ℝ) :  0 < M f x ∨ 0 = M f x :=
begin
apply has_le.le.lt_or_eq, apply real.Sup_nonneg, intros x hx, rw mem_image at hx,
cases hx with z1 hx, cases hx with hz1 hz2, rw [← hz2, comp], simp only [map_nonneg],
end

-- Definition rewrites for g
lemma g_pos_def (f: ℂ → ℂ ) (h0: (M f 0) > 0)(h1 : (M f 1) > 0): 
  g f z = (M f 0)^(z-1) * (M f 1)^(-z) :=
begin
  rw g, apply if_neg, push_neg, split, rw ne_iff_lt_or_gt, right, exact h0,
  rw ne_iff_lt_or_gt, right, exact h1,
end

lemma g_zero_def (f: ℂ → ℂ ) (h: (M f 0) = 0 ∨ (M f 1) = 0): g f z = 0 :=
begin
  rw g, apply if_pos, exact h,
end

-- Differentiable continuous function g

lemma g_diff_cont (f: ℂ → ℂ) (hd : diff_cont_on_cl ℂ f (strip 0 1)) : 
  diff_cont_on_cl ℂ (g f) (strip 0 1) :=
begin
-- Lemma to handle rewriting of g.
  have hzero: (M f 0) = 0 ∨ (M f 1) = 0 → g f = 0, {intro h0, rw funext_iff, intro z,
  rw g_zero_def z f h0, simp only [pi.zero_apply, eq_self_iff_true],},
  have hpos: (M f 0) > 0 ∧ (M f 1) > 0 → g f = λ (z:ℂ), (M f 0)^(z-1) * (M f 1)^(-z),
  {intro h0, rw funext_iff, intro z, rw g_pos_def z f h0.1 h0.2,},
 
  -- Case everywhere 0
  by_cases (M f 0) = 0 ∨ (M f 1) = 0, 
  specialize hzero h, rw hzero, rw pi.zero_def, apply diff_cont_on_cl_const,

  -- Case non-zero
  push_neg at h, cases h with h0 h1, apply differentiable.diff_cont_on_cl, rw differentiable, 
  intro z, rw ne_comm at h0 h1,
  specialize hpos _, split, apply (or.resolve_right (M_nonneg f 0) h0),
  apply (or.resolve_right (M_nonneg f 1) h1), rw hpos,
  apply differentiable_at.mul,
  refine differentiable_at.const_cpow (differentiable_at.sub_const (differentiable_at_id') 1) _,
  left, simp only [ne.def, of_real_eq_zero], rwa eq_comm, refine differentiable_at.const_cpow _ _,
  simp only [differentiable_at_id', differentiable_at_neg_iff],
  left, simp only [ne.def, of_real_eq_zero], rwa eq_comm,
end

lemma F_diff_cont (f: ℂ → ℂ) (hd : diff_cont_on_cl ℂ f (strip 0 1)) : 
  diff_cont_on_cl ℂ (F f) (strip 0 1):=
begin
  refine diff_cont_on_cl.smul _ _,exact hd, exact g_diff_cont f hd, 
end

lemma F'_diff_cont (f: ℂ → ℂ) (n : ℕ) (hd : diff_cont_on_cl ℂ f (strip 0 1)) : 
  diff_cont_on_cl ℂ (F' n f) (strip 0 1):=
begin
  refine diff_cont_on_cl.smul (F_diff_cont f hd) _, apply differentiable.diff_cont_on_cl, simp only 
  [differentiable.cexp, differentiable.mul, differentiable_sub_const_iff, differentiable.pow, 
  differentiable_id', differentiable_const],
end


-- The function f is bounded by M 
lemma f_le_Sup (f : ℂ → ℂ) (z : ℂ) (hD: z ∈ (closed_strip 0 1)) 
  (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))): abs (f z) ≤ M f (z.re) :=
begin
  refine le_cSup _ _, 
  apply bdd_above.mono _ hB, refine (image_subset (abs ∘ f) _), 
  apply preimage_mono, simp only [singleton_subset_iff, ← mem_preimage], exact hD,
  simp only [mem_image_of_mem (⇑abs ∘ f), mem_preimage, mem_singleton], 
end


-- Smoothly decreasing function when the real part is bounded eventually ≤ 1
lemma Expterm_eventually_le_one (n : ℕ) (hn: n ∈ {m : ℕ | 1 ≤ m}):
  ∀ (C : ℝ), ∃ T>0, ∀ (z : ℂ), z.re ∈ (Icc (0:ℝ)  1) → |z.im| ≥ T → 
  C * abs(exp ((z^2-1) * (n : ℝ)⁻¹) ) ≤ 1 :=
begin
  -- Trivial case of: 0 ≤ C. 
    intro C, by_cases hC : C ≤ 0, use 1, split, apply zero_lt_one,
    intros z hset him, apply le_trans _ (le_of_lt (zero_lt_one' ℝ)),
    rw mul_nonpos_iff, right, simp only [hC, of_real_nat_cast, and_self, map_nonneg], 
    rw not_le at hC,
  -- Small casting lemma
    have hdivnat : 0 ≤ ((n:ℂ)⁻¹).re, 
    {simp only [← of_real_nat_cast n, ← of_real_inv n, of_real_re, inv_nonneg, nat.cast_nonneg]},

  -- Bounding with z.re = 1
    have hmax_onre: ∀ (z : ℂ), z.re ∈ (Icc (0:ℝ)  1) 
    → C * real.exp ((z.re * z.re - z.im * z.im - 1) * (n : ℂ)⁻¹.re) 
    ≤ C * real.exp ((- z.im * z.im) * ((n:ℂ)⁻¹).re), 
    {intros z hset, refine mul_le_mul_of_nonneg_left _ (le_of_lt hC),
    rw real.exp_le_exp, refine mul_le_mul_of_nonneg_right _ hdivnat,
    simp only [Icc, mem_set_of_eq] at hset, 
    simp only [neg_mul, add_sub_cancel'_right, tsub_le_iff_right, le_neg_add_iff_add_le, ← sq,
    sq_le_one_iff hset.1, hset.2],
    },

  -- Non-zero terms
    have hExpne: ∀ (z:ℂ), real.exp(-z.im * z.im * (n : ℂ)⁻¹.re) ≠ 0, 
    {intro z, rw ne_comm, apply (has_lt.lt.ne (real.exp_pos (-z.im * z.im * (n : ℂ)⁻¹.re))),},

  -- Trivial case of: 0 < C ≤ 1
    by_cases hC1 : C ≤ 1, use 1, split, apply zero_lt_one,
    intros z hset him,
    -- Rewriting in terms of z.re+I*z.im 
    rw ← re_add_im z, simp only [abs_exp, tsub_zero,
    sub_re, one_re, mul_re, zero_div, re_add_im,
    of_real_nat_cast, one_im, nat_cast_im, inv_im,
    sq, sub_im, mul_im, mul_zero, neg_zero],
    -- Bounding by the case z.re = 0 and showing that exp of neg is ≤ 1. 
    specialize hmax_onre z hset, apply le_trans hmax_onre, 
    apply mul_le_one hC1 (le_of_lt (real.exp_pos (-z.im * z.im * (n : ℂ)⁻¹.re))),
    simp only [real.exp_le_one_iff, right.neg_nonpos_iff, neg_mul, nat_cast_re, ← sq,
    mul_nonneg (sq_nonneg z.im) (hdivnat)], rw not_le at hC1,

  -- Using semi-explicit T depending only on C
    use real.sqrt(n*real.log C), split, 
    {apply real.sqrt_pos_of_pos, apply mul_pos, 
    simp only [nat.cast_pos, lt_of_lt_of_le zero_lt_one hn.out], apply real.log_pos hC1,},
    intros z hset him,
    -- Rewriting in terms of z.re+I*z.im 
    rw ← re_add_im z, simp only [abs_exp, tsub_zero,
    sub_re, one_re, mul_re, zero_div, re_add_im,
    of_real_nat_cast, one_im, nat_cast_im, inv_im,
    sq, sub_im, mul_im, mul_zero, neg_zero],

  -- Manipulate to show that T is well chosen.
  specialize hmax_onre z hset,
  apply le_trans hmax_onre, clear hmax_onre, 
  rw ← real.log_nonpos_iff (mul_pos hC (real.exp_pos (-z.im * z.im * (n : ℂ)⁻¹.re))), 
  specialize hExpne z,
  rw real.log_mul (ne_of_gt hC) hExpne,  
  simp only [add_zero, neg_mul, nat_cast_re, real.log_exp, add_neg_le_iff_le_add'],
  simp only [← of_real_nat_cast n, ← of_real_inv n, of_real_re],
  rwa [← inv_mul_le_iff' _, inv_inv, ← sq, ← real.sqrt_le_sqrt_iff (sq_nonneg z.im), 
  real.sqrt_sq_eq_abs], simp only [nat.cast_pos, inv_pos, lt_of_lt_of_le zero_lt_one hn.out], 
end

-- The function F is bounded above because f is.
lemma F_bdd_above (f: ℂ → ℂ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))):
  bdd_above ((abs ∘ F f) '' (closed_strip 0 1)) :=
begin
  -- Bounding individual terms
    have hBM0: ∀ z ∈ (closed_strip 0 1),  abs((M f 0)^(z-1)) ≤ max 1 ((M f 0)^-(1:ℝ)),
    {intros z hset, rw [closed_strip, mem_preimage, Icc, mem_set_of_eq] at hset,
    cases (M_nonneg f 0) with hpos hzero, by_cases hM0_one : 1 ≤ M f 0,
    -- 1 ≤ M f 0
    apply le_trans _ (le_max_left 1 ((M f 0)^-(1:ℝ))),
    rw abs_cpow_eq_rpow_re_of_pos hpos, simp only [sub_re, one_re],
    apply real.rpow_le_one_of_one_le_of_nonpos hM0_one, simp only [sub_nonpos], exact hset.2,
    -- 0 < M f 0 < 1
    rw not_le at hM0_one, apply le_trans _ (le_max_right 1 ((M f 0)^-(1:ℝ))),
    simp only [abs_cpow_eq_rpow_re_of_pos hpos, sub_re, one_re],
    apply real.rpow_le_rpow_of_exponent_ge (hpos) (le_of_lt hM0_one), 
    simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left], exact hset.1,
    -- M f 0 = 0
    apply le_trans _ (le_max_left 1 ((M f 0)^-(1:ℝ))),
    by_cases hz1 : z=1, rw hz1, simp only [le_refl, map_one, cpow_zero, sub_self],
    rw [← hzero, of_real_zero, zero_cpow], simp only [zero_le_one, map_zero],
    rwa [ne.def, sub_eq_zero],
    },

    have hBM1: ∀ z ∈ (closed_strip 0 1),  abs((M f 1)^(-z)) ≤ max 1 ((M f 1)^-(1:ℝ)),
    {intros z hset, rw [closed_strip, mem_preimage, Icc, mem_set_of_eq] at hset,
    cases (M_nonneg f 1) with hpos hzero, by_cases hM1_one : 1 ≤ M f 1,
    -- 1 ≤ M f 1
    apply le_trans _ (le_max_left 1 ((M f 1)^-(1:ℝ))),
    rw abs_cpow_eq_rpow_re_of_pos hpos, simp only [sub_re, one_re],
    apply real.rpow_le_one_of_one_le_of_nonpos hM1_one, simp only [right.neg_nonpos_iff, neg_re],
    exact hset.1,
    -- 0 < M f 1 < 1
    rw not_le at hM1_one, apply le_trans _ (le_max_right 1 ((M f 1)^-(1:ℝ))),
    rw abs_cpow_eq_rpow_re_of_pos hpos, simp only [sub_re, one_re],
    apply real.rpow_le_rpow_of_exponent_ge (hpos) (le_of_lt hM1_one), 
    simp only [neg_le_neg_iff, neg_re], exact hset.2,
    -- M f 1 = 0
    apply le_trans _ (le_max_left 1 ((M f 1)^-(1:ℝ))),
    by_cases hz0 : z=0, rw hz0, rw ← hzero, simp only [le_refl, map_one, cpow_zero, neg_zero],
    rw [← hzero, of_real_zero, zero_cpow], simp only [zero_le_one, map_zero],
    rw ne.def, simp only [not_false_iff, neg_eq_zero, one_ne_zero], exact hz0,},

  
  -- rewriting goal
  simp only [F, image_congr, comp_app, map_mul], 
  rw bdd_above_def at *, cases hB with B hB,
  -- Using bound
  use B * ((max 1 ((M f 0)^-(1:ℝ))) * max 1 ((M f 1)^-(1:ℝ))), 
  simp only [smul_eq_mul, map_mul, mem_image, forall_exists_index,
   and_imp, forall_apply_eq_imp_iff₂], intros z hset, specialize hB (abs(f z)),
  specialize hB _, {simp only [image_congr, mem_image, comp_app], use z, split,
    rwa [closed_strip, mem_preimage], refl,},
  -- Proof that the bound is correct
  refine mul_le_mul hB _ _ _,
  -- zero case
  by_cases (M f 0) = 0 ∨ (M f 1) = 0, rw g_zero_def z f h, 
  simp only [zero_le_one, true_or, le_max_iff, zero_le_mul_right, map_zero],
  apply le_trans _ (mul_le_mul (le_max_left 1 ((M f 0)^-(1:ℝ)))
   (le_max_left 1 ((M f 1)^-(1:ℝ))) zero_le_one 
   (le_trans zero_le_one (le_max_left 1 ((M f 0)^-(1:ℝ))))),
  simp only [mul_one, zero_le_one],
  -- pos case
  push_neg at h, cases h with h0 h1, rw ne.def at *, rw eq_comm at h0 h1,
  rw g_pos_def z f (or.resolve_right (M_nonneg f 0) h0) (or.resolve_right (M_nonneg f 1) h1),
  simp only [map_mul], refine mul_le_mul (hBM0 z hset) (hBM1 z hset) _ _,
  simp only [map_nonneg], apply le_trans zero_le_one (le_max_left 1 ((M f 0)^-(1:ℝ))),
  simp only [map_nonneg], apply le_trans _ hB, simp only [map_nonneg], 
end


lemma F'_eventually_le_one (f: ℂ → ℂ) (n : ℕ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hn: n ∈ {m : ℕ | 1 ≤ m}) :
  ∃ T > 0,  ∀ (z : ℂ), z.re ∈ (Icc (0:ℝ)  1) → |z.im| ≥ T →  (abs ∘ (F' n f)) z ≤ 1 :=
begin
  rw F', cases (F_bdd_above f hB)  with C hF', rw mem_upper_bounds at hF',
  cases (Expterm_eventually_le_one n hn C) with T hExp, cases hExp with hT hExp, use T,
  split, exact hT,
  intros z hset him, simp only [comp_app, map_mul], specialize hExp z,
  specialize hExp hset, specialize hExp him, 
  simp only [algebra.id.smul_eq_mul, of_real_nat_cast, map_mul], 
  specialize hF' (abs (F f z)),
  -- Showing abs (F f z) ∈ abs ∘ F f '' closed_strip 0 1
  specialize hF' _, 
    {simp only [image_congr, mem_image, comp_app], use z, split,
    rw closed_strip, rw mem_preimage, exact hset, refl,},
  -- Combining hExp with hF' by trans
  apply le_trans _ hExp, apply mul_le_mul hF', apply le_of_eq, refl,
  simp only [map_nonneg], apply le_trans _ hF', simp only [map_nonneg],
end


-- Proofs that the edges are bounded by one
lemma F_edge_zero_le_one (f: ℂ → ℂ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z.re = 0):  abs (F f z) ≤ 1:=
begin
  rw F, simp only [algebra.id.smul_eq_mul, map_mul],
  cases (M_nonneg f 0) with hpos hzero, cases (M_nonneg f 1) with h1pos h1zero,
  rw g_pos_def z f hpos h1pos, simp only [map_mul, abs_cpow_eq_rpow_re_of_pos, hpos, h1pos,
  complex.sub_re, complex.one_re, complex.neg_re, hz, mul_one, zero_sub, real.rpow_zero, neg_zero,
  real.rpow_neg_one, mul_inv_le_iff hpos],
  rw ← hz, refine f_le_Sup f z _ hB,
  {simp only [closed_strip, mem_preimage, zero_le_one, set.left_mem_Icc, hz],}, 
  -- Handeling cases where M f 0 = 0, M f 1 = 0.
  rw g_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
  right, simp only [h1zero, eq_self_iff_true],
  rw g_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
  left, rw eq_comm, exact hzero,
end

--Same proof of F_edge_zero_le_one
lemma F_edge_one_le_one (f: ℂ → ℂ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z.re = 1):  abs (F f z) ≤ 1:=
begin
  rw F, simp only [algebra.id.smul_eq_mul, map_mul],
  cases (M_nonneg f 1) with h1pos h1zero, cases (M_nonneg f 0) with hpos hzero, 
  rw g_pos_def z f hpos h1pos, simp only [map_mul, abs_cpow_eq_rpow_re_of_pos, hpos, h1pos, 
  sub_re, one_re, neg_re, hz, one_mul, real.rpow_zero, sub_self, real.rpow_neg_one, 
  mul_inv_le_iff h1pos, mul_one],  
  rw ← hz, refine f_le_Sup f z _ hB, 
  {simp only [closed_strip, mem_preimage, zero_le_one, hz, right_mem_Icc],}, 
  -- Handeling cases where M f 0 = 0, M f 1 = 0.
  rw g_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
  left, rw eq_comm, exact hzero,
  rw g_zero_def z f, simp only [zero_le_one, mul_zero, map_zero], 
  right, simp only [h1zero, eq_self_iff_true],
end

-- Edges of F' are constructed to be ≤ 1
lemma edges_le_one (f: ℂ → ℂ) (n : ℕ) (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1)))
  (hz: z ∈ re ⁻¹' {0, 1}) :  (abs ∘ F' n f) z ≤ 1:=
begin
  -- Small useful lemma
  have hdivnat : 0 ≤ ((n:ℂ)⁻¹).re, 
  {simp only [← of_real_nat_cast n, ← of_real_inv n, of_real_re, inv_nonneg,nat.cast_nonneg],},

  -- Expterm ≤ 1
  have hexp : abs(exp ((z ^ 2 - 1) * (↑n)⁻¹)) ≤ 1, {rw abs_exp,
  rw ← re_add_im z,
  simp only [tsub_zero, sub_re, one_re, add_im, add_zero, mul_one, mul_re, 
    zero_div, zero_mul, of_real_re, add_re, one_im, nat_cast_im, of_real_im, I_im, 
    zero_add, inv_im, sq, sub_im, I_re, real.exp_le_one_iff, mul_im, mul_zero, neg_zero],
  cases hz with hz0 hz1,
  simp only [hz0, zero_sub, nat_cast_re, mul_zero], refine mul_nonpos_of_nonpos_of_nonneg _ hdivnat,
  simp only [← sq, sub_nonpos, neg_le], apply le_of_lt, 
  apply lt_of_lt_of_le neg_one_lt_zero (sq_nonneg z.im),
  rw hz1.out, simp only [right.neg_nonpos_iff, one_pow, neg_mul, sub_sub_cancel_left,← sq],
  rw mul_nonneg_iff, left, split, apply sq_nonneg, exact hdivnat,},

  -- Combining Expterm ≤ 1 with F ≤ 1 on edges
  rw F', rw mem_preimage at hz, simp only [algebra.id.smul_eq_mul, of_real_nat_cast, map_mul],
  simp only [comp_app, map_mul], cases hz with hz0 hz1,
  apply left.mul_le_one_of_le_of_le (F_edge_zero_le_one z f hB hz0) hexp (map_nonneg abs (F f z)),
  apply left.mul_le_one_of_le_of_le (F_edge_one_le_one z f hB hz1) hexp (map_nonneg abs (F f z)),
end


-- Combine bdd_Hadamard_sequence + tendsto 0
lemma Hadamard_sequence (f : ℂ → ℂ) (hd : diff_cont_on_cl ℂ f (strip 0 1)) (z : ℂ)
  (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))) (hz: z ∈ closed_strip 0 1) (n: ℕ) 
  (hn: n ∈ {m : ℕ | 1 ≤ m}) : (⇑abs ∘ F' n f) z ≤ 1 :=
begin
  cases (F'_eventually_le_one f n hB hn) with T hF', cases hF' with hT hF',
  by_cases (|z.im| ≤ T), 

  -- First case |z.im| ≤ T
    {-- Bounded domain 
    have bdd_strip_is_bounded : metric.bounded (bdd_strip 0 1 T),
    {apply ((bounded_Ioo _ _).re_prod_im (bounded_Ioo _ _)),},

    --Function is diff_cont_on_cl on subset + multiplied by 'simple' function
    have hd_subset : diff_cont_on_cl ℂ (F' n f) (bdd_strip 0 1 T),
    {refine diff_cont_on_cl.mono _ _, use strip 0 1, apply F'_diff_cont f n hd, 
    apply inter_subset_left},

    apply norm_le_of_forall_mem_frontier_norm_le bdd_strip_is_bounded hd_subset _ _, 

    -- Frontier bounded by one
    intro z, intro hfz, rw [bdd_strip, ← re_prod_im, frontier_re_prod_im] at hfz, 
    cases hfz with hfz1 hfz2, rotate, replace hfz2 := mem_of_mem_inter_left hfz2,
    rw frontier_Ioo at hfz2, apply edges_le_one z f n hB hfz2, exact (zero_lt_one' ℝ), rotate,
    cases hfz1 with hfz_re hfz_im, rw frontier_Ioo at hfz_im, rw closure_Ioo at hfz_re,
    apply hF' z hfz_re,
    -- |T| = |z.im|
    apply le_of_eq, rw ← abs_of_nonneg (le_of_lt hT), simp only [abs_of_real],
    rw [eq_comm, abs_eq_abs, or_comm], exact hfz_im, exact zero_ne_one' ℝ, 
    -- -T < T
    simp only [neg_lt_self_iff], exact hT,
    -- z ∈ closure (bdd_strip 0 1 T) →  z.re ∈ Icc 0 1
    --Local goal: z ∈ closure (bdd_strip 0 1 T) with h: |z.im| ≤ T and hz: z ∈ strip 0 1.
    rw [bdd_strip, ← re_prod_im, closure_re_prod_im, closure_Ioo, closure_Ioo,  
    re_prod_im, mem_inter_iff],
    split, rwa ← closed_strip, rw [mem_preimage, mem_Icc], simp only [← abs_le, h],  
    apply ne_of_lt,
    simp_rw [neg_lt_self_iff], exact hT, apply zero_ne_one' ℝ, 
    },

  --Local goal: (⇑abs ∘ F' n f) z ≤ 1 with h: |z.im| > T and hz: z ∈ strip 0 1.
  simp only [not_le] at h, apply hF', rw ← mem_preimage, exact hz,
  exact le_of_lt h,  
end


-- tendsto_inverse_at_top_nhds_0_nat with complex coercion.
-- I proved this using the definition of filter.tendsto. 
lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℂ)⁻¹) at_top (nhds 0) :=
begin
  rw tendsto_def, intros s hs, simp only [filter.mem_at_top_sets], rw metric.mem_nhds_iff at hs,
  cases hs with ε hs, cases hs with hε hsub, use nat.ceil ((ε:ℝ)⁻¹+1), 
  intros n hn, simp only [mem_preimage], simp only [ge_iff_le, nat.ceil_le] at hn,
  apply mem_of_subset_of_mem hsub, rw metric.mem_ball, 
  simp only [map_inv₀, abs_cast_nat, dist_zero_right, norm_eq_abs],
  apply inv_lt_of_inv_lt hε, apply lt_of_lt_of_le (lt_add_one (ε⁻¹)) hn,
end


--Proof that F_seq tendsto F
lemma F_seq_to_F (f : ℂ → ℂ) (z : ℂ) : tendsto (λ n : ℕ, F' n f z ) at_top (nhds (F f z)):=
begin
  have mul_const : tendsto (λ n : ℕ,  (z^2-1) * (n : ℝ)⁻¹) at_top (nhds 0), {
    by simpa only [mul_zero]
      using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat,
  },

  have comp_exp : tendsto (λ n : ℕ, exp( (z^2-1) * (n : ℝ)⁻¹)) at_top (nhds 1), {
    by simpa only [exp_zero]
      using  (continuous.tendsto continuous_exp 0).comp mul_const,
  },
  by simpa only [mul_one]
    using tendsto_const_nhds.mul comp_exp,
end

-- Proof that |F_seq| tendsto |F|
lemma F_seq_to_F_abs (f : ℂ → ℂ) (z : ℂ) :
tendsto (λ n : ℕ, (abs ∘ (F' n f)) z ) at_top (nhds ((abs ∘ (F f)) z)):=
  (continuous.tendsto continuous_abs (F f z)).comp (F_seq_to_F f z)

-- Combination of Hadamard_sequence with F_seq_to_F_abs
lemma Hadamard_three_lines_theorem_on_zero_one (f : ℂ → ℂ) (hd : diff_cont_on_cl ℂ f (strip 0 1))  (z : ℂ)
  (hB : bdd_above ((abs ∘ f) '' (closed_strip 0 1))) :
   ∀ z ∈ closed_strip 0 1, (abs ∘ (F f)) z ≤ 1 := 
begin
  intros z hz,
  apply le_of_tendsto (F_seq_to_F_abs f z) _,
  rw filter.eventually_iff_exists_mem, use {n:ℕ | 1 ≤ n}, split, apply filter.mem_at_top, 
  apply Hadamard_sequence f hd z hB hz,
end


end complex
