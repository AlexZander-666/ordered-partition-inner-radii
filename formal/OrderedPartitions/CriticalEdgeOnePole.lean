import OrderedPartitions.CriticalEdgeCircle
import OrderedPartitions.CriticalEdgeDisk
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The unique simple denominator zero on the subcritical parameter disk. -/

noncomputable section

namespace OrderedPartitions.CriticalEdgeCircle

open Finset Set
open scoped ComplexConjugate

private theorem unperturbed_zero_iff {a : ℝ} (ha : a ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ a) :
    (2 : ℂ) - Complex.exp z = 0 ↔ z = ((Real.log 2 : ℝ) : ℂ) := by
  have hr : Complex.exp ((Real.log 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_cast
  constructor
  · intro h
    have habs : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans (hz.trans ha)
    have zband := abs_le.mp habs
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi (x := z) (y := (Real.log 2 : ℝ))
      (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
      (by rw [Complex.ofReal_im]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [Complex.ofReal_im]; exact Real.pi_pos.le)
    exact (sub_eq_zero.mp h).symm.trans hr.symm
  · intro he
    rw [he, hr, sub_self]

private theorem unperturbed_differentiable :
    Differentiable ℂ (fun z : ℂ ↦ (2 : ℂ) - Complex.exp z) :=
  (differentiable_const (c := (2 : ℂ))).sub Complex.differentiable_exp

private theorem unperturbed_simple (z : ℂ) :
    deriv (fun w : ℂ ↦ (2 : ℂ) - Complex.exp w) z ≠ 0 := by
  have h := ((hasDerivAt_const z (2 : ℂ)).sub (Complex.hasDerivAt_exp z)).deriv
  change deriv (fun w : ℂ ↦ (2 : ℂ) - Complex.exp w) z = 0 - Complex.exp z at h
  rw [h, zero_sub]
  exact neg_ne_zero.mpr (Complex.exp_ne_zero z)

/-- The entire denominator can be differentiated at every complex argument. -/
theorem denominator_differentiable (j : ℕ) (s : ℂ) : Differentiable ℂ (denominator j s) := by
  unfold denominator tailComplex
  exact unperturbed_differentiable.add ((Complex.differentiable_exp.sub
    (Differentiable.fun_sum fun n _ ↦ (differentiable_id.pow n).div_const _)).const_mul s)

/-- The denominator has constant coefficient 1 for positive thresholds. -/
theorem denominator_at_zero {j : ℕ} (hj : 1 ≤ j) (s : ℂ) : denominator j s 0 = 1 := by
  have h : (∑ n ∈ range j, (0 : ℂ) ^ n / (n.factorial : ℂ)) = 1 := by
    rw [sum_eq_single 0]
    · norm_num
    · intro n _ hn
      simp [zero_pow hn]
    · intro hn
      exact (hn (mem_range.mpr hj)).elim
  norm_num [denominator, tailComplex, h]

/-- The complex denominator restricts to the exponential truncation on the real axis. -/
theorem denominator_ofReal (j : ℕ) (s x : ℝ) :
    denominator j s x = ((2 - Real.exp x + s *
      (Real.exp x - ∑ n ∈ range j, x ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) := by
  push_cast
  rfl

/-- Conjugation preserves the denominator and its parameter. -/
theorem denominator_conj (j : ℕ) (s z : ℂ) :
    denominator j (conj s) (conj z) = conj (denominator j s z) := by
  simp [denominator, tailComplex, map_sum, Complex.conj_ofNat]

/-- Strict subcritical parameters give exactly one zero on the closed critical disk,
and it is simple and interior. -/
theorem subcritical_one_simple_pole {j : ℕ} {a C : ℝ} {s : ℂ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (hC : C * (Real.exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = Real.exp a - 2)
    (hs : ‖s‖ < C) :
    ∃ z : ℂ, ‖z‖ < a ∧ denominator j s z = 0 ∧ deriv (denominator j s) z ≠ 0 ∧
      ∀ w : ℂ, ‖w‖ ≤ a → denominator j s w = 0 → w = z := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply CriticalEdgeDisk.one_simple_zero (F := fun z : ℂ ↦ (2 : ℂ) - Complex.exp z)
    (p := ((Real.log 2 : ℝ) : ℂ)) (hlog.trans ha)
  · rwa [Complex.norm_real, Real.norm_of_nonneg hlog.le]
  · exact unperturbed_differentiable
  · exact denominator_differentiable j s
  · exact fun z hz ↦ unperturbed_zero_iff ha₁ hz
  · exact unperturbed_simple _
  · intro z hz
    have h : denominator j s z - ((2 : ℂ) - Complex.exp z) = s * tailComplex j z := by
      unfold denominator
      ring
    rw [h]
    exact boundary_dominance ha ha₁ hz hC hs.le (.inl hs)

/-- For a real subcritical parameter the unique simple denominator zero is real. -/
theorem subcritical_one_real_pole {j : ℕ} {a C s : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (hC : C * (Real.exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = Real.exp a - 2)
    (hs : |s| < C) :
    ∃ x : ℝ, |x| < a ∧ denominator j s x = 0 ∧ deriv (denominator j s) x ≠ 0 ∧
      ∀ w : ℂ, ‖w‖ ≤ a → denominator j s w = 0 → w = (x : ℂ) := by
  obtain ⟨z, hz, hzero, hdz, uniq⟩ := subcritical_one_simple_pole ha ha₁ hC
    (show ‖(s : ℂ)‖ < C by simpa only [Complex.norm_real, Real.norm_eq_abs] using hs)
  have hc : conj z = z := uniq (conj z) (by simpa only [Complex.norm_conj] using hz.le) (by
    rw [← Complex.conj_ofReal s, denominator_conj, hzero, map_zero])
  have he : (z.re : ℂ) = z := by simpa only [Complex.conj_eq_iff_re] using hc
  refine ⟨z.re, ?_, by rwa [he], by rwa [he], ?_⟩
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using (show ‖(z.re : ℂ)‖ < a by rwa [he])
  · intro w hw hzero'
    simpa only [he] using uniq w hw hzero'

/-- For positive thresholds, real subcritical parameters put the sole pole on `(0,a)`. -/
theorem subcritical_one_positive_pole {j : ℕ} (hj : 1 ≤ j) {a C s : ℝ}
    (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (hC : C * (Real.exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = Real.exp a - 2)
    (hs : |s| < C) :
    ∃ x ∈ Ioo 0 a, denominator j s x = 0 ∧ deriv (denominator j s) x ≠ 0 ∧
      ∀ w : ℂ, ‖w‖ ≤ a → denominator j s w = 0 → w = (x : ℂ) := by
  let f := fun x : ℝ ↦ (denominator j (s : ℂ) (x : ℂ)).re
  have zero : f 0 = 1 := by simp [f, denominator_at_zero hj]
  have ha₀ : 0 < a := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have he : 2 < Real.exp a := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr ha
  have ht : 0 < Real.exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ) := by
    exact pos_of_mul_pos_right (a := C) (by linarith only [hC, he]) ((abs_nonneg s).trans hs.le)
  have fa : f a < 0 := by
    dsimp only [f]
    rw [denominator_ofReal, Complex.ofReal_re]
    have h₀ := mul_neg_of_neg_of_pos (sub_neg.mpr ((le_abs_self s).trans_lt hs)) ht
    linarith only [h₀, hC]
  have hcont : Continuous f := Complex.continuous_re.comp
    ((denominator_differentiable j s).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' ha₀.le hcont.continuousOn
    (show 0 ∈ Ioo (f a) (f 0) from ⟨fa, zero.symm ▸ zero_lt_one⟩)
  have xzero : denominator j s x = 0 := by
    change f x = 0 at hfx
    dsimp only [f] at hfx
    rw [denominator_ofReal, Complex.ofReal_re] at hfx
    rw [denominator_ofReal, hfx, Complex.ofReal_zero]
  obtain ⟨p, _, _, hderiv, uniq⟩ := subcritical_one_real_pole ha ha₁ hC hs
  have xp := uniq (x : ℂ) (by simpa only [Complex.norm_real, Real.norm_of_nonneg hx.1.le] using hx.2.le) xzero
  exact ⟨x, hx, xzero, xp.symm ▸ hderiv, fun w hw hz ↦ (uniq w hw hz).trans xp.symm⟩

#print axioms denominator_differentiable
#print axioms denominator_at_zero
#print axioms denominator_ofReal
#print axioms denominator_conj
#print axioms subcritical_one_simple_pole
#print axioms subcritical_one_real_pole
#print axioms subcritical_one_positive_pole

end OrderedPartitions.CriticalEdgeCircle
