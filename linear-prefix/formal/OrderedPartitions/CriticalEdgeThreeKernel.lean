import OrderedPartitions.CriticalEdgeSmallBarrier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The quadratic Taylor remainder of exp separates the complex poles at threshold three. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Complex Set MeasureTheory
open scoped Interval

private def quadIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  (1-(t:ℂ))*Complex.exp ((t:ℂ)*w)

def quadKernel (w : ℂ) : ℂ := ∫ t in (0:ℝ)..1, quadIntegrand w t

theorem quadKernel_exact (w : ℂ) : w^2*quadKernel w = Complex.exp w-1-w := by
  let prim := fun t : ℝ ↦ Complex.exp ((t:ℂ)*w) * (1+w*(1-(t:ℂ)))
  have h (t : ℝ) : HasDerivAt prim (w^2*quadIntegrand w t) t := by
    have idc : HasDerivAt (fun t : ℝ ↦ (t:ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
    have expd := (idc.mul_const w).cexp
    have aff := ((idc.const_sub (1:ℂ)).const_mul w).const_add (1:ℂ)
    apply (expd.mul aff).congr_deriv
    unfold quadIntegrand
    ring
  have intg : Continuous (fun t : ℝ ↦ w^2*quadIntegrand w t) := by unfold quadIntegrand; fun_prop
  rw [quadKernel,← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ h t) (intg.intervalIntegrable _ _)]
  simp [prim]; ring

private theorem kernel_im_pos {w : ℂ} (lo : 0<w.im) (hi : w.im<Real.pi) :
    0<(quadKernel w).im := by
  have ct : Continuous (quadIntegrand w) := by unfold quadIntegrand; fun_prop
  have sm (t : ℝ) : (quadIntegrand w t).im =
      (1-t)*Real.exp (t*w.re)*Real.sin (t*w.im) := by
    unfold quadIntegrand
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,im_ofReal_mul,exp_im,re_ofReal_mul,im_ofReal_mul]
    ring
  have ei := Complex.imCLM.intervalIntegral_comp_comm (ct.intervalIntegrable (μ:=volume) 0 1)
  change 0 < Complex.imCLM (∫ t in (0:ℝ)..1, quadIntegrand w t)
  rw [← ei]
  apply intervalIntegral.integral_pos zero_lt_one (Complex.continuous_im.comp ct).continuousOn
  · intro t ht
    change 0 ≤ (quadIntegrand w t).im
    rw [sm]
    have ub : t*w.im ≤ Real.pi := (mul_le_of_le_one_left lo.le ht.2).trans hi.le
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (Real.exp_pos _).le)
      (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht.1.le lo.le) ub)
  · refine ⟨1/2,by constructor <;> norm_num,?_⟩
    change 0 < (quadIntegrand w (1/2)).im
    rw [sm]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith))

theorem quadKernel_real_mono : Monotone fun v : ℝ ↦ (quadKernel v).re := by
  intro x y xy
  have eq (a : ℝ) : (quadKernel a).re = ∫ t in (0:ℝ)..1, (1-t)*Real.exp (t*a) := by
    have ct : Continuous (quadIntegrand (a:ℂ)) := by unfold quadIntegrand; fun_prop
    change Complex.reCLM (∫ t in (0:ℝ)..1, quadIntegrand (a:ℂ) t) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm (ct.intervalIntegrable (μ:=volume) 0 1)]
    apply intervalIntegral.integral_congr
    intro t _
    simp [quadIntegrand,←Complex.ofReal_mul,←Complex.ofReal_exp]
  change (quadKernel (x:ℂ)).re ≤ (quadKernel (y:ℂ)).re
  rw [eq,eq]
  apply intervalIntegral.integral_mono_on zero_le_one
    ((by fun_prop : Continuous fun t : ℝ ↦ (1-t)*Real.exp (t*x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ ↦ (1-t)*Real.exp (t*y)).intervalIntegrable _ _)
  intro t ht
  gcongr
  · exact sub_nonneg.mpr ht.2
  · exact ht.1

theorem quadKernel_real_of_real_value {w : ℂ} (small : |w.im|<Real.pi)
    (realv : (quadKernel w).im=0) : w.im=0 := by
  rcases lt_trichotomy w.im 0 with neg|eq|pos
  · have conjEq : quadKernel (star w)=star (quadKernel w) := by
      by_cases wn : w=0
      · simp [wn] at neg
      have nne : (star w)^2≠0 := pow_ne_zero _ (by simpa using wn)
      apply mul_left_cancel₀ nne
      rw [quadKernel_exact]
      change Complex.exp ((starRingEnd ℂ) w)-1-(starRingEnd ℂ) w = _
      rw [Complex.exp_conj]
      simpa only [Complex.star_def,map_mul,map_pow,map_sub,map_one] using (congrArg (starRingEnd ℂ) (quadKernel_exact w)).symm
    have p : 0 < (star w).im := by simpa using neg
    have q : (star w).im < Real.pi := by simpa [abs_of_neg neg] using small
    have hp := kernel_im_pos p q
    rw [conjEq] at hp
    simp [realv] at hp
  · exact eq
  · exact False.elim ((kernel_im_pos pos (by simpa [abs_of_pos pos] using small)).ne' realv)

#print axioms quadKernel_exact
#print axioms quadKernel_real_mono
#print axioms quadKernel_real_of_real_value
end OrderedPartitions.CriticalEdge
