import OrderedPartitions.CriticalEdgeGlobalRank
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Real phase cells with rank-uniform constants for simple zeros of perturbed sine. -/
noncomputable section
namespace OrderedPartitions.CriticalEdgeRank
open Real Set

/-- In one phase cell, small C¹ errors preserve a unique simple zero. The
phase error at that zero is bounded by twice the actual perturbation. -/
theorem unique_sine_cell {φ e : ℝ → ℝ} {l r p η : ℝ} (lr : l<r)
    (left : φ l=p-π/4) (right : φ r=p+π/4) (small : η≤1/4)
    (phase : ∀ t ∈ Icc l r, DifferentiableAt ℝ φ t ∧ 1≤deriv φ t)
    (err : ∀ t ∈ Icc l r, DifferentiableAt ℝ e t ∧ |e t|≤η ∧ |deriv e t|≤1/4) :
    ∃ y ∈ Ioo l r, sin (φ y-p)+e y=0 ∧ |φ y-p|≤2*|e y| ∧
      0<deriv (fun t ↦ sin (φ t-p)+e t) y ∧
      ∀ z ∈ Icc l r, sin (φ z-p)+e z=0 → z=y := by
  let F := fun t ↦ sin (φ t-p)+e t
  have phaseCont : ContinuousOn φ (Icc l r) := fun t ht ↦ (phase t ht).1.continuousAt.continuousWithinAt
  have pm := strictMonoOn_of_deriv_pos (convex_Icc l r) phaseCont (fun t ht ↦
    zero_lt_one.trans_le (phase t (interior_subset ht)).2)
  have bound {t : ℝ} (ht : t∈Icc l r) : |φ t-p|≤π/4 := by
    have low := pm.monotoneOn (left_mem_Icc.mpr lr.le) ht ht.1
    have high := pm.monotoneOn ht (right_mem_Icc.mpr lr.le) ht.2
    rw [left] at low
    rw [right] at high
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have derivF (t : ℝ) (ht : t∈Icc l r) :
      HasDerivAt F (cos (φ t-p)*deriv φ t+deriv e t) t := by
    dsimp [F]
    simpa only [Pi.add_apply, one_mul, mul_one] using
      (((phase t ht).1.hasDerivAt.sub_const p).sin.fun_add (err t ht).1.hasDerivAt)
  have cF : ContinuousOn F (Icc l r) := fun t ht ↦ (derivF t ht).continuousAt.continuousWithinAt
  have dpos {t : ℝ} (ht : t∈Icc l r) : 0<deriv F t := by
    have c := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (φ t-p)) (by linarith [pi_pos] : π/4≤π) (bound ht)
    rw [cos_abs] at c
    have hc : 1/2 ≤ cos (φ t-p) := by rw [cos_pi_div_four] at c; linarith [Real.one_le_sqrt.mpr (by norm_num : (1:ℝ)≤2)]
    have prod := mul_le_mul_of_nonneg_left (phase t ht).2 (show 0≤cos (φ t-p) by linarith)
    have de := (abs_le.mp (err t ht).2.2).1
    rw [(derivF t ht).deriv]
    linarith
  have fm := strictMonoOn_of_deriv_pos (convex_Icc l r) cF (fun _ h ↦ dpos (interior_subset h))
  have sinL : 1/2 ≤ sin (π/4) := by rw [sin_pi_div_four]; linarith [Real.one_le_sqrt.mpr (by norm_num : (1:ℝ)≤2)]
  have sl : F l<0 := by
    dsimp [F]; rw [left,show p-π/4-p= -(π/4) by ring,sin_neg]
    linarith [(le_abs_self (e l)).trans (err l (left_mem_Icc.mpr lr.le)).2.1]
  have sr : 0<F r := by
    dsimp [F]; rw [right,add_sub_cancel_left]
    linarith [(abs_le.mp (err r (right_mem_Icc.mpr lr.le)).2.1).1]
  obtain ⟨y,hy,zr⟩ := intermediate_value_Ioo lr.le cF (show 0∈Ioo (F l) (F r) from ⟨sl,sr⟩)
  have ym := Ioo_subset_Icc_self hy
  refine ⟨y,hy,zr,?_,dpos ym,fun z zm zz ↦ fm.injOn zm ym (zz.trans zr.symm)⟩
  have s : sin (φ y-p)= -e y := by change sin (φ y-p)+e y=0 at zr; linarith
  have jor := mul_abs_le_abs_sin (le_trans (bound ym) (by linarith [pi_pos] : π/4≤π/2))
  rw [s,abs_neg] at jor
  have half : 1/2 ≤ 2/π := (le_div_iff₀ pi_pos).mpr (by linarith [pi_lt_four])
  linarith [mul_le_mul_of_nonneg_right half (abs_nonneg (φ y-p))]

#print axioms unique_sine_cell

/-- A small complex error whose real component vanishes to first order
on the imaginary axis forces every solution to stay on that axis. -/
theorem transverse_real {v L E : ℂ} (eqn : Complex.sinh L = E) (small : ‖E‖ ≤ 1/4)
    (transverse : |E.re| ≤ |v.re|/4) (lower : |v.re| ≤ |L.re|) : v.re = 0 := by
  have split : Complex.sinh L =
      (sinh L.re : ℂ) * cos L.im + (cosh L.re : ℂ) * (sin L.im * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im L, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp
  have him := congrArg Complex.im (eqn.symm.trans split)
  have hre := congrArg Complex.re (eqn.symm.trans split)
  simp [Complex.mul_re,Complex.mul_im] at him hre
  change E.im = cosh L.re * sin L.im at him
  change E.re = sinh L.re * cos L.im at hre
  have imag := (Complex.abs_im_le_norm E).trans small
  rw [him,abs_mul,abs_of_nonneg (cosh_pos _).le] at imag
  have sb : |sin L.im| ≤ 1/4 := by
    linarith [mul_le_mul_of_nonneg_right (one_le_cosh L.re) (abs_nonneg (sin L.im))]
  have cb : 1/2 ≤ |cos L.im| := by
    by_contra! h
    nlinarith [sq_abs (sin L.im),sq_abs (cos L.im),sin_sq_add_cos_sq L.im,
      mul_self_le_mul_self (abs_nonneg _) sb,
      mul_self_lt_mul_self (abs_nonneg _) h]
  have xb : |L.re| ≤ |sinh L.re| := by
    rcases le_total 0 L.re with h | h
    · simpa only [abs_of_nonneg h, abs_of_nonneg (sinh_nonneg_iff.mpr h)] using self_le_sinh_iff.mpr h
    · simpa only [abs_of_nonpos h, abs_of_nonpos (sinh_nonpos_iff.mpr h)] using neg_le_neg (sinh_le_self_iff.mpr h)
  rw [hre,abs_mul] at transverse
  have prod := mul_le_mul xb cb (by norm_num : (0:ℝ) ≤ 1/2) (abs_nonneg _)
  apply abs_eq_zero.mp
  linarith [abs_nonneg v.re]

#print axioms transverse_real
end OrderedPartitions.CriticalEdgeRank
