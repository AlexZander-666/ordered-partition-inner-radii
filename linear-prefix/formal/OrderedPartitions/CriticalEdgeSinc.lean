import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Evaluation of the limiting quadratic contour by the entire sinc series. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter

/-- The entire continuation of `sin (sqrt u) / sqrt u`, expressed without a branch. -/
def innerSinc (u : ℂ) : ℂ := ∑' m : ℕ, (-u) ^ m / ((2 * m + 1).factorial : ℂ)

@[simp] theorem innerSinc_zero : innerSinc 0 = 1 := by
  rw [innerSinc, tsum_eq_single 0 (fun m hm ↦ by simp [zero_pow hm])]
  norm_num

theorem innerSinc_of_square {u w : ℂ} (hw : w ^ 2 = -u) (w0 : w ≠ 0) :
    innerSinc u = Complex.sinh w / w := by
  have sum := (Complex.hasSum_sinh w).div_const w
  have funEq (m : ℕ) : w ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ) / w =
      (-u) ^ m / ((2 * m + 1).factorial : ℂ) := by
    rw [pow_succ, pow_mul, hw]
    field_simp [w0]
  exact (sum.congr_fun fun m ↦ (funEq m).symm).tsum_eq

/-- Cauchy's formulas evaluate the limiting integral, including the double pole at `u=0`. -/
theorem limiting_contour_eq_sinc {M : ℝ} (hM : 0 < M) {u : ℂ} (hu : ‖u‖ < M ^ 2) :
    -((2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), Complex.exp (-v) / (v ^ 2 + u)) =
      innerSinc u := by
  let f := fun v : ℂ ↦ Complex.exp (-v)
  have fd : Differentiable ℂ f := Complex.differentiable_exp.comp differentiable_neg
  by_cases u0 : u = 0
  · subst u
    have d : deriv f 0 = -1 := by
      have h := (Complex.hasDerivAt_exp (-(0 : ℂ))).comp 0 (hasDerivAt_neg (0 : ℂ))
      simpa [f, Function.comp_def] using h.deriv
    have eq := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
      (c := (0 : ℂ)) (f := f) (s := ∅) hM 1 countable_empty fd.continuous.continuousOn
      (fun z _ ↦ fd z)
    simp only [sub_zero, Nat.factorial_one, Nat.cast_one, div_one, Nat.reduceAdd,
      smul_eq_mul, iteratedDeriv_one, d] at eq
    have integral : (∮ v in C(0, M), Complex.exp (-v) / (v ^ 2 + 0)) =
        ∮ v in C(0, M), (1 / v ^ 2) * f v := by
      apply circleIntegral.integral_congr hM.le
      intro z _
      change f z / (z ^ 2 + 0) = (1 / z ^ 2) * f z
      simp only [add_zero, div_eq_mul_inv]
      ring
    rw [integral, eq, innerSinc_zero, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul, neg_neg]
  · let w := (-u) ^ ((2 : ℂ)⁻¹)
    have ww : w ^ 2 = -u := Complex.cpow_ofNat_inv_pow (-u) 2
    have w0 : w ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at ww
      exact u0 (neg_eq_zero.mp ww.symm)
    have normw : ‖w‖ < M := by
      have sq : ‖w‖ ^ 2 = ‖u‖ := by rw [← norm_pow, ww, norm_neg]
      exact (sq_lt_sq₀ (norm_nonneg _) hM.le).mp (sq.trans_lt hu)
    have inside : w ∈ ball (0 : ℂ) M := by simpa only [mem_ball, dist_zero_right] using normw
    have inside' : -w ∈ ball (0 : ℂ) M := by simpa only [mem_ball, dist_zero_right, norm_neg] using normw
    have integrable (p : ℂ) (hp : p ∈ ball (0 : ℂ) M) :
        CircleIntegrable (fun v ↦ (v - p)⁻¹ * f v) 0 M := by
      apply ContinuousOn.circleIntegrable hM.le
      exact ((continuousOn_id.sub continuousOn_const).inv₀ (fun z hz ↦ sub_ne_zero.mpr fun e ↦ by
        change z=p at e
        exact (mem_ball.mp hp).ne (e ▸ mem_sphere.mp hz))).mul fd.continuous.continuousOn
    have eval (p : ℂ) (hp : p ∈ ball (0 : ℂ) M) :
        (∮ v in C(0, M), (v - p)⁻¹ * f v) = (2 * (Real.pi : ℂ) * I) * f p := by
      simpa only [smul_eq_mul] using fd.differentiableOn.circleIntegral_sub_inv_smul hp
    have integral : (∮ v in C(0, M), Complex.exp (-v) / (v ^ 2 + u)) =
        (2 * w)⁻¹ * ∮ v in C(0, M), (v - w)⁻¹ * f v - (v - (-w))⁻¹ * f v := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hM.le
      intro z hz
      have normz : ‖z‖ = M := by simpa only [mem_sphere, dist_zero_right] using hz
      have z1 : z - w ≠ 0 := sub_ne_zero.mpr fun e ↦ normw.ne (e ▸ normz)
      have z2 : z - (-w) ≠ 0 := sub_ne_zero.mpr fun e ↦ by
        have h := congrArg (fun v : ℂ ↦ ‖v‖) e
        rw [normz, norm_neg] at h
        exact normw.ne h.symm
      change f z / (z ^ 2 + u) = (2 * w)⁻¹ * ((z - w)⁻¹ * f z - (z - (-w))⁻¹ * f z)
      rw [show z ^ 2 + u = (z - w) * (z - (-w)) by rw [show u= -w^2 from by rw [ww,neg_neg]]; ring]
      field_simp [z1, z2, w0]
      ring
    rw [integral, circleIntegral.integral_sub (integrable w inside) (integrable (-w) inside'),
      eval w inside, eval (-w) inside', innerSinc_of_square ww w0]
    simp only [f, neg_neg, smul_eq_mul, Complex.sinh]
    field_simp [Complex.two_pi_I_ne_zero, w0, Complex.I_ne_zero, Real.pi_ne_zero]
    ring

#print axioms innerSinc_of_square
#print axioms limiting_contour_eq_sinc

end OrderedPartitions.CriticalEdge
