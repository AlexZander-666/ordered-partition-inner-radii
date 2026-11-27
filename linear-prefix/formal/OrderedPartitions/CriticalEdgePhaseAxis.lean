import OrderedPartitions.CriticalEdgePhaseRegularity

/-! Exclusion of off-axis complex zeros in the split-pole coordinate. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set

/-- The projection onto the imaginary axis. Its norm is at most the original norm. -/
def imaginaryProjection (z : ℂ) : ℂ := (z.im : ℂ) * Complex.I

theorem norm_imaginaryProjection_le (z : ℂ) : ‖imaginaryProjection z‖ ≤ ‖z‖ := by
  simpa only [imaginaryProjection, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    using Complex.abs_im_le_norm z

theorem sub_imaginaryProjection (z : ℂ) : z - imaginaryProjection z = (z.re : ℂ) :=
  sub_eq_iff_eq_add.mpr (by simpa only [imaginaryProjection] using (Complex.re_add_im z).symm)

/-- Uniform derivative bounds control the real change from the imaginary projection. -/
theorem horizontal_real_bound {F : ℂ → ℂ} {r B : ℝ} {v : ℂ} (hv : ‖v‖ ≤ r)
    (diff : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ F z)
    (bound : ∀ z ∈ closedBall (0 : ℂ) r, ‖deriv F z‖ ≤ B)
    (axis : (F (imaginaryProjection v)).re = 0) :
    |(F v).re| ≤ B * |v.re| := by
  have vmem : v ∈ closedBall (0 : ℂ) r := by simpa only [mem_closedBall, dist_zero_right] using hv
  have pmem : imaginaryProjection v ∈ closedBall (0 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_right] using (norm_imaginaryProjection_le v).trans hv
  have lip := Convex.norm_image_sub_le_of_norm_deriv_le diff bound (convex_closedBall (0 : ℂ) r) pmem vmem
  rw [sub_imaginaryProjection, Complex.norm_real, Real.norm_eq_abs] at lip
  have mid := Complex.abs_re_le_norm (F v - F (imaginaryProjection v))
  rw [Complex.sub_re, axis, sub_zero] at mid
  exact mid.trans lip

/-- A function with derivative close to a positive multiple of the identity
expands the real part away from the imaginary axis. -/
theorem phase_horizontal_lower {F : ℂ → ℂ} {r N B : ℝ} {v : ℂ} (hv : ‖v‖ ≤ r) (N0 : 0 ≤ N)
    (diff : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ F z)
    (bound : ∀ z ∈ closedBall (0 : ℂ) r, ‖deriv F z - (N : ℂ)‖ ≤ B)
    (axis : (F (imaginaryProjection v)).re = 0) :
    (N - B) * |v.re| ≤ |(F v).re| := by
  let G : ℂ → ℂ := F - (fun z ↦ (N : ℂ) * z)
  have dg (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      HasDerivAt G (deriv F z - (N : ℂ)) z := by
    have dl : HasDerivAt (fun x : ℂ ↦ (N : ℂ) * x) (N : ℂ) z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (N : ℂ)
    exact (diff z hz).hasDerivAt.sub dl
  have gp : (G (imaginaryProjection v)).re = 0 := by
    change (F (imaginaryProjection v) - (N : ℂ) * imaginaryProjection v).re = 0
    rw [Complex.sub_re, axis]
    simp [imaginaryProjection, Complex.mul_re]
  have hb := horizontal_real_bound hv (fun z hz ↦ (dg z hz).differentiableAt)
    (fun z hz ↦ by rw [(dg z hz).deriv]; exact bound z hz) gp
  have express : (G v).re = (F v).re - N * v.re := by
    simp [G, Complex.mul_re]
  rw [express] at hb
  have tri := abs_sub_abs_le_abs_sub (N * v.re) (F v).re
  rw [abs_mul, abs_of_nonneg N0, abs_sub_comm] at tri
  linarith only [hb,tri]

#print axioms horizontal_real_bound
#print axioms phase_horizontal_lower

end OrderedPartitions.CriticalEdge
