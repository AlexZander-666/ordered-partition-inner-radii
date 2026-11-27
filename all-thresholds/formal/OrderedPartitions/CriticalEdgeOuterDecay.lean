import OrderedPartitions.CriticalEdgeKernelLimit

/-! The outer contour contributes an exponentially decaying normalized error. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter
open scoped Topology

/-- A fixed circle without critical zeros has a positive denominator margin for every
bounded rescaled parameter, uniformly in all sufficiently large rows. -/
theorem outer_contour_eventual_lower {k : ℕ} {a R : ℝ} (hR : 0 < R)
    (edge : ∀ z : ℂ, ‖z‖ = R → generatingDen (k + 2) (ratio k a) z ≠ 0) (U : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop, ∀ u ∈ closedBall (0 : ℂ) U,
      ∀ z : ℂ, ‖z‖ = R → b ≤ ‖generatingDen (k + 2) (edgeActivity k a n u) z‖ := by
  let D0 := generatingDen (k + 2) (ratio k a)
  have cont : Continuous D0 := (CriticalEdgeCircle.denominator_differentiable _ _).continuous
  have nonempty : (sphere (0 : ℂ) R).Nonempty := by
    refine ⟨(R : ℂ), ?_⟩
    simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hR.le]
  obtain ⟨w, hw, minw⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn nonempty cont.norm.continuousOn
  have wn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
  have pos : 0 < ‖D0 w‖ := norm_pos_iff.mpr (edge w wn)
  let F := fun x : ℂ × (ℂ × ℂ) ↦ generatingDen (k + 2)
    ((ratio k a : ℂ) + (edgeWidth k a : ℂ) * x.2.1 * x.1 ^ 2) x.2.2
  have hc : Continuous F := by unfold F generatingDen; fun_prop
  have K := (isCompact_closedBall (0 : ℂ) U).prod (isCompact_sphere (0 : ℂ) R)
  have close := Metric.tendstoUniformlyOn_iff.mp
    (compact_parameter_uniform K fun _ _ ↦ hc.continuousAt) (‖D0 w‖ / 2) (half_pos pos)
  refine ⟨‖D0 w‖ / 2, half_pos pos, ?_⟩
  filter_upwards [close] with n hn
  intro u hu z hz
  have zsp : z ∈ sphere (0 : ℂ) R := by simpa only [mem_sphere, dist_zero_right] using hz
  have h := hn (u, z) ⟨hu, zsp⟩
  have h0 : dist (D0 z) (generatingDen (k + 2) (edgeActivity k a n u) z) < ‖D0 w‖ / 2 := by
    simpa only [F, edgeActivity, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] using h
  have htri := norm_sub_norm_le (D0 z) (generatingDen (k + 2) (edgeActivity k a n u) z)
  rw [dist_eq_norm] at h0
  have hmin : ‖D0 w‖ ≤ ‖D0 z‖ := minw zsp
  linarith only [h0, htri, hmin]

/-- Uniform vanishing of the scaled outer integral on each bounded mark set. -/
theorem outer_contour_tendsto_uniformly {k : ℕ} {a R : ℝ} (ha : 0 < a) (Ra : a < R)
    (edge : ∀ z : ℂ, ‖z‖ = R → generatingDen (k + 2) (ratio k a) z ≠ 0) (U : ℝ) :
    TendstoUniformlyOn (fun n : ℕ ↦ fun u : ℂ ↦ edgeCoefficientScale k a n *
      circleRemainder (generatingDen (k + 2) (edgeActivity k a n u)) R n) (fun _ ↦ 0)
      atTop (closedBall (0 : ℂ) U) := by
  have Rp := ha.trans Ra
  obtain ⟨b, bp, e⟩ := outer_contour_eventual_lower Rp edge U
  let J := a * ((k : ℝ) + 1)
  let crit := fun n : ℕ ↦ (J / b) * (a / R) ^ n
  have converge : Tendsto crit atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha.le Rp.le) ((div_lt_one Rp).mpr Ra)
    simpa only [crit, mul_zero] using h.const_mul (J / b)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [e, eventually_ge_atTop (1 : ℕ), converge.eventually (gt_mem_nhds hε)] with n hn n1 nc
  intro u hu
  let g := generatingDen (k + 2) (edgeActivity k a n u)
  have rn := norm_circleRemainder_le (g := g) Rp bp (hn u hu) n
  have scale : ‖edgeCoefficientScale k a n‖ ≤ a ^ n * J := by
    have kn : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    unfold edgeCoefficientScale
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_of_nonneg ha.le, kn, norm_inv,
      Complex.norm_natCast]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast n1))
  change dist 0 (edgeCoefficientScale k a n * circleRemainder g R n) < ε
  rw [dist_zero_left, norm_mul]
  calc
    _ ≤ (a ^ n * J) * (1 / (b * R ^ n)) := mul_le_mul scale rn (norm_nonneg _) (by positivity)
    _ = crit n := by dsimp [crit]; rw [div_pow]; field_simp [bp.ne', Rp.ne']
    _ < ε := nc

#print axioms outer_contour_eventual_lower
#print axioms outer_contour_tendsto_uniformly

end OrderedPartitions.CriticalEdge
