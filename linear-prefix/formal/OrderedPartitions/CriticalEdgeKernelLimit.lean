import OrderedPartitions.CriticalEdgeScaledContours
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Uniform convergence of the scaled kernel on the fixed contour. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter
open scoped Topology

theorem secondQuotient_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) :
    Differentiable ℂ (secondQuotient g c) := by
  have shift {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (dslope f c) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (univ_mem : univ ∈ 𝓝 c)).mpr hf.differentiableOn)
  exact shift (shift hg)

theorem rescaledDen_continuous (k : ℕ) (a : ℝ) :
    Continuous (fun x : ℂ × (ℂ × ℂ) ↦ rescaledDen (k + 2) a (ratio k a) (edgeWidth k a)
      x.2.1 x.2.2 x.1) := by
  have d := (secondQuotient_differentiable
    (CriticalEdgeCircle.denominator_differentiable (k + 2) (ratio k a)) (a : ℂ)).continuous
  have b : Continuous (CriticalEdgeCircle.tailComplex (k + 2)) := by
    unfold CriticalEdgeCircle.tailComplex
    fun_prop
  unfold rescaledDen
  fun_prop

private def logSlope : ℂ → ℂ := dslope (fun z : ℂ ↦ Complex.log (1 + z)) 0

private theorem logOne_deriv : HasDerivAt (fun z : ℂ ↦ Complex.log (1 + z)) 1 0 := by
  let F := fun z : ℂ ↦ 1 + z
  have d : HasDerivAt F 1 0 := (hasDerivAt_id (0 : ℂ)).const_add 1
  have hlog : HasDerivAt Complex.log (F 0)⁻¹ (F 0) :=
    Complex.hasDerivAt_log (by simp [F])
  simpa only [F, Function.comp_def, add_zero, inv_one, one_mul] using hlog.comp 0 d

private theorem logSlope_zero : logSlope 0 = 1 := by
  rw [logSlope, dslope_same, logOne_deriv.deriv]

private theorem logSlope_continuousAt : ContinuousAt logSlope 0 := by
  exact continuousAt_dslope_same.mpr logOne_deriv.differentiableAt

private theorem logSlope_identity (z : ℂ) : z * logSlope z = Complex.log (1 + z) := by
  simpa only [logSlope, sub_zero, add_zero, Complex.log_one, smul_eq_mul] using
    sub_smul_dslope (fun w : ℂ ↦ Complex.log (1 + w)) 0 z

private def extendedKernel (k : ℕ) (a : ℝ) (x : ℂ × (ℂ × ℂ)) : ℂ :=
  ((a : ℂ) * ((k : ℂ) + 1)) * Complex.exp (-(1 + x.1) * x.2.2 * logSlope (x.1 * x.2.2)) /
    rescaledDen (k + 2) a (ratio k a) (edgeWidth k a) x.2.1 x.2.2 x.1

private theorem extendedKernel_at_zero {k : ℕ} {a : ℝ} (ha : 0 < a) (hz : criticalTest k a = 0)
    {u v : ℂ} (h : v ^ 2 + u ≠ 0) : extendedKernel k a (0, u, v) = Complex.exp (-v) / (v ^ 2 + u) := by
  have an : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have kn : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  unfold extendedKernel
  rw [rescaled_critical ha hz]
  simp only [add_zero, neg_one_mul, zero_mul, logSlope_zero, mul_one]
  field_simp [an, kn, h]

private theorem extendedKernel_at_inverse {k n : ℕ} {a : ℝ} (hn : n ≠ 0) {u v : ℂ}
    (hb : 1 + (n : ℂ)⁻¹ * v ≠ 0) :
    extendedKernel k a ((n : ℂ)⁻¹, u, v) = scaledKernel k a n u v := by
  have nn : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  let h := (n : ℂ)⁻¹
  have coeff : (1 + h) * v * logSlope (h * v) = (n + 1 : ℕ) * Complex.log (1 + h * v) := by
    have hC := logSlope_identity (h * v)
    rw [← hC]
    dsimp only [h]
    push_cast
    field_simp [nn]
  unfold extendedKernel scaledKernel
  change _ * Complex.exp (-(1 + h) * v * logSlope (h * v)) / _ =
    _ * (((1 + h * v) ^ (n + 1)) * _)⁻¹
  rw [neg_mul, neg_mul, coeff, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log hb]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem continuousAt_extendedKernel {k : ℕ} {a : ℝ} (ha : 0 < a) (hz : criticalTest k a = 0)
    {u v : ℂ} (hn : v ^ 2 + u ≠ 0) : ContinuousAt (extendedKernel k a) (0, u, v) := by
  have an : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have kn : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  have logc : ContinuousAt (fun x : ℂ × (ℂ × ℂ) ↦ logSlope (x.1 * x.2.2)) (0, u, v) := by
    have mulc : ContinuousAt (fun x : ℂ × (ℂ × ℂ) ↦ x.1 * x.2.2) (0, u, v) := by fun_prop
    have lc : ContinuousAt logSlope ((0 : ℂ) * v) := by rw [zero_mul]; exact logSlope_continuousAt
    exact lc.comp (x := (0, u, v)) mulc
  unfold extendedKernel
  apply ContinuousAt.div (by fun_prop) (rescaledDen_continuous k a).continuousAt
  exact (rescaled_critical ha hz u v).trans_ne (mul_ne_zero (mul_ne_zero an kn) hn)

private theorem v_sq_add_ne {u v : ℂ} {U M : ℝ} (UM : U < M ^ 2)
    (hu : u ∈ closedBall (0 : ℂ) U) (hv : v ∈ sphere (0 : ℂ) M) : v ^ 2 + u ≠ 0 := by
  intro e
  have he : v ^ 2 = -u := eq_neg_of_add_eq_zero_left e
  have eq := congrArg (fun z : ℂ ↦ ‖z‖) he
  have vv : ‖v‖ = M := by simpa only [mem_sphere, dist_zero_right] using hv
  rw [norm_pow, norm_neg, vv] at eq
  have ub : ‖u‖ ≤ U := by simpa only [mem_closedBall, dist_zero_right] using hu
  linarith only [eq, ub, UM]

/-- Joint continuity along a compact parameter slice gives uniform convergence to the slice. -/
theorem compact_parameter_uniform {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {F : ℂ × X → ℂ} (hc : ∀ y ∈ K, ContinuousAt F (0, y)) :
    TendstoUniformlyOn (fun n : ℕ ↦ fun y ↦ F ((n : ℂ)⁻¹, y)) (fun y ↦ F (0, y)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have near : ∀ᶠ h : ℂ in 𝓝 0, ∀ y ∈ K, dist (F (0, y)) (F (h, y)) < ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have cp : ContinuousAt (fun x : ℂ × X ↦ ((0 : ℂ), x.2)) (0, y) := by fun_prop
    have hc' : ContinuousAt (fun x : ℂ × X ↦ F (0, x.2)) (0, y) :=
      (hc y hy).comp (x := (0, y)) cp
    have er := hc'.tendsto.dist (hc y hy).tendsto
    exact er.eventually (by simpa only [dist_self] using gt_mem_nhds hε)
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).eventually near

/-- The rescaled kernel converges uniformly over compact sets of markers and the fixed contour.
The marker bound lies strictly below the squared contour radius. -/
theorem scaledKernel_tendsto_uniformly {k : ℕ} {a : ℝ} (ha : 0 < a) (hz : criticalTest k a = 0)
    {U M : ℝ} (UM : U < M ^ 2) :
    TendstoUniformlyOn (fun n : ℕ ↦ fun x : ℂ × ℂ ↦ scaledKernel k a n x.1 x.2)
      (fun x ↦ Complex.exp (-x.2) / (x.2 ^ 2 + x.1)) atTop
        (closedBall (0 : ℂ) U ×ˢ sphere (0 : ℂ) M) := by
  let K := closedBall (0 : ℂ) U ×ˢ sphere (0 : ℂ) M
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) U).prod (isCompact_sphere (0 : ℂ) M)
  have nz (x : ℂ × ℂ) (hx : x ∈ K) : x.2 ^ 2 + x.1 ≠ 0 := v_sq_add_ne UM hx.1 hx.2
  have h := compact_parameter_uniform hK (F := extendedKernel k a)
    (fun x hx ↦ continuousAt_extendedKernel ha hz (nz x hx))
  have eventualBase : ∀ᶠ h : ℂ in 𝓝 0, ∀ x ∈ K, 1 + h * x.2 ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have c : ContinuousAt (fun y : ℂ × (ℂ × ℂ) ↦ (1 : ℂ) + y.1 * y.2.2) (0, x) := by fun_prop
    exact c.eventually_ne (by simp)
  have close := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).eventually eventualBase
  apply (h.congr_right fun x hx ↦ extendedKernel_at_zero ha hz (nz x hx)).congr
  filter_upwards [close, eventually_ne_atTop 0] with n hn h0
  intro x hx
  exact extendedKernel_at_inverse h0 (hn x hx)

/-- The limiting and finite integrands are regular on the fixed circle, uniformly over the
compact set of marks once the rank is large enough. -/
theorem scaledKernel_eventually_continuousOn {k : ℕ} {a : ℝ} (ha : 0 < a)
    (hz : criticalTest k a = 0) {U M : ℝ} (UM : U < M ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ closedBall (0 : ℂ) U,
      ContinuousOn (scaledKernel k a n u) (sphere (0 : ℂ) M) := by
  let K := closedBall (0 : ℂ) U ×ˢ sphere (0 : ℂ) M
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) U).prod (isCompact_sphere (0 : ℂ) M)
  let D := fun x : ℂ × (ℂ × ℂ) ↦
    rescaledDen (k + 2) a (ratio k a) (edgeWidth k a) x.2.1 x.2.2 x.1
  have hD : Continuous D := rescaledDen_continuous k a
  have an : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have kn : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  have eventuallyNonzero : ∀ᶠ h : ℂ in 𝓝 0, ∀ x ∈ K,
      (1 + h * x.2 ≠ 0) ∧ D (h, x) ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have c : ContinuousAt (fun y : ℂ × (ℂ × ℂ) ↦ (1 : ℂ) + y.1 * y.2.2) (0, x) := by fun_prop
    have dd : D (0, x) ≠ 0 := by
      dsimp only [D]
      rw [rescaled_critical ha hz]
      exact mul_ne_zero (mul_ne_zero an kn) (v_sq_add_ne UM hx.1 hx.2)
    exact (c.eventually_ne (by simp)).and (hD.continuousAt.eventually_ne dd)
  filter_upwards [(tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).eventually eventuallyNonzero] with n hn
  intro u hu
  have d'' : Continuous (fun v : ℂ ↦ D ((n : ℂ)⁻¹, u, v)) := hD.comp (by fun_prop)
  unfold scaledKernel
  apply ContinuousOn.const_mul
  apply ContinuousOn.inv₀
  · exact (((continuous_const.add (continuous_id.const_mul _)).pow _).mul d'').continuousOn
  · intro v hv
    exact mul_ne_zero (pow_ne_zero _ (hn (u, v) ⟨hu, hv⟩).1) (hn (u, v) ⟨hu, hv⟩).2

/-- Uniform convergence after integrating on the fixed scaled circle. -/
theorem scaledCircle_tendsto_uniformly {k : ℕ} {a : ℝ} (ha : 0 < a) (hz : criticalTest k a = 0)
    {U M : ℝ} (hM : 0 < M) (UM : U < M ^ 2) :
    TendstoUniformlyOn (fun n : ℕ ↦ fun u : ℂ ↦
      (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), scaledKernel k a n u v)
      (fun u ↦ (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), Complex.exp (-v) / (v ^ 2 + u))
        atTop (closedBall (0 : ℂ) U) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have close := (Metric.tendstoUniformlyOn_iff.mp (scaledKernel_tendsto_uniformly ha hz UM))
    (ε / (2 * M)) (div_pos hε (by positivity))
  filter_upwards [close, scaledKernel_eventually_continuousOn ha hz UM] with n hn cont
  intro u hu
  let f := fun v : ℂ ↦ Complex.exp (-v) / (v ^ 2 + u)
  let g := scaledKernel k a n u
  have fi : CircleIntegrable f 0 M := by
    apply ContinuousOn.circleIntegrable hM.le
    exact (by fun_prop : ContinuousOn (fun v : ℂ ↦ Complex.exp (-v)) (sphere 0 M)).div
      (by fun_prop) (fun _ hv ↦ v_sq_add_ne UM hu hv)
  have gi : CircleIntegrable g 0 M := (cont u hu).circleIntegrable hM.le
  change dist ((2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), f v)
    ((2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), g v) < ε
  rw [dist_eq_norm, ← smul_sub, ← circleIntegral.integral_sub fi gi]
  have bound := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hM.le
    (f := fun v ↦ f v - g v) (C := ε / (2 * M)) (fun v hv ↦ by
      have hh := hn (u, v) ⟨hu, hv⟩
      change dist (f v) (g v) < ε / (2 * M) at hh
      rw [dist_eq_norm] at hh
      exact hh.le)
  refine bound.trans_lt ?_
  have eq : M * (ε / (2 * M)) = ε / 2 := by field_simp [hM.ne']
  rw [eq]
  exact half_lt_self hε

#print axioms secondQuotient_differentiable
#print axioms rescaledDen_continuous
#print axioms compact_parameter_uniform
#print axioms scaledKernel_tendsto_uniformly
#print axioms scaledKernel_eventually_continuousOn
#print axioms scaledCircle_tendsto_uniformly

end OrderedPartitions.CriticalEdge
