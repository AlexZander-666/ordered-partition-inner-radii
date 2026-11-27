import OrderedPartitions.CriticalEdgePhaseReadout
import OrderedPartitions.CriticalEdgeGlobalRank
import OrderedPartitions.CriticalEdgeInnerRadii

/-! The real phase cells describe exactly the corresponding roots of the original row. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge.SplitPhaseDisk

open Complex Filter Set Metric
open scoped Topology

variable {k : ℕ} {a : ℝ} (D : SplitPhaseDisk k a)

/-- Original real marker at a positive imaginary splitting coordinate. -/
def axisMarker (k : ℕ) (a y : ℝ) : ℝ :=
  1 - ratio k a - edgeWidth k a * y^2

theorem axisMarker_negative (L : 0 < edgeWidth k a) (C : 1 < ratio k a) (y : ℝ) :
    axisMarker k a y < 0 := by
  unfold axisMarker
  linarith only [C, mul_nonneg L.le (sq_nonneg y)]

theorem axisMarker_strictAnti (L : 0 < edgeWidth k a) :
    StrictAntiOn (axisMarker k a) (Ici 0) := by
  intro x hx y hy xy
  have s := (sq_lt_sq₀ hx hy).mpr xy
  unfold axisMarker
  linarith only [mul_lt_mul_of_pos_left s L]

private theorem axis_marker_identity (k : ℕ) (a y : ℝ) :
    1 - splitActivity k a (onAxis y) = (axisMarker k a y : ℂ) := by
  unfold axisMarker splitActivity onAxis
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

private theorem splitRow_axis (k n : ℕ) (a y : ℝ) :
    splitRow k a n (onAxis y) = ((((row n (k+2)).eval (axisMarker k a y) /
      (n.factorial : ℝ)) : ℝ) : ℂ) := by
  rw [splitRow, axis_marker_identity]
  have e := Polynomial.eval₂_at_apply (p := row n (k+2)) ofRealHom (axisMarker k a y)
  rw [show (row n (k+2)).eval₂ ofRealHom (axisMarker k a y : ℂ) =
    (((row n (k+2)).eval (axisMarker k a y) : ℝ) : ℂ) from e]
  push_cast
  rfl

theorem realWave_product (n : ℕ) (y : ℝ) :
    D.realWave n y = (splitScale k a D.pole n (onAxis y)).im *
      ((row n (k+2)).eval (axisMarker k a y) / (n.factorial : ℝ)) := by
  rw [realWave, splitRow_axis]
  simp [Complex.mul_im]

theorem wave_zero_iff_original_zero (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) (yn : y ≠ 0) :
    D.realWave n y = 0 ↔ (row n (k+2)).eval (axisMarker k a y) = 0 := by
  constructor
  · intro z
    have p : splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y) = 0 := by
      apply Complex.ext
      · simpa only [Complex.zero_re] using D.axis_wave_re_zero n hy
      · change (splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y)).im = 0 at z
        simpa only [Complex.zero_im] using z
    have yn' : onAxis y ≠ 0 := mul_ne_zero (by exact_mod_cast yn) Complex.I_ne_zero
    have split := (mul_eq_zero.mp p).resolve_left (splitScale_ne_zero yn')
    rw [splitRow_axis, Complex.ofReal_eq_zero] at split
    simpa [div_eq_zero_iff, Nat.factorial_ne_zero] using split
  · intro z
    simp [D.realWave_product, z]

private theorem wave_axis_factor_diff (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    DifferentiableAt ℝ (fun x : ℝ ↦ (splitScale k a D.pole n (onAxis x)).im) y := by
  have ymem : onAxis y ∈ closedBall (0 : ℂ) D.radius := by
    simpa only [mem_closedBall, dist_zero_right, norm_onAxis] using hy
  exact (imaginary_axis_derivative (D.analyticScale n _ ymem).differentiableAt).differentiableAt

private theorem marker_deriv (k : ℕ) (a y : ℝ) :
    HasDerivAt (axisMarker k a) (-(edgeWidth k a*(2*y))) y := by
  unfold axisMarker
  simpa using ((hasDerivAt_pow 2 y).const_mul (edgeWidth k a)).const_sub (1 - ratio k a)

theorem original_simple_of_wave_simple (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius)
    (root : (row n (k+2)).eval (axisMarker k a y) = 0)
    (simple : deriv (D.realWave n) y ≠ 0) :
    (row n (k+2)).derivative.eval (axisMarker k a y) ≠ 0 := by
  intro bad
  have dp := (((row n (k+2)).hasDerivAt (axisMarker k a y)).comp y
    (marker_deriv k a y)).div_const (n.factorial : ℝ)
  have h := (D.wave_axis_factor_diff n hy).hasDerivAt.mul dp
  change HasDerivAt (fun x ↦ (splitScale k a D.pole n (onAxis x)).im *
    ((row n (k+2)).eval (axisMarker k a x) / (n.factorial : ℝ))) _ y at h
  have eq : D.realWave n = fun x ↦ (splitScale k a D.pole n (onAxis x)).im *
      ((row n (k+2)).eval (axisMarker k a x) / (n.factorial : ℝ)) :=
    funext (D.realWave_product n)
  have hh := h.deriv
  apply simple
  rw [eq, hh]
  simp [root, bad, Function.comp_apply]

theorem center_not_root_of_wave_simple (n : ℕ)
    (simple : deriv (D.realWave n) 0 ≠ 0) :
    (row n (k+2)).eval (1 - ratio k a) ≠ 0 := by
  intro bad
  have hy : |(0 : ℝ)| ≤ D.radius := by simpa only [abs_zero] using D.radius_pos.le
  have dp := (((row n (k+2)).hasDerivAt (axisMarker k a 0)).comp 0
    (marker_deriv k a 0)).div_const (n.factorial : ℝ)
  have h := (D.wave_axis_factor_diff n hy).hasDerivAt.mul dp
  change HasDerivAt (fun x ↦ (splitScale k a D.pole n (onAxis x)).im *
    ((row n (k+2)).eval (axisMarker k a x) / (n.factorial : ℝ))) _ 0 at h
  have eq : D.realWave n = fun x ↦ (splitScale k a D.pole n (onAxis x)).im *
      ((row n (k+2)).eval (axisMarker k a x) / (n.factorial : ℝ)) :=
    funext (D.realWave_product n)
  have hh := h.deriv
  apply simple
  rw [eq, hh]
  simp [axisMarker, splitScale, bad, Function.comp_apply]

theorem realWave_derivative (n : ℕ) {y : ℝ} (hy : |y| < D.radius) :
    deriv (D.realWave n) y =
      Real.cos (D.realPhase n y) * deriv (D.realPhase n) y + deriv (D.realError n) y := by
  have near : ∀ᶠ x : ℝ in 𝓝 y, |x| < D.radius := continuous_abs.continuousAt.eventually
    (gt_mem_nhds hy)
  have eq : D.realWave n =ᶠ[𝓝 y] fun x ↦ Real.sin (D.realPhase n x) + D.realError n x :=
    near.mono (fun _ h ↦ D.axis_wave_identity n h.le)
  rw [eq.deriv_eq]
  rw [(D.phase_diff n hy.le).deriv, (D.error_diff n hy.le).deriv]
  have P := Real.hasDerivAt_sin (D.realPhase n y)
  have dh := (P.comp y (D.phase_diff n hy.le)).add (D.error_diff n hy.le)
  change HasDerivAt (fun x ↦ Real.sin (D.realPhase n x) + D.realError n x) _ y at dh
  exact dh.deriv

include D in
theorem eventually_center_not_root :
    ∀ᶠ n : ℕ in atTop, (row n (k+2)).eval (1 - ratio k a) ≠ 0 := by
  let M := D.biasBound
  have grow : ∀ᶠ n : ℕ in atTop, (4/3 : ℝ) * (M+1) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  have rate := (tendsto_pow_atTop_nhds_zero_of_lt_one D.rate_pos.le D.rate_lt).const_mul (2*D.errorBound)
  rw [mul_zero] at rate
  filter_upwards [grow,rate.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num)] with n nlo E
  have h0 : |(0:ℝ)| < D.radius := by simpa only [abs_zero] using D.radius_pos
  have lower := (D.phase_axis_derivative_bounds n h0.le).1
  have sm := ((D.error_axis_bounds n h0.le).2.trans_lt E)
  apply D.center_not_root_of_wave_simple n
  rw [D.realWave_derivative n h0, D.realPhase_zero, Real.cos_zero, one_mul]
  have Eneg := (abs_lt.mp sm).1
  dsimp only [M] at nlo
  linarith only [lower,Eneg,nlo]

/-- A uniform lower bound on translated root distances places every root of almost
minimal modulus in the real phase coordinate. -/
theorem eventually_represent_global_roots_of_lower {d : ℝ} (dp : 0 < d) (dr : d ≤ D.radius)
    (ap : 0 < a) (tall : 1 < ratio k a)
    (lower : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ,
      (row n (k+2)).eval₂ ofRealHom z = 0 → 1 + (ratio k a - 1) - η ≤ ‖1-z‖) :
    ∃ e > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℂ,
      (row n (k+2)).eval₂ ofRealHom t = 0 → ‖t‖ ≤ ratio k a - 1 + e →
      ∃ y ∈ Ioo 0 d, t = (axisMarker k a y : ℂ) ∧ D.realWave n y = 0 := by
  let C := ratio k a
  let L := edgeWidth k a
  have Lp : 0 < L := by dsimp [L,edgeWidth]; have := tail_pos (k+2) ap; positivity
  have L0 : (L : ℂ) ≠ 0 := by exact_mod_cast Lp.ne'
  obtain ⟨e,ep,N,near⟩ := CriticalEdgeRank.localize_family (r := C-1) (by linarith)
    (fun n t ↦ (row n (k+2)).eval₂ ofRealHom t = 0) lower
    (radius := L*d^2) (by positivity)
  refine ⟨e,ep,?_⟩
  filter_upwards [eventually_ge_atTop N,D.eventually_split_zero_imaginary,D.eventually_center_not_root]
    with n nN axis ncenter
  intro t tz tm
  have small := near n nN t tz tm
  let b := 1-C
  let v := ((t - (b : ℂ))/(L : ℂ)) ^ ((2 : ℂ)⁻¹)
  have hv : v ^ 2 = (t - (b : ℂ))/(L : ℂ) := Complex.cpow_ofNat_inv_pow _ 2
  have he : t = (b : ℂ) + (L : ℂ)*v^2 := by
    rw [hv]
    field_simp [L0]
    ring
  have normV : ‖v‖ < d := by
    have s : ‖v‖^2 = ‖t + ((C-1 : ℝ) : ℂ)‖/L := by
      rw [← norm_pow, hv, norm_div, Complex.norm_of_nonneg Lp.le]
      have heq : t - (b : ℂ) = t + ((C-1 : ℝ) : ℂ) := by
        simp only [b, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rw [heq]
    apply (sq_lt_sq₀ (norm_nonneg _) dp.le).mp
    rw [s, div_lt_iff₀ Lp]
    exact small.trans_eq (mul_comm _ _)
  have vmem : v ∈ closedBall (0 : ℂ) D.radius := by
    simpa only [mem_closedBall,dist_zero_right] using normV.le.trans dr
  have veq : 1 - splitActivity k a v = t := by
    rw [he, splitActivity]
    dsimp [b,C,L]
    push_cast
    ring
  have vz : splitRow k a n v = 0 := by rw [splitRow, veq, tz, zero_div]
  have vRe := axis v vmem vz
  let y := |v.im|
  have tRep : t = (axisMarker k a y : ℂ) := by
    have cv : v = (v.im : ℂ)*I := by
      simpa only [vRe, Complex.ofReal_zero, zero_add] using (Complex.re_add_im v).symm
    rw [he,cv,mul_pow,Complex.I_sq]
    dsimp [axisMarker,b,C,L]
    push_cast
    have yy : (y : ℂ)^2 = (v.im : ℂ)^2 := by exact_mod_cast (sq_abs v.im)
    rw [yy]
    ring
  have yd : y < d := (Complex.abs_im_le_norm v).trans_lt normV
  have yp : 0 < y := by
    by_contra! no
    have y0 : y=0 := le_antisymm no (abs_nonneg _)
    rw [y0] at tRep
    have h := (Polynomial.eval₂_at_apply (p := row n (k+2)) ofRealHom (axisMarker k a 0))
    have z : (((row n (k+2)).eval (axisMarker k a 0) : ℝ) : ℂ) = 0 := h.symm.trans (by change (row n (k+2)).eval₂ ofRealHom (axisMarker k a _ : ℂ) = 0; rwa [← tRep])
    have e := Complex.ofReal_eq_zero.mp z
    exact ncenter (by simpa [axisMarker] using e)
  have eval : (row n (k+2)).eval (axisMarker k a y) = 0 := by
    have h := Polynomial.eval₂_at_apply (p := row n (k+2)) ofRealHom (axisMarker k a y)
    exact Complex.ofReal_eq_zero.mp (h.symm.trans (by change (row n (k+2)).eval₂ ofRealHom (axisMarker k a _ : ℂ) = 0; rwa [← tRep]))
  exact ⟨y,⟨yp,yd⟩,tRep,by rw [D.realWave_product,eval,zero_div,mul_zero]⟩

/-- The translated distance limit alone supplies the global localization input,
independently of the location of the positive critical point. -/
theorem eventually_represent_global_roots_of_infDist {d : ℝ} (dp : 0 < d) (dr : d ≤ D.radius)
    (ap : 0 < a) (tall : 1 < ratio k a)
    (lim : Tendsto (fun n : ℕ ↦ infDist (1 : ℂ) (originalZeroSet k n)) atTop
      (𝓝 (ratio k a))) :
    ∃ e > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℂ,
      (row n (k+2)).eval₂ ofRealHom t = 0 → ‖t‖ ≤ ratio k a - 1 + e →
      ∃ y ∈ Ioo 0 d, t = (axisMarker k a y : ℂ) ∧ D.realWave n y = 0 := by
  apply D.eventually_represent_global_roots_of_lower dp dr ap tall
  intro η ηp
  have lo : ratio k a - η < ratio k a := sub_lt_self _ ηp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (lim.eventually (lt_mem_nhds lo))
  refine ⟨N, fun n hn z hz ↦ ?_⟩
  have hm : z ∈ originalZeroSet k n := hz
  have hd := infDist_le_dist_of_mem (x := (1 : ℂ)) hm
  rw [dist_eq_norm] at hd
  linarith only [hN n hn, hd]

/-- The same localization with the explicit logarithmic estimate from the critical disk. -/
theorem eventually_represent_global_roots {d : ℝ} (dp : 0 < d) (dr : d ≤ D.radius)
    (ha : Real.log 2 < a) (a1 : a ≤ 1) (tall : 1 < ratio k a) :
    ∃ e > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℂ,
      (row n (k+2)).eval₂ ofRealHom t = 0 → ‖t‖ ≤ ratio k a - 1 + e →
      ∃ y ∈ Ioo 0 d, t = (axisMarker k a y : ℂ) ∧ D.realWave n y = 0 := by
  let C := ratio k a
  have ap := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha
  have ht : C * tail (k+2) a = Real.exp a - 2 := div_mul_cancel₀ _ (tail_pos _ ap).ne'
  have lg : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have loss : Tendsto (radialLoss k a C) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ (2*a*(1+C)*Real.exp a/tail (k+2) a) * (Real.log n/(n:ℝ))) atTop (𝓝 0)
    simpa only [mul_zero] using lg.const_mul (2*a*(1+C)*Real.exp a/tail (k+2) a)
  have lower (η : ℝ) (ηp : 0 < η) : ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ,
      (row n (k+2)).eval₂ ofRealHom z = 0 → 1 + (C-1) - η ≤ ‖1-z‖ := by
    have ev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ radialLoss k a C n < η :=
      (eventually_ge_atTop 3).and (loss.eventually_lt_const ηp)
    obtain ⟨N,hN⟩ := eventually_atTop.mp ev
    refine ⟨N,fun n hn z hz ↦ ?_⟩
    have bound := (root_distance_log_bound ha a1 tall ht (hN n hn).1 hz).1
    linarith only [bound,(hN n hn).2]
  exact D.eventually_represent_global_roots_of_lower dp dr ap tall lower

#print axioms SplitPhaseDisk.wave_zero_iff_original_zero
#print axioms SplitPhaseDisk.original_simple_of_wave_simple
#print axioms SplitPhaseDisk.eventually_center_not_root
#print axioms SplitPhaseDisk.eventually_represent_global_roots
#print axioms SplitPhaseDisk.eventually_represent_global_roots_of_infDist

end OrderedPartitions.CriticalEdge.SplitPhaseDisk
