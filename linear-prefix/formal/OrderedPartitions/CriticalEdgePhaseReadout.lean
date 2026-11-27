import OrderedPartitions.CriticalEdgePhaseDisk
import OrderedPartitions.CriticalEdgeMovingCells
import Mathlib.Analysis.Complex.RealDeriv

/-! Real phase and transverse exclusion for the genuinely normalized finite rows. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge.SplitPhaseDisk

open Complex Filter Set Metric
open scoped Topology ComplexConjugate

variable {k : ℕ} {a : ℝ} (D : SplitPhaseDisk k a)

def onAxis (y : ℝ) : ℂ := (y : ℂ) * Complex.I

@[simp] theorem norm_onAxis (y : ℝ) : ‖onAxis y‖ = |y| := by
  simp [onAxis, Real.norm_eq_abs]

@[simp] theorem onAxis_zero : onAxis 0 = 0 := by simp [onAxis]

private theorem axis_mem {r : ℝ} {y : ℝ} (hy : |y| ≤ r) :
    onAxis y ∈ closedBall (0 : ℂ) r := by
  simpa only [mem_closedBall, dist_zero_right, norm_onAxis] using hy

private theorem odd_real_axis {F : ℂ → ℂ} {w : ℂ}
    (arg : conj w = -w) (odd : F (-w) = -F w) (real : F (conj w) = conj (F w)) :
    (F w).re = 0 :=
  re_zero_of_conj_eq_neg (real.symm.trans ((congrArg F arg).trans odd))

private theorem odd_bias (v : ℂ) : splitBias k a D.pole (-v) = -splitBias k a D.pole v := by
  simp only [splitBias, pairedLogDiff_odd, neg_neg]

private theorem phase_odd (n : ℕ) (v : ℂ) :
    splitPhase k a D.pole n (-v) = -splitPhase k a D.pole n v := by
  simp only [splitPhase_add, pairedLogDiff_odd, D.odd_bias]
  ring

private theorem phase_real (n : ℕ) {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) D.radius) :
    splitPhase k a D.pole n (conj v) = conj (splitPhase k a D.pole n v) := by
  simp only [splitPhase_add, D.realLeading v hv, D.realBias v hv, map_add, map_mul, map_natCast,
    map_one]

private theorem phase_derivs (n : ℕ) {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) D.radius) :
    HasDerivAt (splitPhase k a D.pole n)
      (((n : ℂ) + 1) * deriv (pairedLogDiff D.pole) v + deriv (splitBias k a D.pole) v) v := by
  rw [splitPhase_add]
  exact (((D.leading v hv).1.differentiableAt.hasDerivAt).const_mul _).add
    ((D.bias v hv).1.differentiableAt.hasDerivAt)

theorem phase_derivative_bound (n : ℕ) {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) D.radius) :
    ‖deriv (splitPhase k a D.pole n) v - (((n : ℝ) + 1 : ℝ) : ℂ)‖ ≤
      ((n : ℝ) + 1) / 4 + D.biasBound := by
  rw [(D.phase_derivs n hv).deriv]
  have e : ((n : ℂ) + 1) * deriv (pairedLogDiff D.pole) v +
      deriv (splitBias k a D.pole) v - (((n : ℝ) + 1 : ℝ) : ℂ) =
      ((n : ℂ) + 1) * (deriv (pairedLogDiff D.pole) v - 1) +
        deriv (splitBias k a D.pole) v := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_of_nonneg (by positivity)]]
  exact add_le_add (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [one_div] using (D.leading v hv).2) (by positivity)) (D.bias v hv).2

/-- The true row zeros in the fixed split disk are eventually confined to the
imaginary axis, including complex competitors in that disk. -/
theorem eventually_split_zero_imaginary :
    ∀ᶠ n : ℕ in atTop, ∀ v ∈ closedBall (0 : ℂ) D.radius,
      splitRow k a n v = 0 → v.re = 0 := by
  let K := D.errorBound
  let q := D.rate
  let r := D.radius
  let M := D.biasBound
  have qv := tendsto_pow_atTop_nhds_zero_of_lt_one D.rate_pos.le D.rate_lt
  have errDeriv : ∀ᶠ n : ℕ in atTop, 2*K*q^n < 1/4 := by
    have lin := (qv.const_mul (2*K))
    rw [mul_zero] at lin
    exact lin.eventually_lt_const (by norm_num)
  have errVal : ∀ᶠ n : ℕ in atTop, K*r*q^n < 1/4 := by
    have lin := (qv.const_mul (K*r))
    rw [mul_zero] at lin
    exact lin.eventually_lt_const (by norm_num)
  have growth : ∀ᶠ n : ℕ in atTop, (4/3 : ℝ)*(M+1) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  filter_upwards [errDeriv, errVal, growth] with n ed ev gr
  intro v hv zero
  let w := imaginaryProjection v
  have vnorm : ‖v‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hv
  have hw : w ∈ closedBall (0 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_right] using (norm_imaginaryProjection_le v).trans vnorm
  have wl : conj w = -w := conj_imaginaryProjection v
  let F := splitPhase k a D.pole n
  let E := splitDefect k a D.pole n
  have ea : (E w).re = 0 := odd_real_axis wl (splitDefect_odd k a D.pole n w) (D.error_conj n w hw)
  have fa : (F w).re = 0 := odd_real_axis wl (D.phase_odd n w) (D.phase_real n hw)
  have yp := horizontal_real_bound vnorm (fun z hz ↦ (D.error n z hz).1.differentiableAt)
    (fun z hz ↦ (D.error n z hz).2.2) ea
  have ylo := phase_horizontal_lower vnorm (N := (n : ℝ) + 1) (by positivity)
    (fun z hz ↦ (D.phase_derivs n hz).differentiableAt) (fun _ hz ↦ D.phase_derivative_bound n hz) fa
  have yn : |v.re| ≤ |(F v).re| := by
    have step : 1 ≤ ((n : ℝ)+1) - (((n : ℝ)+1)/4 + M) := by linarith
    have T := mul_le_mul_of_nonneg_right step (abs_nonneg v.re)
    rw [one_mul] at T
    exact T.trans ylo
  have zr : Complex.sinh (F v) = -E v := by
    simp [F, E, splitDefect, zero]
  apply CriticalEdgeRank.transverse_real zr
  · rw [norm_neg]
    refine ((D.error n v hv).2.1.trans ?_).trans ev.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left vnorm D.errorBound_pos.le)
      (pow_nonneg D.rate_pos.le _)
  · rw [Complex.neg_re, abs_neg, div_eq_mul_inv]
    exact yp.trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using ed.le) (abs_nonneg _))
  · exact yn

/-- Pull a complex derivative back to the imaginary axis, taking its imaginary part. -/
theorem imaginary_axis_derivative {F : ℂ → ℂ} {y : ℝ} (h : DifferentiableAt ℂ F (onAxis y)) :
    HasDerivAt (fun x : ℝ ↦ (F (onAxis x)).im) (deriv F (onAxis y)).re y := by
  have p : HasDerivAt (fun z : ℂ ↦ z * I) I (y : ℂ) := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (y : ℂ)).mul_const I
  have G := ((h.hasDerivAt.comp (y : ℂ) p).const_mul (-I)).real_of_complex
  convert G using 1
  · funext x
    simp [onAxis, Complex.mul_re]
  · simp [Complex.mul_re, Complex.mul_im]

/-- Phase, error and normalized wave on the real coordinate of the imaginary axis. -/
def realPhase (n : ℕ) (y : ℝ) := (splitPhase k a D.pole n (onAxis y)).im
def realError (n : ℕ) (y : ℝ) := (splitDefect k a D.pole n (onAxis y)).im
def realWave (n : ℕ) (y : ℝ) :=
  (splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y)).im

/-- The genuine phase has an n-independent leading shape, so row increments are exact. -/
def realLeadingPhase (y : ℝ) := (pairedLogDiff D.pole (onAxis y)).im

theorem phase_increment (n h : ℕ) (y : ℝ) :
    D.realPhase (n+h) y = D.realPhase n y + (h : ℝ) * D.realLeadingPhase y := by
  unfold realPhase realLeadingPhase
  simp only [splitPhase_add, Complex.add_im, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im]
  push_cast
  ring

theorem phase_diff (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    HasDerivAt (D.realPhase n) (deriv (splitPhase k a D.pole n) (onAxis y)).re y :=
  imaginary_axis_derivative (D.phase_derivs n (axis_mem hy)).differentiableAt

theorem error_diff (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    HasDerivAt (D.realError n) (deriv (splitDefect k a D.pole n) (onAxis y)).re y :=
  imaginary_axis_derivative ((D.error n _ (axis_mem hy)).1.differentiableAt)

theorem axis_wave_identity (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    D.realWave n y = Real.sin (D.realPhase n y) + D.realError n y := by
  have w : conj (onAxis y) = -onAxis y := by simp [onAxis, Complex.conj_I]
  have h := axis_mem hy
  have imPhase : (splitPhase k a D.pole n (onAxis y)).re = 0 :=
    odd_real_axis w (D.phase_odd _ _) (D.phase_real n h)
  have exact : splitPhase k a D.pole n (onAxis y) = (D.realPhase n y : ℂ)*I := by
    simpa only [imPhase, Complex.ofReal_zero, zero_add, realPhase] using
      (Complex.re_add_im (splitPhase k a D.pole n (onAxis y))).symm
  have f : splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y) =
      Complex.sinh (splitPhase k a D.pole n (onAxis y)) + splitDefect k a D.pole n (onAxis y) := by
    unfold splitDefect
    ring
  unfold realWave
  rw [f, Complex.add_im, exact, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  simp [realError, Complex.mul_im, Complex.sin_ofReal_re]

theorem axis_wave_re_zero (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    (splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y)).re = 0 := by
  have w : conj (onAxis y) = -onAxis y := by simp [onAxis, Complex.conj_I]
  have h := axis_mem hy
  have ph : (splitPhase k a D.pole n (onAxis y)).re = 0 :=
    odd_real_axis w (D.phase_odd _ _) (D.phase_real n h)
  have er : (splitDefect k a D.pole n (onAxis y)).re = 0 :=
    odd_real_axis w (splitDefect_odd k a D.pole n _) (D.error_conj n _ h)
  have e : splitPhase k a D.pole n (onAxis y) = (D.realPhase n y : ℂ) * I := by
    simpa only [ph, Complex.ofReal_zero, zero_add, realPhase] using
      (Complex.re_add_im (splitPhase k a D.pole n (onAxis y))).symm
  have f : splitScale k a D.pole n (onAxis y) * splitRow k a n (onAxis y) =
      Complex.sinh (splitPhase k a D.pole n (onAxis y)) + splitDefect k a D.pole n (onAxis y) := by
    unfold splitDefect
    ring
  rw [f, Complex.add_re, er, e, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  simp [Complex.mul_re]

@[simp] theorem realPhase_zero (n : ℕ) : D.realPhase n 0 = 0 := by
  simp [realPhase, splitPhase]

@[simp] theorem realLeadingPhase_zero : D.realLeadingPhase 0 = 0 := by
  simp [realLeadingPhase]

theorem leading_derivative_bounds {y : ℝ} (hy : |y| ≤ D.radius) :
    3/4 ≤ deriv D.realLeadingPhase y ∧ deriv D.realLeadingPhase y ≤ 5/4 := by
  have d := imaginary_axis_derivative (D.leading _ (axis_mem hy)).1.differentiableAt
  have lo := D.leading _ (axis_mem hy) |>.2
  have r := Complex.abs_re_le_norm (deriv (pairedLogDiff D.pole) (onAxis y) - 1)
  rw [show deriv D.realLeadingPhase y = (deriv (pairedLogDiff D.pole) (onAxis y)).re from d.deriv]
  rw [Complex.sub_re, Complex.one_re] at r
  have both := abs_le.mp (r.trans lo)
  constructor <;> linarith only [both.1, both.2]

theorem phase_axis_derivative_bounds (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    (3/4) * ((n : ℝ)+1) - D.biasBound ≤ deriv (D.realPhase n) y ∧
      deriv (D.realPhase n) y ≤ (5/4) * ((n : ℝ)+1) + D.biasBound := by
  rw [(D.phase_diff n hy).deriv]
  have lower := D.phase_derivative_bound n (axis_mem hy)
  have re := Complex.abs_re_le_norm
    (deriv (splitPhase k a D.pole n) (onAxis y) - (((n : ℝ)+1 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at re
  have both := abs_le.mp (re.trans lower)
  constructor <;> linarith only [both.1, both.2]

theorem error_axis_bounds (n : ℕ) {y : ℝ} (hy : |y| ≤ D.radius) :
    |D.realError n y| ≤ D.errorBound * |y| * D.rate^n ∧
      |deriv (D.realError n) y| ≤ (2*D.errorBound)*D.rate^n := by
  have e := D.error n _ (axis_mem hy)
  constructor
  · have er := (Complex.abs_im_le_norm (splitDefect k a D.pole n (onAxis y))).trans e.2.1
    simpa only [realError, norm_onAxis] using er
  · rw [(D.error_diff n hy).deriv]
    exact (Complex.abs_re_le_norm _).trans e.2.2

#print axioms SplitPhaseDisk.eventually_split_zero_imaginary
#print axioms SplitPhaseDisk.phase_increment
#print axioms SplitPhaseDisk.axis_wave_identity
#print axioms SplitPhaseDisk.axis_wave_re_zero
#print axioms SplitPhaseDisk.leading_derivative_bounds
#print axioms SplitPhaseDisk.phase_axis_derivative_bounds
#print axioms SplitPhaseDisk.error_axis_bounds

end OrderedPartitions.CriticalEdge.SplitPhaseDisk
