import OrderedPartitions.CriticalEdgePhaseModel
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Holomorphicity and symmetry of the actual phase error, with fixed-circle derivative bounds. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Set Metric
open scoped Topology ComplexConjugate

theorem splitRow_analytic (k n : ℕ) (a : ℝ) (v : ℂ) :
    AnalyticAt ℂ (splitRow k a n) v := by
  rw [analyticAt_iff_eventually_differentiableAt]
  apply Filter.Eventually.of_forall
  intro x
  unfold splitRow splitActivity
  simp only [Polynomial.eval₂_eq_eval_map]
  fun_prop

theorem splitRow_even (k n : ℕ) (a : ℝ) (v : ℂ) :
    splitRow k a n (-v) = splitRow k a n v := by
  simp [splitRow, splitActivity]

private theorem eval_conjugate (p : Polynomial ℝ) (v : ℂ) :
    p.eval₂ Complex.ofRealHom (conj v) = conj (p.eval₂ Complex.ofRealHom v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial n a => simp [Polynomial.eval₂_monomial]

theorem splitRow_conj (k n : ℕ) (a : ℝ) (v : ℂ) :
    splitRow k a n (conj v) = conj (splitRow k a n v) := by
  have mark : 1 - splitActivity k a (conj v) = conj (1 - splitActivity k a v) := by
    simp [splitActivity]
  simp only [splitRow, mark, eval_conjugate, map_div₀, map_natCast]

/-- The error can be computed as a difference of analytic functions, including at the center. -/
def splitDefect (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  splitScale k a Z n v * splitRow k a n v - Complex.sinh (splitPhase k a Z n v)

theorem splitDefect_odd (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (n : ℕ) (v : ℂ) :
    splitDefect k a Z n (-v) = -splitDefect k a Z n v := by
  have ph : splitPhase k a Z n (-v) = -splitPhase k a Z n v := by
    simp only [splitPhase, pairedLogDiff_odd, mul_neg]
    ring
  simp only [splitDefect, splitScale, pairedMean_even, neg_mul, neg_div, splitRow_even, ph,
    Complex.sinh_neg, neg_sub]
  ring

theorem splitDefect_conj_germ {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ))
    (realZ : ∀ᶠ v : ℂ in 𝓝 0, Z (conj v) = conj (Z v)) :
    ∀ᶠ v : ℂ in 𝓝 0, ∀ n : ℕ, splitDefect k a Z n (conj v) = conj (splitDefect k a Z n v) := by
  let B := residueUnit k a Z
  have za0 : Z 0 ∈ slitPlane := by rw [z0]; exact ofReal_mem_slitPlane.mpr ap
  have ba := residueUnit_analytic ap crit za z0 zd
  have b0 : B 0 ∈ slitPlane := by
    rw [show B 0 = (((2 * ((k : ℝ) + 1))⁻¹ : ℝ) : ℂ) from residueUnit_at_zero ap crit za z0 zd]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  have realB := residueUnit_conj_germ ap crit za z0 zd realZ
  filter_upwards [paired_conj_germ za.continuousAt za0 realZ,
    paired_conj_germ ba.continuousAt b0 realB] with v hZ hB
  intro n
  have p : splitPhase k a Z n (conj v) = conj (splitPhase k a Z n v) := by
    simp only [splitPhase, hZ.1, hB.1, map_sub, map_mul, map_natCast]
  have s : splitScale k a Z n (conj v) = conj (splitScale k a Z n v) := by
    simp only [splitScale, hZ.2, hB.2, map_div₀, map_mul, map_pow, map_ofNat]
  simp only [splitDefect, p, s, splitRow_conj, Complex.sinh_conj, map_mul, map_sub]

theorem splitDefect_analytic_germ {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    ∀ᶠ v : ℂ in 𝓝 0, ∀ n : ℕ, AnalyticAt ℂ (splitDefect k a Z n) v := by
  let B := residueUnit k a Z
  have za0 : Z 0 ∈ slitPlane := by rw [z0]; exact ofReal_mem_slitPlane.mpr ap
  have ba := residueUnit_analytic ap crit za z0 zd
  have b0 : B 0 ∈ slitPlane := by
    rw [show B 0 = (((2 * ((k : ℝ) + 1))⁻¹ : ℝ) : ℂ) from residueUnit_at_zero ap crit za z0 zd]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  obtain ⟨Wz,Gz⟩ := paired_analytic za za0
  obtain ⟨Wb,Gb⟩ := paired_analytic ba b0
  filter_upwards [Wz.eventually_analyticAt, Gz.eventually_analyticAt,
    Wb.eventually_analyticAt, Gb.eventually_analyticAt] with v hw hg hs hu
  intro n
  have ph : AnalyticAt ℂ (splitPhase k a Z n) v := (analyticAt_const.mul hw).sub hs
  have sc : AnalyticAt ℂ (splitScale k a Z n) v :=
    (analyticAt_id.mul (hg.pow _)).div (analyticAt_const.mul hu)
      (mul_ne_zero (by norm_num) (pairedMean_ne_zero _ _))
  have sn : AnalyticAt ℂ (fun z ↦ Complex.sinh (splitPhase k a Z n z)) v := by
    unfold Complex.sinh
    exact (ph.cexp'.sub ph.neg.cexp').div_const
  exact (sc.mul (splitRow_analytic k n a v)).sub sn

theorem splitScale_analytic_germ {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    ∀ᶠ v : ℂ in 𝓝 0, ∀ n : ℕ, AnalyticAt ℂ (splitScale k a Z n) v := by
  let B := residueUnit k a Z
  have za0 : Z 0 ∈ slitPlane := by rw [z0]; exact ofReal_mem_slitPlane.mpr ap
  have ba := residueUnit_analytic ap crit za z0 zd
  have b0 : B 0 ∈ slitPlane := by
    rw [show B 0 = (((2 * ((k : ℝ) + 1))⁻¹ : ℝ) : ℂ) from residueUnit_at_zero ap crit za z0 zd]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  have hz := (paired_analytic za za0).2
  have hb := (paired_analytic ba b0).2
  filter_upwards [hz.eventually_analyticAt, hb.eventually_analyticAt] with v hg hu
  intro n
  exact (analyticAt_id.mul (hg.pow _)).div (analyticAt_const.mul hu)
    (mul_ne_zero (by norm_num) (pairedMean_ne_zero _ _))

/-- Cauchy's bound in a circle of radius half the available fixed disk. -/
theorem deriv_bound_half_disk {F : ℂ → ℂ} {r B : ℝ} (rp : 0 < r)
    (hol : ∀ z ∈ closedBall (0 : ℂ) (2*r), AnalyticAt ℂ F z)
    (bound : ∀ z ∈ closedBall (0 : ℂ) (2*r), ‖F z‖ ≤ B)
    {v : ℂ} (hv : ‖v‖ ≤ r) :
    ‖deriv F v‖ ≤ B / r := by
  have insert : closedBall v r ⊆ closedBall (0 : ℂ) (2*r) := by
    intro z hz
    have tri := dist_triangle z v (0 : ℂ)
    rw [dist_zero_right, dist_zero_right] at tri
    have hm := mem_closedBall.mp hz
    rw [mem_closedBall, dist_zero_right]
    linarith
  have D : DifferentiableOn ℂ F (closedBall v r) := fun z hz ↦
    (hol z (insert hz)).differentiableAt.differentiableWithinAt
  have eq := Complex.differentiable_on_off_countable_deriv_eq_smul_circleIntegral
    (c := v) (f := F) rp countable_empty D.continuousOn
    (fun z hz ↦ (hol z (insert (ball_subset_closedBall hz.1))).differentiableAt)
  let g := fun z : ℂ ↦ (1 / (z - v) ^ 2) • F z
  have E : ‖(2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(v,r), g z‖ ≤ r*(B/r^2) :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const rp.le (fun z hz ↦ by
      have nr : ‖z-v‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
      change ‖(1 / (z-v)^2) • F z‖ ≤ _
      rw [norm_smul, norm_div, norm_one, norm_pow, nr]
      exact (mul_le_mul_of_nonneg_left (bound z (insert (sphere_subset_closedBall hz)))
        (by positivity)).trans_eq (by ring))
  change (∮ z in C(v,r), g z) = _ at eq
  rw [eq, smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul] at E
  refine E.trans_eq ?_
  field_simp [rp.ne']

#print axioms splitRow_analytic
#print axioms splitDefect_odd
#print axioms splitDefect_conj_germ
#print axioms splitDefect_analytic_germ
#print axioms splitScale_analytic_germ
#print axioms deriv_bound_half_disk

end OrderedPartitions.CriticalEdge
