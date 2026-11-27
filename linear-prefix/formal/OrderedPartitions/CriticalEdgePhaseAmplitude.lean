import OrderedPartitions.CriticalEdgePhaseResidues
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Real symmetry and the analytic residue amplitude for the split denominator. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

private theorem conj_zero_tendsto : Tendsto (conj : ℂ → ℂ) (𝓝 0) (𝓝 0) := by
  simpa only [map_zero] using (Complex.continuous_conj.continuousAt (x := (0 : ℂ))).tendsto

private theorem neg_zero_tendsto : Tendsto (fun v : ℂ ↦ -v) (𝓝 0) (𝓝 0) := by
  simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto

/-- The two branches are conjugation-equivariant. The derivative at their common
point determines which branch is taken by conjugation. -/
theorem splitPole_conj_germ {k : ℕ} {a R : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (za : AnalyticAt ℂ Z 0) (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ))
    (geo : ∀ᶠ v : ℂ in 𝓝 0, ‖Z v‖ < R ∧
      ∀ z : ℂ, ‖z‖ ≤ R → (splitDen k a v z = 0 ↔ z = Z v ∨ z = Z (-v))) :
    ∀ᶠ v : ℂ in 𝓝 0, Z (conj v) = conj (Z v) := by
  let F := (conj ∘ Z ∘ conj) - (fun v : ℂ ↦ Z (-v))
  have hZ : HasDerivAt Z (a : ℂ) 0 := by
    rw [← zd]
    exact za.differentiableAt.hasDerivAt
  have dRef : HasDerivAt (conj ∘ Z ∘ conj) (a : ℂ) 0 := by
    simpa only [map_zero, Complex.conj_ofReal] using hZ.conj_conj
  have dNeg : HasDerivAt (fun v : ℂ ↦ Z (-v)) (-(a : ℂ)) 0 := by
    have H := hZ.comp_of_eq (h := fun v : ℂ ↦ -v) 0 (hasDerivAt_neg (0 : ℂ)) (neg_zero.symm)
    simpa only [Function.comp_def, mul_neg, mul_one] using H
  have dF : HasDerivAt F (2 * (a : ℂ)) 0 := by
    apply (dRef.sub dNeg).congr_deriv
    ring
  have f0 : F 0 = 0 := by simp [F, z0]
  have a0 : (2 : ℂ) * (a : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast ap.ne')
  have dq : dslope F 0 0 ≠ 0 := by rwa [dslope_same, dF.deriv]
  have diff := (continuousAt_dslope_same.mpr dF.differentiableAt).eventually_ne dq
  filter_upwards [geo, conj_zero_tendsto.eventually geo, diff] with v hv hc hd
  by_cases v0 : v = 0
  · simp [v0, z0]
  have root : splitDen k a (conj v) (Z (conj v)) = 0 := (hc.2 _ hc.1.le).mpr (Or.inl rfl)
  have hcR : ‖conj (Z (conj v))‖ ≤ R := by simpa only [Complex.norm_conj] using hc.1.le
  have back : splitDen k a v (conj (Z (conj v))) = 0 := by
    simpa only [splitDen_conj, map_zero, starRingEnd_self_apply] using
      (splitDen_conj k a (conj v) (Z (conj v))).trans (congrArg conj root)
  rcases (hv.2 _ hcR).mp back with h | h
  · simpa only [starRingEnd_self_apply] using congrArg conj h
  · have eq : F v = 0 := by simp [F, h]
    have pm := sub_smul_dslope F 0 v
    rw [sub_zero, smul_eq_mul, eq, f0, sub_zero] at pm
    exact (mul_ne_zero v0 hd pm).elim

/-- The scalar derivative in the pole variable keeps the denominator's conjugation law. -/
theorem splitDen_deriv_conj (k : ℕ) (a : ℝ) (v z : ℂ) :
    deriv (splitDen k a (conj v)) (conj z) = conj (deriv (splitDen k a v) z) := by
  have d := ((splitDen_diff k a v z).hasDerivAt.conj_conj)
  have eq : conj ∘ splitDen k a v ∘ conj = splitDen k a (conj v) := by
    funext w
    simpa only [Function.comp_apply, starRingEnd_self_apply] using (splitDen_conj k a v (conj w)).symm
  rw [eq] at d
  exact d.deriv

/-- The derivative at the selected split pole, viewed as a function of the splitting parameter. -/
def residueSlope (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (v : ℂ) : ℂ :=
  deriv (splitDen k a v) (Z v)

/-- The continued amplitude of the split residue, equal to v divided by the pole derivative. -/
def residueUnit (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (v : ℂ) : ℂ :=
  (dslope (residueSlope k a Z) 0 v)⁻¹

theorem residueSlope_formula (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (v : ℂ) :
    residueSlope k a Z v = -Complex.exp (Z v) +
      splitActivity k a v * CriticalEdgeCircle.tailComplex (k+1) (Z v) :=
  (cden_deriv k (splitActivity k a v) (Z v)).deriv

private theorem residueSlope_at_zero {k : ℕ} {a : ℝ} {Z : ℂ → ℂ}
    (ap : 0 < a) (crit : criticalTest k a = 0) (z0 : Z 0 = (a : ℂ)) :
    residueSlope k a Z 0 = 0 := by
  simp only [residueSlope, splitDen, splitActivity, z0, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero]
  exact (cden_contact k ap crit).2.1

private theorem residueSlope_analytic {k : ℕ} {a : ℝ} {Z : ℂ → ℂ}
    (za : AnalyticAt ℂ Z 0) : AnalyticAt ℂ (residueSlope k a Z) 0 := by
  rw [funext (residueSlope_formula k a Z)]
  have pol : AnalyticAt ℂ (splitActivity k a) 0 := by unfold splitActivity; fun_prop
  have t : AnalyticAt ℂ (CriticalEdgeCircle.tailComplex (k+1)) (Z 0) := by
    unfold CriticalEdgeCircle.tailComplex
    fun_prop
  exact (za.cexp.neg).add (pol.mul (t.comp za))

private theorem residueSlope_derivative {k : ℕ} {a : ℝ} {Z : ℂ → ℂ}
    (ap : 0 < a) (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    HasDerivAt (residueSlope k a Z) (2 * ((k : ℂ) + 1)) 0 := by
  have hZ : HasDerivAt Z (a : ℂ) 0 := by
    rw [← zd]
    exact za.differentiableAt.hasDerivAt
  have t := (complex_tail_deriv k (Z 0)).comp 0 hZ
  have par : HasDerivAt (splitActivity k a) 0 0 := by
    unfold splitActivity
    simpa using
      ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (edgeWidth k a : ℂ)).const_sub (ratio k a : ℂ)
  rw [funext (residueSlope_formula k a Z)]
  apply (hZ.cexp.neg.add (par.mul t)).congr_deriv
  simp only [z0, splitActivity, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_add, sub_zero]
  have second :
      -Complex.exp (a : ℂ) + (ratio k a : ℂ) * CriticalEdgeCircle.tailComplex k a =
        ((2 * ((k : ℝ) + 1) / a : ℝ) : ℂ) := by
    have cast : CriticalEdgeCircle.tailComplex k (a : ℂ) = (tail k a : ℂ) := by
      unfold CriticalEdgeCircle.tailComplex tail tap
      push_cast
      rfl
    rw [cast, ← Complex.ofReal_exp, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal (critical_curvature ap crit)
  have a0 : (a : ℂ) ≠ 0 := by exact_mod_cast ap.ne'
  have e := congrArg (fun w : ℂ ↦ w * (a : ℂ)) second
  push_cast at e
  rw [div_mul_cancel₀ _ a0] at e
  linear_combination e

theorem residueUnit_at_zero {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    residueUnit k a Z 0 = (((2 * ((k : ℝ) + 1))⁻¹ : ℝ) : ℂ) := by
  rw [residueUnit, dslope_same, (residueSlope_derivative ap crit za z0 zd).deriv]
  push_cast
  rfl

theorem residueUnit_analytic {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    AnalyticAt ℂ (residueUnit k a Z) 0 := by
  unfold residueUnit
  apply (residueSlope_analytic za).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt.inv
  rw [dslope_same, (residueSlope_derivative ap crit za z0 zd).deriv]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast (by positivity : ((k : ℝ) + 1) ≠ 0))

theorem residueUnit_formula {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (z0 : Z 0 = (a : ℂ)) {v : ℂ} (vn : v ≠ 0) :
    residueUnit k a Z v = v / deriv (splitDen k a v) (Z v) := by
  rw [residueUnit, dslope_of_ne _ vn, slope_def_field, residueSlope_at_zero ap crit z0]
  simp only [sub_zero, inv_div, residueSlope]

theorem residueUnit_conj_germ {k : ℕ} {a : ℝ} {Z : ℂ → ℂ} (ap : 0 < a)
    (crit : criticalTest k a = 0) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ))
    (realZ : ∀ᶠ v : ℂ in 𝓝 0, Z (conj v) = conj (Z v)) :
    ∀ᶠ v : ℂ in 𝓝 0, residueUnit k a Z (conj v) = conj (residueUnit k a Z v) := by
  filter_upwards [realZ] with v hv
  by_cases vn : v = 0
  · simp only [vn, map_zero, residueUnit_at_zero ap crit za z0 zd, Complex.conj_ofReal]
  rw [residueUnit_formula ap crit z0 ((map_ne_zero conj).mpr vn), residueUnit_formula ap crit z0 vn,
    hv, splitDen_deriv_conj, map_div₀]

#print axioms splitPole_conj_germ
#print axioms splitDen_deriv_conj
#print axioms residueUnit_at_zero
#print axioms residueUnit_analytic
#print axioms residueUnit_formula
#print axioms residueUnit_conj_germ

end OrderedPartitions.CriticalEdge
