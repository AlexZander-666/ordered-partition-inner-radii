import OrderedPartitions.CriticalEdgePhaseAmplitude

/-! Half-logarithmic coordinates for a pair of nearby poles. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Set
open scoped Topology ComplexConjugate

/-- The half-difference of the logarithms at opposite arguments. -/
def pairedLogDiff (F : ℂ → ℂ) (v : ℂ) : ℂ :=
  (Complex.log (F v) - Complex.log (F (-v))) / 2

/-- The geometric mean with the branch determined by the positive common center. -/
def pairedMean (F : ℂ → ℂ) (v : ℂ) : ℂ :=
  Complex.exp ((Complex.log (F v) + Complex.log (F (-v))) / 2)

@[simp] theorem pairedLogDiff_zero (F : ℂ → ℂ) : pairedLogDiff F 0 = 0 := by
  simp [pairedLogDiff]

theorem pairedLogDiff_odd (F : ℂ → ℂ) (v : ℂ) :
    pairedLogDiff F (-v) = -pairedLogDiff F v := by
  simp only [pairedLogDiff, neg_neg]
  ring

theorem pairedMean_even (F : ℂ → ℂ) (v : ℂ) :
    pairedMean F (-v) = pairedMean F v := by
  simp [pairedMean, add_comm]

theorem pairedMean_ne_zero (F : ℂ → ℂ) (v : ℂ) : pairedMean F v ≠ 0 :=
  Complex.exp_ne_zero _

theorem pairedMean_center {F : ℂ → ℂ} (h0 : F 0 ≠ 0) : pairedMean F 0 = F 0 := by
  unfold pairedMean
  rw [neg_zero, show (Complex.log (F 0) + Complex.log (F 0)) / 2 = Complex.log (F 0) by ring,
    Complex.exp_log h0]

theorem paired_specialization {F : ℂ → ℂ} {v : ℂ} (hp : F v ≠ 0) (hn : F (-v) ≠ 0) :
    pairedMean F v * Complex.exp (pairedLogDiff F v) = F v ∧
      pairedMean F v * Complex.exp (-pairedLogDiff F v) = F (-v) := by
  unfold pairedMean pairedLogDiff
  constructor
  · rw [← Complex.exp_add, show (Complex.log (F v) + Complex.log (F (-v))) / 2 +
       (Complex.log (F v) - Complex.log (F (-v))) / 2 = Complex.log (F v) by ring,
       Complex.exp_log hp]
  · rw [← Complex.exp_add, show (Complex.log (F v) + Complex.log (F (-v))) / 2 +
       -((Complex.log (F v) - Complex.log (F (-v))) / 2) = Complex.log (F (-v)) by ring,
       Complex.exp_log hn]

theorem paired_analytic {F : ℂ → ℂ} (fa : AnalyticAt ℂ F 0) (hs : F 0 ∈ slitPlane) :
    AnalyticAt ℂ (pairedLogDiff F) 0 ∧ AnalyticAt ℂ (pairedMean F) 0 := by
  have hp := fa.clog hs
  have hpn : AnalyticAt ℂ (fun v ↦ Complex.log (F v)) (-(0 : ℂ)) := by simpa only [neg_zero] using hp
  have hn := hpn.comp (f := fun v : ℂ ↦ -v) (by fun_prop : AnalyticAt ℂ (fun v : ℂ ↦ -v) 0)
  have hn' : AnalyticAt ℂ (fun v ↦ Complex.log (F (-v))) 0 := by
    simpa only [neg_zero, Function.comp_def] using hn
  exact ⟨(hp.sub hn').div_const, ((hp.add hn').div_const (c := 2)).cexp⟩

theorem pairedLogDiff_derivative {F : ℂ → ℂ} (fa : AnalyticAt ℂ F 0) (hs : F 0 ∈ slitPlane) :
    HasDerivAt (pairedLogDiff F) (deriv F 0 / F 0) 0 := by
  have dp := fa.differentiableAt.hasDerivAt.clog hs
  have d0 : HasDerivAt (fun v ↦ Complex.log (F (-v))) (-(deriv F 0 / F 0)) 0 := by
    have hn := dp.comp_of_eq (h := fun v : ℂ ↦ -v) 0 (hasDerivAt_neg (0 : ℂ)) (neg_zero.symm)
    simpa only [Function.comp_def, mul_neg, mul_one] using hn
  apply ((dp.sub d0).div_const 2).congr_deriv
  ring

theorem paired_conj_germ {F : ℂ → ℂ} (fc : ContinuousAt F 0) (hs : F 0 ∈ slitPlane)
    (sym : ∀ᶠ v : ℂ in 𝓝 0, F (conj v) = conj (F v)) :
    ∀ᶠ v : ℂ in 𝓝 0, pairedLogDiff F (conj v) = conj (pairedLogDiff F v) ∧
      pairedMean F (conj v) = conj (pairedMean F v) := by
  have negNear : Tendsto (fun v : ℂ ↦ -v) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
  have branch := fc.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hs)
  have hb : ∀ᶠ v in 𝓝 0, F v ∈ slitPlane := branch
  filter_upwards [sym, negNear.eventually sym, hb, negNear.eventually hb] with v h1 h2 b1 b2
  have hn : F (-conj v) = conj (F (-v)) := by simpa only [map_neg] using h2
  have posLog := Complex.log_conj (F v) (slitPlane_arg_ne_pi b1)
  have negLog := Complex.log_conj (F (-v)) (slitPlane_arg_ne_pi b2)
  simp only [pairedLogDiff, pairedMean, h1, hn, posLog, negLog, map_div₀,
    map_add, map_sub, ← Complex.exp_conj, map_ofNat, and_self]

/-- The exact local change from the splitting parameter to the half-logarithm. -/
theorem pairedLog_inverse {Z : ℂ → ℂ} {a : ℝ} (ap : 0 < a) (za : AnalyticAt ℂ Z 0)
    (z0 : Z 0 = (a : ℂ)) (zd : deriv Z 0 = (a : ℂ)) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧ deriv V 0 = 1 ∧
      (∀ᶠ w : ℂ in 𝓝 0, pairedLogDiff Z (V w) = w) ∧
      (∀ᶠ v : ℂ in 𝓝 0, V (pairedLogDiff Z v) = v) := by
  let W := pairedLogDiff Z
  have slit : Z 0 ∈ slitPlane := z0 ▸ ofReal_mem_slitPlane.mpr ap
  have Wa : AnalyticAt ℂ W 0 := (paired_analytic za slit).1
  have Wd : deriv W 0 = 1 := by
    have A : (a : ℂ) ≠ 0 := by exact_mod_cast ap.ne'
    simpa only [zd, z0, div_self A] using (pairedLogDiff_derivative za slit).deriv
  have nz : deriv W 0 ≠ 0 := Wd.trans_ne one_ne_zero
  let V := Wa.hasStrictDerivAt.localInverse _ _ _ nz
  have left : ∀ᶠ z in 𝓝 (0 : ℂ), V (W z) = z := Wa.hasStrictDerivAt.eventually_left_inverse nz
  have right : ∀ᶠ w in 𝓝 (W 0), W (V w) = w := Wa.hasStrictDerivAt.eventually_right_inverse nz
  have Va := Wa.analyticAt_localInverse nz
  have Vd := (Wa.hasStrictDerivAt.to_localInverse nz).hasDerivAt.deriv
  have W0 : W 0 = 0 := pairedLogDiff_zero Z
  refine ⟨V, ?_, ?_, ?_, ?_, left⟩
  · simpa only [W0] using Va
  · simpa only [W0] using left.self_of_nhds
  · simpa only [W0, Wd, inv_one] using Vd
  · simpa only [W0] using right

#print axioms paired_specialization
#print axioms paired_analytic
#print axioms pairedLogDiff_derivative
#print axioms paired_conj_germ
#print axioms pairedLog_inverse

end OrderedPartitions.CriticalEdge
