import OrderedPartitions.CriticalEdgeActivity
import OrderedPartitions.CriticalEdgeScalar

/-! Removable quadratic singularity for the two-pole transition. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Set Filter
open scoped Topology

/-- Dividing a function with a double zero by the squared displacement
continues it to the center, including its value at the collision. -/
def secondQuotient (f : ℂ→ℂ) (a : ℂ) := dslope (dslope f a) a

theorem quadratic_identity {f : ℂ→ℂ} {a : ℂ} (h0 : f a=0) (h1 : deriv f a=0) (z : ℂ) :
    f z=(z-a)^2*secondQuotient f a z := by
  have first := sub_smul_dslope f a z
  have second := sub_smul_dslope (dslope f a) a z
  rw [h0,sub_zero,smul_eq_mul] at first
  rw [dslope_same,h1,sub_zero,smul_eq_mul] at second
  rw [←first,←second]
  unfold secondQuotient
  ring

theorem secondQuotient_analytic {f : ℂ→ℂ} {a : ℂ} (an : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (secondQuotient f a) a :=
  an.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.analyticAt

theorem secondQuotient_value {f : ℂ→ℂ} {a : ℂ} (an : AnalyticAt ℂ f a) :
    secondQuotient f a a=iteratedDeriv 2 f a / 2 := by
  have eq := an.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope.coeff_zero 1
  change FormalMultilinearSeries.coeff _ 0 = _ at eq
  simpa [secondQuotient,FormalMultilinearSeries.coeff_fslope,FormalMultilinearSeries.coeff_ofScalars,
    Nat.factorial] using eq.symm

def rescaledDen (j : ℕ) (a C L u v h : ℂ) :=
  (a*v)^2*secondQuotient (generatingDen j C) a (a+h*(a*v)) +
    L*u*CriticalEdgeCircle.tailComplex j (a+h*(a*v))

theorem rescaled_identity {j : ℕ} {a C : ℂ} (h0 : generatingDen j C a=0)
    (h1 : deriv (generatingDen j C) a=0) (L u v h : ℂ) :
    generatingDen j (C+L*u*h^2) (a+h*(a*v)) = h^2*rescaledDen j a C L u v h := by
  have id := quadratic_identity h0 h1 (a+h*(a*v))
  rw [show generatingDen j (C+L*u*h^2) (a+h*(a*v)) =
    generatingDen j C (a+h*(a*v)) + L*u*h^2*CriticalEdgeCircle.tailComplex j (a+h*(a*v)) by
      unfold generatingDen CriticalEdgeCircle.tailComplex;ring]
  rw [id]
  unfold rescaledDen
  ring

theorem rescaled_value (j : ℕ) (a C L u v : ℂ) :
    rescaledDen j a C L u v 0=(a*v)^2*(iteratedDeriv 2 (generatingDen j C) a/2)+
      L*u*CriticalEdgeCircle.tailComplex j a := by
  have an : AnalyticAt ℂ (generatingDen j C) a := by unfold generatingDen; fun_prop
  simp [rescaledDen,secondQuotient_value an]

theorem rescaled_analytic (j : ℕ) (a C L u v : ℂ) :
    AnalyticAt ℂ (fun h ↦ rescaledDen j a C L u v h) 0 := by
  have an : AnalyticAt ℂ (generatingDen j C) a := by unfold generatingDen; fun_prop
  have sub : AnalyticAt ℂ (secondQuotient (generatingDen j C) a) (a+0*(a*v)) := by
    simpa using secondQuotient_analytic an
  have left := sub.comp (f:=fun h ↦ a+h*(a*v)) (by fun_prop : AnalyticAt ℂ (fun h ↦ a+h*(a*v)) 0)
  change AnalyticAt ℂ (fun h ↦ (a*v)^2*secondQuotient (generatingDen j C) a (a+h*(a*v))+
     L*u*CriticalEdgeCircle.tailComplex j (a+h*(a*v))) 0
  apply AnalyticAt.add
  · exact analyticAt_const.mul left
  · unfold CriticalEdgeCircle.tailComplex
    fun_prop


private abbrev ct (n : ℕ) (z : ℂ) := z^n/(n.factorial:ℂ)

private theorem ct_deriv (n : ℕ) (z : ℂ) : HasDerivAt (ct (n+1)) (ct n z) z := by
  apply ((hasDerivAt_pow (n+1) z).div_const (((n+1).factorial):ℂ)).congr_deriv
  unfold ct
  rw [Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.add_sub_cancel]
  field_simp

private theorem complex_tail_succ (n : ℕ) (z : ℂ) :
    CriticalEdgeCircle.tailComplex (n+1) z=CriticalEdgeCircle.tailComplex n z-ct n z := by
  simp only [CriticalEdgeCircle.tailComplex,Finset.sum_range_succ,ct]
  ring

theorem complex_tail_deriv (n : ℕ) (z : ℂ) :
    HasDerivAt (CriticalEdgeCircle.tailComplex (n+1)) (CriticalEdgeCircle.tailComplex n z) z := by
  induction n with
  | zero =>
    rw [show CriticalEdgeCircle.tailComplex (0+1) = fun y ↦ Complex.exp y-1 by
      funext y; simp [CriticalEdgeCircle.tailComplex]]
    simpa only [CriticalEdgeCircle.tailComplex,Finset.range_zero,Finset.sum_empty,sub_zero] using
      (Complex.hasDerivAt_exp z).sub_const 1
  | succ n ih =>
    rw [show CriticalEdgeCircle.tailComplex (n+1+1) =
      fun y ↦ CriticalEdgeCircle.tailComplex (n+1) y - ct (n+1) y from funext (complex_tail_succ _)]
    simpa [complex_tail_succ n z,Pi.sub_def] using ih.sub (ct_deriv n z)

private def cslope (k : ℕ) (C z : ℂ) := -Complex.exp z+C*CriticalEdgeCircle.tailComplex (k+1) z

theorem cden_deriv (k : ℕ) (C z : ℂ) :
    HasDerivAt (generatingDen (k+2) C) (cslope k C z) z := by
  change HasDerivAt (fun y ↦ 2-Complex.exp y+C*CriticalEdgeCircle.tailComplex (k+2) y) _ z
  simpa only [cslope,Pi.add_def,Pi.sub_def,zero_sub] using
    (((hasDerivAt_const z (2:ℂ)).sub (Complex.hasDerivAt_exp z)).add ((complex_tail_deriv (k+1) z).const_mul C))

private theorem ct_real (j : ℕ) (a : ℝ) : CriticalEdgeCircle.tailComplex j (a:ℂ)=(tail j a:ℂ) := by
  unfold CriticalEdgeCircle.tailComplex tail tap
  push_cast
  rfl

theorem cden_contact (k : ℕ) {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) :
    generatingDen (k+2) (ratio k a) a=0 ∧ deriv (generatingDen (k+2) (ratio k a)) (a:ℂ)=0 ∧
    iteratedDeriv 2 (generatingDen (k+2) (ratio k a)) (a:ℂ)=((2*((k:ℝ)+1)/a:ℝ):ℂ) := by
  obtain ⟨d,s,_⟩ := critical_contact k ha hz
  have der : deriv (generatingDen (k+2) (ratio k a)) = cslope k (ratio k a) :=
    funext fun z ↦ (cden_deriv k (ratio k a) z).deriv
  have second := (Complex.hasDerivAt_exp (a:ℂ)).neg.add ((complex_tail_deriv k (a:ℂ)).const_mul (ratio k a:ℂ))
  constructor
  · change 2-Complex.exp (a:ℂ) + (ratio k a:ℂ)*CriticalEdgeCircle.tailComplex (k+2) a = 0
    rw [ct_real,←Complex.ofReal_exp]
    exact_mod_cast d
  constructor
  · rw [der]
    unfold cslope
    rw [ct_real,←Complex.ofReal_exp]
    exact_mod_cast s
  · rw [iteratedDeriv_succ',der, iteratedDeriv_one]
    change deriv (cslope k (ratio k a)) (a:ℂ) = _
    rw [show deriv (cslope k (ratio k a)) (a:ℂ) =
      -Complex.exp (a:ℂ)+(ratio k a:ℂ)*CriticalEdgeCircle.tailComplex k a by exact second.deriv]
    rw [ct_real,←Complex.ofReal_exp]
    exact_mod_cast critical_curvature ha hz

/-- The critical inner-edge scale in the source-exact activity variable. -/
def edgeWidth (k : ℕ) (a : ℝ) := a*((k:ℝ)+1)/tail (k+2) a

theorem rescaled_critical {k : ℕ} {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) (u v : ℂ) :
    rescaledDen (k+2) a (ratio k a) (edgeWidth k a) u v 0 =
      (a:ℂ)*((k:ℂ)+1)*(v^2+u) := by
  rw [rescaled_value,(cden_contact k ha hz).2.2,ct_real]
  unfold edgeWidth
  push_cast
  have a0 : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have b0 : ((tail (k+2) a):ℂ)≠0 := by exact_mod_cast (tail_pos _ ha).ne'
  field_simp

theorem quadratic_scaling_limit {k : ℕ} {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) (u v : ℂ) :
    Tendsto (fun h : ℂ ↦ generatingDen (k+2) ((ratio k a:ℂ)+(edgeWidth k a:ℂ)*u*h^2)
      ((a:ℂ)+h*((a:ℂ)*v))/h^2) (𝓝[≠] 0) (𝓝 ((a:ℂ)*((k:ℂ)+1)*(v^2+u))) := by
  obtain ⟨d,s,_⟩ := cden_contact k ha hz
  have conv := (rescaled_analytic (k+2) a (ratio k a) (edgeWidth k a) u v).continuousAt.tendsto
  rw [rescaled_critical ha hz] at conv
  refine (conv.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h≠0 := hh
  rw [rescaled_identity d s]
  field_simp

#print axioms quadratic_scaling_limit
#print axioms rescaled_identity
#print axioms rescaled_value
#print axioms rescaled_analytic
#print axioms cden_contact
end OrderedPartitions.CriticalEdge
