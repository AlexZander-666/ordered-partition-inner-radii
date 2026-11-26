import OrderedPartitions.CriticalEdgeScaling
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! An invertible holomorphic square coordinate for the actual pair of critical poles. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Filter Set
open scoped Topology

private def poleUnit (j : ℕ) (a C L z : ℂ) :=
  a^2*secondQuotient (generatingDen j C) a z / (L*CriticalEdgeCircle.tailComplex j z)

def poleCoordinate (j : ℕ) (a C L z : ℂ) :=
  ((z-a)/a)*Complex.exp (Complex.log (poleUnit j a C L z)/2)

private theorem unit_data {k : ℕ} {a : ℝ} (ha : 0<a) (crit : criticalTest k a=0) :
    let j := k+2
    let C : ℂ := ratio k a
    let L : ℂ := edgeWidth k a
    L*CriticalEdgeCircle.tailComplex j a ≠ 0 ∧ poleUnit j a C L a=1 ∧
      AnalyticAt ℂ (poleUnit j a C L) (a:ℂ) := by
  dsimp only
  have tb : CriticalEdgeCircle.tailComplex (k+2) (a:ℂ)=(tail (k+2) a:ℂ) := by
    unfold CriticalEdgeCircle.tailComplex tail tap
    push_cast
    rfl
  have pos : 0<edgeWidth k a := by unfold edgeWidth; have := tail_pos (k+2) ha; positivity
  have nz : (edgeWidth k a:ℂ)*CriticalEdgeCircle.tailComplex (k+2) a ≠ 0 := by
    rw [tb]; exact_mod_cast (mul_pos pos (tail_pos _ ha)).ne'
  have eq := rescaled_critical ha crit (-1) 1
  simp [rescaledDen] at eq
  refine ⟨nz,?_,?_⟩
  · unfold poleUnit
    apply (div_eq_one_iff_eq nz).2
    linear_combination eq
  · have an : AnalyticAt ℂ (generatingDen (k+2) (ratio k a)) (a:ℂ) := by unfold generatingDen; fun_prop
    exact (analyticAt_const.mul (secondQuotient_analytic an)).div
      (analyticAt_const.mul (by unfold CriticalEdgeCircle.tailComplex; fun_prop)) nz

theorem poleCoordinate_factor_data {k : ℕ} {a : ℝ} (ha : 0<a) (crit : criticalTest k a=0) :
    let W := poleCoordinate (k+2) (a:ℂ) (ratio k a) (edgeWidth k a)
    W a=0 ∧ AnalyticAt ℂ W (a:ℂ) ∧ deriv W (a:ℂ)=(a:ℂ)⁻¹ ∧
    ∀ᶠ z : ℂ in 𝓝 (a:ℂ), ∀ v : ℂ,
      generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2) z =
        ((W z)^2-v^2) * ((edgeWidth k a:ℂ)*CriticalEdgeCircle.tailComplex (k+2) z) := by
  dsimp only
  let j := k+2
  let C : ℂ := ratio k a
  let L : ℂ := edgeWidth k a
  let A : ℂ := a
  let U := poleUnit j A C L
  obtain ⟨Bn,U1,Ua⟩ := unit_data ha crit
  have A0 : A≠0 := by dsimp [A]; exact_mod_cast ha.ne'
  have logok : U A ∈ slitPlane := by rw [show U A=1 from U1]; exact one_mem_slitPlane
  have unitAn : AnalyticAt ℂ (fun z ↦ Complex.exp (Complex.log (U z)/2)) A :=
    ((Ua.clog logok).div_const (c := 2)).cexp'
  have uval : Complex.exp (Complex.log (U A)/2)=1 := by rw [show U A=1 from U1];simp
  have Wd := (((hasDerivAt_id A).sub_const A).div_const A).mul unitAn.differentiableAt.hasDerivAt
  refine ⟨by simp [poleCoordinate],?_,?_,?_⟩
  · exact (show AnalyticAt ℂ (fun z : ℂ ↦ (z-A)/A) A by fun_prop).mul unitAn
  · change deriv ((fun z : ℂ ↦ (z-A)/A) * fun z ↦ Complex.exp (Complex.log (U z)/2)) A=A⁻¹
    simpa [uval,id] using Wd.deriv
  · have hU : ∀ᶠ z in 𝓝 A, U z≠0 :=
      Ua.continuousAt.eventually_ne (by simpa [U] using (show poleUnit j A C L A≠0 by rw [U1];norm_num))
    have hB : ContinuousAt (fun z ↦ L*CriticalEdgeCircle.tailComplex j z) A := by
      unfold CriticalEdgeCircle.tailComplex;fun_prop
    filter_upwards [hU,hB.eventually_ne Bn] with z uz bz
    intro v
    have sq : (Complex.exp (Complex.log (U z)/2))^2=U z := by
      rw [sq,←Complex.exp_add,show Complex.log (U z)/2+Complex.log (U z)/2=Complex.log (U z) by ring,
        Complex.exp_log uz]
    have w2 : (poleCoordinate j A C L z)^2* (L*CriticalEdgeCircle.tailComplex j z)=
        generatingDen j C z := by
      rw [poleCoordinate,mul_pow,sq,quadratic_identity (cden_contact k ha crit).1 (cden_contact k ha crit).2.1]
      change ((z-A)/A)^2*(A^2*secondQuotient (generatingDen j C) A z/(L*CriticalEdgeCircle.tailComplex j z))*
        (L*CriticalEdgeCircle.tailComplex j z)=_
      field_simp [A0]
      apply (div_eq_iff bz).2
      change _=(z-A)^2*secondQuotient (generatingDen j C) A z*(L*CriticalEdgeCircle.tailComplex j z)
      ring
    have eq : generatingDen j (C-L*v^2) z =
        ((poleCoordinate j A C L z)^2-v^2)*(L*CriticalEdgeCircle.tailComplex j z) := by
      rw [sub_mul,w2]
      unfold generatingDen CriticalEdgeCircle.tailComplex;ring
    exact eq

theorem poleCoordinate_data {k : ℕ} {a : ℝ} (ha : 0<a) (crit : criticalTest k a=0) :
    let W := poleCoordinate (k+2) (a:ℂ) (ratio k a) (edgeWidth k a)
    W a=0 ∧ AnalyticAt ℂ W (a:ℂ) ∧ deriv W (a:ℂ)=(a:ℂ)⁻¹ ∧
    ∀ᶠ z : ℂ in 𝓝 (a:ℂ), ∀ v : ℂ,
      generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2) z=0 ↔
      W z=v ∨ W z= -v := by
  dsimp only
  obtain ⟨h0,an,der,factor⟩ := poleCoordinate_factor_data ha crit
  refine ⟨h0,an,der,?_⟩
  have cont : ContinuousAt (fun z : ℂ ↦ (edgeWidth k a:ℂ)*CriticalEdgeCircle.tailComplex (k+2) z) (a:ℂ) := by
    unfold CriticalEdgeCircle.tailComplex;fun_prop
  filter_upwards [factor,cont.eventually_ne (unit_data ha crit).1] with z eq nz
  intro v
  rw [eq v,mul_eq_zero,or_iff_left nz,sub_eq_zero]
  exact sq_eq_sq_iff_eq_or_eq_neg

theorem inverse_poleCoordinate {k : ℕ} {a : ℝ} (ha : 0<a) (crit : criticalTest k a=0) :
    let W := poleCoordinate (k+2) (a:ℂ) (ratio k a) (edgeWidth k a)
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0=(a:ℂ) ∧ deriv Z 0=(a:ℂ) ∧
      (∀ᶠ v in 𝓝 0, W (Z v)=v) ∧ (∀ᶠ z in 𝓝 (a:ℂ), Z (W z)=z) := by
  dsimp only
  let W := poleCoordinate (k+2) (a:ℂ) (ratio k a) (edgeWidth k a)
  obtain ⟨h0,an,der,_⟩ := poleCoordinate_data ha crit
  have dn : deriv W (a:ℂ) ≠ 0 := by rw [show deriv W (a:ℂ)=(a:ℂ)⁻¹ from der];exact inv_ne_zero (by exact_mod_cast ha.ne')
  let Z := an.hasStrictDerivAt.localInverse _ _ _ dn
  have left : ∀ᶠ z in 𝓝 (a:ℂ), Z (W z)=z := an.hasStrictDerivAt.eventually_left_inverse dn
  have right : ∀ᶠ v in 𝓝 (W a), W (Z v)=v := an.hasStrictDerivAt.eventually_right_inverse dn
  have Z0 : Z (W a)=(a:ℂ) := left.self_of_nhds
  have Zder := (an.hasStrictDerivAt.to_localInverse dn).hasDerivAt.deriv
  have Zanalytic := an.analyticAt_localInverse dn
  have zero : W a=0 := h0
  refine ⟨Z,?_,?_,?_,?_,left⟩
  · simpa only [←zero] using Zanalytic
  · simpa only [←zero] using Z0
  · rw [←zero,show deriv Z (W a)=(deriv W (a:ℂ))⁻¹ from Zder,der,inv_inv]
  · simpa only [←zero] using right

#print axioms poleCoordinate_factor_data
#print axioms poleCoordinate_data
#print axioms inverse_poleCoordinate
end OrderedPartitions.CriticalEdge
