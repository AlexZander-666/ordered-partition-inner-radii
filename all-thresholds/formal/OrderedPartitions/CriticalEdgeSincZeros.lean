import OrderedPartitions.CriticalEdgeSinc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The entire limiting kernel has precisely the nonzero squared integer multiples
of π as complex zeros, all simple. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Filter
open scoped Topology

theorem innerSinc_square {w : ℂ} (wn : w≠0) :
    innerSinc (w^2)=Complex.sin w/w := by
  have s : (w*I)^2= -(w^2) := by rw [mul_pow,I_sq];ring
  rw [innerSinc_of_square s (mul_ne_zero wn I_ne_zero), Complex.sinh_mul_I]
  field_simp [wn,I_ne_zero]

theorem innerSinc_zeros (u : ℂ) : innerSinc u=0 ↔
    ∃ m : ℤ, m≠0 ∧ u=((m:ℂ)*(Real.pi:ℂ))^2 := by
  constructor
  · intro h
    have un : u≠0 := by intro eq;simp [eq] at h
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq u (by decide : 0<2)
    have wn : w≠0 := by intro eq;apply un;rw [←hw,eq];norm_num
    rw [←hw,innerSinc_square wn] at h
    obtain ⟨m,hm⟩ := Complex.sin_eq_zero_iff.mp ((div_eq_zero_iff.mp h).resolve_right wn)
    refine ⟨m,?_,by rw [←hw,hm]⟩
    rintro rfl
    exact wn (by simpa using hm)
  · rintro ⟨m,mn,rfl⟩
    have n : (m:ℂ)*(Real.pi:ℂ)≠0 := mul_ne_zero (by exact_mod_cast mn) (by exact_mod_cast Real.pi_ne_zero)
    rw [innerSinc_square n,Complex.sin_int_mul_pi,zero_div]

theorem innerSinc_simple {u : ℂ} (root : innerSinc u=0) : deriv innerSinc u≠0 := by
  have un : u≠0 := by intro eq;simp [eq] at root
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq u (by decide : 0<2)
  have wn : w≠0 := by intro eq;apply un;rw [←hw,eq];norm_num
  have sinzero : Complex.sin w=0 := by
    rw [←hw,innerSinc_square wn] at root
    exact (div_eq_zero_iff.mp root).resolve_right wn
  have cosnonzero : Complex.cos w≠0 := by
    rcases Complex.sin_eq_zero_iff_cos_eq.mp sinzero with h|h <;> rw [h] <;> norm_num
  let f := fun z : ℂ ↦ z^2
  have ev : ∀ᶠ x : ℂ in 𝓝 w, x≠0 := isOpen_ne.mem_nhds wn
  have germ : innerSinc ∘ f =ᶠ[𝓝 w] fun z ↦ Complex.sin z/z :=
    ev.mono fun _ h ↦ innerSinc_square h
  have an : AnalyticAt ℂ f w := by dsimp [f];fun_prop
  have fd : HasDerivAt f (2*w) w := by simpa [f] using hasDerivAt_pow 2 w
  have nd : deriv f w≠0 := fd.deriv.trans_ne (mul_ne_zero (by norm_num) wn)
  have composed : AnalyticAt ℂ (innerSinc ∘ f) w :=
    ((show AnalyticAt ℂ (fun z : ℂ ↦ Complex.sin z/z) w from analyticAt_sin.div analyticAt_id wn)).congr germ.symm
  have ia := (analyticAt_comp_iff_of_deriv_ne_zero an nd).mp composed
  have hd := (ia.differentiableAt.hasDerivAt.comp w fd).deriv
  have quotient := ((Complex.hasDerivAt_sin w).div (hasDerivAt_id w) wn).deriv
  change deriv (innerSinc ∘ f) w=deriv innerSinc (f w)*(2*w) at hd
  have eq := hd.symm.trans (germ.deriv_eq.trans quotient)
  intro bad
  have fw : f w=u := hw
  rw [fw,bad,zero_mul,sinzero] at eq
  simp only [id_eq, zero_mul, sub_zero] at eq
  exact (div_ne_zero (mul_ne_zero cosnonzero wn) (pow_ne_zero _ wn)) eq.symm

theorem innerSinc_analytic_zero : AnalyticAt ℂ innerSinc 0 := by
  apply HasFPowerSeriesAt.analyticAt (p:=FormalMultilinearSeries.ofScalars ℂ
    (fun m : ℕ ↦ (-1:ℂ)^m / ((2*m+1).factorial:ℂ)))
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with u hu
  have gu : ‖u‖<1 := by simpa using hu
  have major : Summable (fun m : ℕ ↦ ‖u‖^m) := summable_geometric_of_lt_one (norm_nonneg _) gu
  have sum : Summable (fun m : ℕ ↦ (-u)^m / ((2*m+1).factorial:ℂ)) := by
    apply major.of_norm_bounded
    intro m
    rw [norm_div,norm_pow,norm_neg,Complex.norm_natCast]
    apply div_le_self (by positivity)
    exact_mod_cast Nat.factorial_pos (2*m+1)
  rw [zero_add]
  apply sum.hasSum.congr_fun
  intro m
  rw [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul]
  rw [show -u=(-1:ℂ)*u by ring,mul_pow]
  ring

#print axioms innerSinc_analytic_zero
#print axioms innerSinc_square
#print axioms innerSinc_zeros
#print axioms innerSinc_simple
end OrderedPartitions.CriticalEdge
