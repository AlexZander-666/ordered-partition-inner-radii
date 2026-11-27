import OrderedPartitions.CriticalEdgeThreeKernel
import Mathlib.Analysis.Real.Pi.Bounds

/-! Isolation of the double zero for the original threshold-three denominator. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Finset Set

/-- Sharpness only needs the ordering a>1; positivity of the last exponential
term gives a strict separation at the far real endpoint of the disk. -/
private theorem kernel_lower {a : ℝ} (lo : 1<a) :
    1 < (2*(1+a))*(quadKernel ((-2*a:ℝ):ℂ)).re := by
  have e := congrArg Complex.re (quadKernel_exact ((-2*a:ℝ):ℂ))
  have r (x : ℝ) (z : ℂ) : (((x:ℂ)^2)*z).re = x^2*z.re := by
    rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  rw [r] at e
  simp only [sub_re,←Complex.ofReal_exp,ofReal_re,one_re] at e
  have expo := Real.exp_pos (-2*a)
  have ap := zero_lt_one.trans lo
  have h : (4*a^2) < (2*(1+a))*(Real.exp (-2*a)-1+2*a) := by
    nlinarith only [mul_pos (show 0 < 1+a by linarith) expo,lo]
  apply (mul_lt_mul_iff_left₀ (show 0<4*a^2 by positivity)).mp
  nlinarith only [h,e,congrArg (fun y : ℝ ↦ (2*(1+a))*y) e]

theorem threshold_three_critical_isolation {a : ℝ} (lo : 1<a) (hi : a<2)
    (crit : criticalTest 1 a=0) (height : 1<ratio 1 a) {z : ℂ} (zn : ‖z‖≤a)
    (zero : generatingDen 3 (ratio 1 a) z=0) : z=(a:ℂ) := by
  let s := ratio 1 a
  let w : ℂ := z-a
  have ap := zero_lt_one.trans lo
  obtain ⟨dc,sc,_⟩ := critical_contact 1 ap crit
  have v0 : 2-s*(1+a+a^2/2)+(s-1)*Real.exp a = 0 := by
    norm_num [den,tail,tap,sum_range_succ] at dc
    dsimp [s]; linarith only [dc]
  have v1 : (s-1)*Real.exp a = s*(1+a) := by
    norm_num [slope,tail,tap,sum_range_succ] at sc
    dsimp [s]; linarith only [sc]
  have cv0 : (2:ℂ)-(s:ℂ)*(1+(a:ℂ)+(a:ℂ)^2/2)+((s:ℂ)-1)*Complex.exp a=0 := by
    exact_mod_cast v0
  have cv1 : ((s:ℂ)-1)*Complex.exp a=(s:ℂ)*(1+(a:ℂ)) := by exact_mod_cast v1
  have formula : generatingDen 3 s z =
      2-(s:ℂ)*(1+z+z^2/2)+((s:ℂ)-1)*Complex.exp z := by
    unfold generatingDen
    norm_num [sum_range_succ]
    ring
  have za : z=(a:ℂ)+w := by dsimp [w]; ring
  have atz := zero
  rw [formula,za,Complex.exp_add] at atz
  have rel : (s:ℂ)*(1+(a:ℂ))*(Complex.exp w-1-w)=(s:ℂ)*w^2/2 := by
    linear_combination atz - cv0 + (1-Complex.exp w)*cv1
  by_contra nz
  have wn : w ≠ 0 := sub_ne_zero.mpr nz
  have sn : (s:ℂ)≠0 := by exact_mod_cast (zero_lt_one.trans height).ne'
  rw [←quadKernel_exact w] at rel
  have eq : 2*(1+(a:ℂ))*quadKernel w = 1 := by
    apply (mul_right_cancel₀ (mul_ne_zero sn (pow_ne_zero 2 wn)))
    linear_combination 2*rel
  have eqr : (((2*(1+a):ℝ):ℂ))*quadKernel w=1 := by push_cast; exact eq
  have non : 0 < 2*(1+a) := by linarith
  have im0 : (quadKernel w).im = 0 := by
    have h := congrArg Complex.im eqr
    simp only [im_ofReal_mul,one_im] at h
    exact (mul_eq_zero.mp h).resolve_left non.ne'
  have small : |w.im|<Real.pi := by
    simpa [w] using (Complex.abs_im_le_norm z).trans_lt (zn.trans_lt (hi.trans (by linarith [Real.pi_gt_three])))
  have wi := quadKernel_real_of_real_value small im0
  have eqw : (w.re:ℂ)=w := by apply Complex.ext <;> simp [wi]
  have low : -2*a ≤ w.re := by
    have zlo := (abs_le.mp ((Complex.abs_re_le_norm z).trans zn)).1
    dsimp [w]; linarith
  have cmp := quadKernel_real_mono low
  change (quadKernel ((-2*a:ℝ):ℂ)).re ≤ (quadKernel (w.re:ℂ)).re at cmp
  rw [eqw] at cmp
  have rr := congrArg Complex.re eqr
  simp only [re_ofReal_mul,one_re] at rr
  exact (kernel_lower lo).not_ge ((mul_le_mul_of_nonneg_left cmp non.le).trans_eq rr)

#print axioms threshold_three_critical_isolation
end OrderedPartitions.CriticalEdge
