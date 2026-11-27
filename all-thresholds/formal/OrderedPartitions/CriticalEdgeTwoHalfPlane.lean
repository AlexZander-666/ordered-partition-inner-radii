import OrderedPartitions.CriticalEdgeOriginal
import OrderedPartitions.CriticalEdgeScalar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! At threshold two, the critical and the inner positive pole are isolated in
a whole half-plane by a scalar exponential inequality. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Complex Finset Set

theorem linear_exp_left {w : ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (AB : A ≤ B)
    (hw : w.re ≤ 0) (eq : (A:ℂ)*(Complex.exp w-1) = (B:ℂ)*w) : w = 0 := by
  have im := congrArg Complex.im eq
  simp only [im_ofReal_mul, sub_im, one_im, sub_zero, exp_im] at im
  have exp1 : Real.exp w.re ≤ 1 := Real.exp_le_one_iff.mpr hw
  have im0 : w.im = 0 := by
    by_contra ne
    have h := congrArg abs im
    simp only [abs_mul, abs_of_nonneg hA, abs_of_pos hB, abs_of_pos (Real.exp_pos _)] at h
    have ub : A * Real.exp w.re ≤ B := (mul_le_of_le_one_right hA exp1).trans AB
    have hs := Real.abs_sin_lt_abs ne
    have h1 := mul_le_mul_of_nonneg_right ub (abs_nonneg (Real.sin w.im))
    have h2 := mul_lt_mul_of_pos_left hs hB
    nlinarith only [h, h1, h2]
  have re := congrArg Complex.re eq
  simp only [re_ofReal_mul, sub_re, one_re, exp_re, im0, Real.cos_zero, mul_one] at re
  have re0 : w.re = 0 := by
    by_contra hn
    have lt := Real.add_one_lt_exp hn
    by_cases a0 : A = 0
    · rw [a0,zero_mul] at re
      exact hn ((mul_eq_zero.mp re.symm).resolve_left hB.ne')
    · have h1 := mul_lt_mul_of_pos_left lt (lt_of_le_of_ne hA (Ne.symm a0))
      have h2 := mul_le_mul_of_nonpos_right AB hw
      nlinarith only [h1,h2,re]
  exact Complex.ext (by simpa using re0) (by simpa using im0)

theorem threshold_two_left_pole {p s : ℝ} (sp : 1 ≤ s)
    (dominant : (s-1)*Real.exp p ≤ s) (pole : generatingDen 2 s p=0)
    {z : ℂ} (left : z.re ≤ p) (zero : generatingDen 2 s z=0) : z=(p:ℂ) := by
  have formula (v : ℂ) : generatingDen 2 s v =
      2-(s:ℂ)*(1+v)+((s:ℂ)-1)*Complex.exp v := by
    unfold generatingDen
    simp [sum_range_succ]
    ring
  rw [formula] at pole zero
  have e : Complex.exp z = (Real.exp p : ℂ)*Complex.exp (z-p) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; ring_nf
  have eq : (((s-1)*Real.exp p:ℝ):ℂ)*(Complex.exp (z-p)-1) = (s:ℂ)*(z-p) := by
    push_cast
    rw [e] at zero
    rw [Complex.ofReal_exp] at zero
    linear_combination zero-pole
  have w0 := linear_exp_left (mul_nonneg (sub_nonneg.mpr sp) (Real.exp_pos p).le)
    (zero_lt_one.trans_le sp) dominant (w:=z-p) (by simpa using sub_nonpos.mpr left) eq
  exact sub_eq_zero.mp w0

/-- The positive double zero at threshold two is the only zero to the left
of its vertical tangent line, including its boundary. -/
theorem threshold_two_critical_half_plane {a : ℝ} (ap : 0<a) (crit : criticalTest 0 a=0)
    (height : 1 ≤ ratio 0 a) {z : ℂ} (left : z.re ≤ a) :
    generatingDen 2 (ratio 0 a) z = 0 ↔ z=(a:ℂ) := by
  obtain ⟨dc,sc,_⟩ := critical_contact 0 ap crit
  let s := ratio 0 a
  have dom : (s-1)*Real.exp a = s := by
    simp [slope,tail,tap] at sc
    dsimp [s]
    linarith only [sc]
  have eq : generatingDen 2 s a = 0 := by
    simp [den,tail,tap,Finset.sum_range_succ] at dc
    unfold generatingDen
    simp [Finset.sum_range_succ]
    dsimp [s]
    exact_mod_cast dc
  exact ⟨threshold_two_left_pole height dom.le eq left, fun h ↦ h ▸ eq⟩

/-- Existence of the actual threshold-two critical marker and unconditional
exclusion of all competing poles throughout its left half-plane. -/
theorem original_two_critical_pole :
    ∃ a ∈ Ioo (Real.log 2) 2, criticalTest 0 a=0 ∧ 1<ratio 0 a ∧
      ∀ z : ℂ, z.re≤a → (generatingDen 2 (ratio 0 a) z=0 ↔ z=(a:ℂ)) := by
  have neg : criticalTest 0 2 < 0 := by
    unfold criticalTest tail tap
    norm_num [sum_range_succ]
    nlinarith only [Real.exp_pos (-2)]
  have le : Real.log 2 ≤ 2 := by linarith [Real.log_two_lt_d9]
  have mid := intermediate_value_Icc' le
    (f:=criticalTest 0) (fun x _ ↦ (criticalTest_deriv 0 x).continuousAt.continuousWithinAt)
    (show 0 ∈ Icc (criticalTest 0 2) (criticalTest 0 (Real.log 2)) from
      ⟨neg.le,(criticalTest_at_log 0).le⟩)
  obtain ⟨a,ha,crit⟩ := mid
  have lo : Real.log 2 < a := lt_of_le_of_ne ha.1 (by rintro rfl; linarith [criticalTest_at_log 0])
  have hi : a<2 := lt_of_le_of_ne ha.2 (by rintro rfl; linarith)
  have ap := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans lo
  have tall : 1 < ratio 0 a := by
    rw [critical_ratio ap crit]
    simpa [lt_div_iff₀ ap] using hi
  exact ⟨a,⟨lo,hi⟩,crit,tall,fun _ left ↦ threshold_two_critical_half_plane ap crit tall.le left⟩

#print axioms original_two_critical_pole
#print axioms linear_exp_left
#print axioms threshold_two_left_pole
#print axioms threshold_two_critical_half_plane
end OrderedPartitions.CriticalEdge
