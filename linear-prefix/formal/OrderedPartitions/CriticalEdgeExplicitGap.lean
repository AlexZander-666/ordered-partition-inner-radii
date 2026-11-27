import OrderedPartitions.CriticalEdgeScaling
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative separation of a complex pole from the boundary of the critical disk. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Metric Set

/-- A uniform bound for the derivative of the original denominator on a closed disk. -/
theorem norm_den_deriv_le (k : ℕ) {a S : ℝ} {z s : ℂ} (h : ‖z‖≤a) (sS : ‖s‖≤S) :
    ‖deriv (generatingDen (k+2) s) z‖ ≤ (1+S)*Real.exp a := by
  have eq : deriv (generatingDen (k+2) s) z =
      -Complex.exp z+s*CriticalEdgeCircle.tailComplex (k+1) z := (cden_deriv k s z).deriv
  have exp_bound : ‖Complex.exp z‖ ≤ Real.exp a := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans h)
  have tail_bound : ‖CriticalEdgeCircle.tailComplex (k+1) z‖ ≤ Real.exp a := by
    refine (CriticalEdgeCircle.norm_tailComplex_le (k+1) z).trans ?_
    exact (sub_le_self _ (Finset.sum_nonneg (fun _ _ ↦ by positivity))).trans (Real.exp_le_exp.mpr h)
  rw [eq]
  calc
    _ ≤ ‖-Complex.exp z‖+‖s*CriticalEdgeCircle.tailComplex (k+1) z‖ := norm_add_le _ _
    _ ≤ Real.exp a+S*Real.exp a := by
      rw [norm_neg,norm_mul]
      exact add_le_add exp_bound (mul_le_mul sS tail_bound (norm_nonneg _) (le_trans (norm_nonneg _) sS))
    _ = _ := by ring

/-- Project a pole radially onto the surrounding circle and use the nonzero
boundary margin and a uniform derivative bound. -/
theorem pole_gap {k : ℕ} {a C S : ℝ} {s p : ℂ} (ha : Real.log 2<a) (a1 : a≤1)
    (height : C*tail (k+2) a=Real.exp a-2)
    (sS : ‖s‖≤S) (hp : ‖p‖≤a) (nz : p≠0) (zero : generatingDen (k+2) s p=0) :
    (C-S)*tail (k+2) a ≤ (1+S)*Real.exp a*(a-‖p‖) := by
  have a0 := lt_trans (Real.log_pos (by norm_num : (1:ℝ)<2)) ha
  let v : ℝ := a/‖p‖
  let w : ℂ := v • p
  have pn := norm_pos_iff.mpr nz
  have big : 1≤v := (one_le_div pn).mpr hp
  have wnorm : ‖w‖=a := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤v)]
    exact div_mul_cancel₀ _ pn.ne'
  have delta : ‖w-p‖=a-‖p‖ := by
    rw [show w-p=(v-1) • p by change v • p-p=(v-1) • p;rw [sub_smul,one_smul],norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr big)]
    dsimp [v]
    field_simp
  have low := CriticalEdgeCircle.norm_denominator_lower_on_circle (j:=k+2) (s:=s) ha.le a1 wnorm height
  have upper := (convex_closedBall (0:ℂ) a).norm_image_sub_le_of_norm_deriv_le
    (f:=generatingDen (k+2) s) (fun z _ ↦ (cden_deriv k s z).differentiableAt)
    (fun z hz ↦ norm_den_deriv_le k (by simpa using hz) sS)
    (show p∈closedBall (0:ℂ) a by simpa using hp)
    (show w∈closedBall (0:ℂ) a by simpa using wnorm.le)
  rw [zero,sub_zero,delta] at upper
  exact (mul_le_mul_of_nonneg_right (by linarith) (tail_pos (k+2) a0).le).trans (low.trans upper)

#print axioms norm_den_deriv_le
#print axioms pole_gap
end OrderedPartitions.CriticalEdge
