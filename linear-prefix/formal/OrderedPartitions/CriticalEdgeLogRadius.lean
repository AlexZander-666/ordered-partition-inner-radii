import OrderedPartitions.CriticalEdgeFiniteZeroFree
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A logarithmic finite-size error bound for every complex zero of the actual rows. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Set

def radialLoss (k : ℕ) (a C : ℝ) (n : ℕ) : ℝ :=
  (2*a*(1+C)*Real.exp a / tail (k+2) a) * (Real.log n / n)

/-- Explicit bound valid already from n=3. Negative proposed radii give a
vacuous disk in small ranks, while the loss tends to zero for fixed threshold. -/
theorem root_distance_log_bound {k n : ℕ} {a C : ℝ}
    (ha : Real.log 2 < a) (a1 : a ≤ 1) (hC : 1 < C)
    (height : C*tail (k+2) a = Real.exp a-2) (hn : 3 ≤ n)
    {t : ℂ} (root : (row n (k+2)).eval₂ ofRealHom t=0) :
    C-radialLoss k a C n < ‖1-t‖ ∧ C-1-radialLoss k a C n < ‖t‖ := by
  have a0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha
  have B0 := tail_pos (k+2) a0
  have nx : (3:ℝ) ≤ n := by exact_mod_cast hn
  have n0 : 0 < (n:ℝ) := by linarith
  have logn : 1 < Real.log n := (Real.lt_log_iff_exp_lt n0).2
    (Real.exp_one_lt_three.trans_le nx)
  have loss : 0 < radialLoss k a C n := by
    unfold radialLoss
    have logpos : 0 < Real.log n := by linarith
    positivity
  let S := C-radialLoss k a C n
  have below : S<C := sub_lt_self _ loss
  have dist : S<‖1-t‖ := by
    by_contra! failed
    have S0 := (norm_nonneg _).trans failed
    let y := subcriticalFraction k a C S
    have deq : y*(a*((1+S)*Real.exp a)) = (C-S)*tail (k+2) a := by
      exact div_mul_cancel₀ _ (by positivity)
    have numerator : (C-S)*tail (k+2) a =
        (2*Real.log n/(n:ℝ))*(a*((1+C)*Real.exp a)) := by
      dsimp [S,radialLoss]
      field_simp [B0.ne',n0.ne']
      ring
    have denpos : 0 < a*((1+S)*Real.exp a) := by positivity
    have low : 2*Real.log n/(n:ℝ) ≤ y := by
      apply (mul_le_mul_iff_left₀ denpos).mp
      rw [deq,numerator]
      have lp : 0 ≤ 2*Real.log n/(n:ℝ) := by positivity
      gcongr
    have ny : 2*Real.log n ≤ (n:ℝ)*y := by
      simpa [mul_comm y] using (div_le_iff₀ n0).mp low
    have inv : (n:ℝ)⁻¹ ≤ y := by
      rw [← one_div]
      apply (div_le_iff₀ n0).2
      rw [mul_comm]
      linarith
    have lr := Real.log_le_log (inv_pos.mpr n0) inv
    rw [Real.log_inv] at lr
    exact original_no_zero_in_disk_of_log ha a1 height S0 below (by change -Real.log y < (n:ℝ)*y; linarith) failed root
  have tr : ‖1-t‖ ≤ 1+‖t‖ := by simpa using norm_sub_le (1:ℂ) t
  exact ⟨dist,by dsimp [S] at dist; linarith⟩

/-- All assumptions about the critical point are discharged for every j≥4. -/
theorem original_log_radius {k : ℕ} (hk : 2 ≤ k) :
    ∃ a ∈ Ioo (Real.log 2) 1, criticalTest k a = 0 ∧
      ∀ n ≥ 3, ∀ t : ℂ, (row n (k+2)).eval₂ ofRealHom t=0 →
        ratio k a-radialLoss k a (ratio k a) n < ‖1-t‖ ∧
        ratio k a-1-radialLoss k a (ratio k a) n < ‖t‖ := by
  obtain ⟨a,lo,hi,hc,tall,_⟩ := strict_maximum hk
  have pos := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans lo
  exact ⟨a,⟨lo,hi⟩,hc,fun _ hn _ hz ↦ root_distance_log_bound lo hi.le tall
    (div_mul_cancel₀ _ (tail_pos _ pos).ne') hn hz⟩

#print axioms root_distance_log_bound
#print axioms original_log_radius
end OrderedPartitions.CriticalEdge
