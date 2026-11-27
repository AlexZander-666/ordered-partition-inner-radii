import OrderedPartitions.CriticalEdgePositiveRows
import OrderedPartitions.CriticalEdgeTwoHalfPlane
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The all-rank real barrier at the exact critical marker for thresholds two and three. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Finset Set

theorem small_critical_exists {k : ℕ} (small : k=0 ∨ k=1) :
    ∃ a ∈ Ioo (1:ℝ) 2, criticalTest k a=0 ∧ 1<ratio k a := by
  have exp1 : 8/3 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have pos : 0<criticalTest k 1 := by
    unfold criticalTest
    apply mul_pos (Real.exp_pos _)
    rcases small with rfl|rfl <;> norm_num [tail,tap,sum_range_succ] <;> linarith
  have neg : criticalTest k 2<0 := by
    unfold criticalTest
    apply mul_neg_of_pos_of_neg (Real.exp_pos _)
    rcases small with rfl|rfl <;> norm_num [tail,tap,sum_range_succ] <;> linarith
  obtain ⟨a,ha,crit⟩ := intermediate_value_Icc' (by norm_num : (1:ℝ)≤2)
    (f:=criticalTest k) (fun x _ ↦ (criticalTest_deriv k x).continuousAt.continuousWithinAt)
    (show 0 ∈ Icc (criticalTest k 2) (criticalTest k 1) from ⟨neg.le,pos.le⟩)
  have lo : 1<a := lt_of_le_of_ne ha.1 (by rintro rfl; linarith)
  have hi : a<2 := lt_of_le_of_ne ha.2 (by rintro rfl; linarith)
  have ap := zero_lt_one.trans lo
  refine ⟨a,⟨lo,hi⟩,crit,?_⟩
  rw [critical_ratio ap crit]
  rcases small with rfl|rfl <;> norm_num [lt_div_iff₀,ap]
  all_goals nlinarith [(sq_lt_sq₀ ap.le (by norm_num : (0:ℝ)≤2)).mpr hi]

/-- In the entire real interval from the critical marker up to zero every
row is strictly positive, with a quantitative all-rank lower bound. -/
theorem original_small_critical_barrier {k : ℕ} (small : k=0 ∨ k=1) :
    ∃ a ∈ Ioo (1:ℝ) 2, criticalTest k a=0 ∧ 1<ratio k a ∧
      ∀ s ∈ Icc 1 (ratio k a), ∀ n : ℕ,
        1 ≤ positiveScale (k+2) n a s ∧ 0 < (row n (k+2)).eval (1-s) := by
  obtain ⟨a,⟨lo,hi⟩,crit,tall⟩ := small_critical_exists small
  have ap := zero_lt_one.trans lo
  refine ⟨a,⟨lo,hi⟩,crit,tall,fun s hs n ↦ ?_⟩
  have ht := tail_pos (k+2) ap
  have hC : ratio k a * tail (k+2) a = Real.exp a-2 := div_mul_cancel₀ _ ht.ne'
  have non : 2-Real.exp a+s*tail (k+2) a ≤ 0 := by
    linarith only [mul_le_mul_of_nonneg_right hs.2 ht.le,hC]
  have lower := original_scaled_rows_lower (n:=n) (by omega : 2≤k+2) lo.le hs.1 non
  refine ⟨lower,?_⟩
  have pp := zero_lt_one.trans_le lower
  unfold positiveScale at pp
  by_contra! h
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ap.le n) h) (by positivity))) pp

#print axioms original_small_critical_barrier
end OrderedPartitions.CriticalEdge
