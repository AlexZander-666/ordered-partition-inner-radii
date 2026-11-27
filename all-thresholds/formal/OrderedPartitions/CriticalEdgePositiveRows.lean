import OrderedPartitions.MarkedSeries
import OrderedPartitions.CriticalEdgeScalar
import Mathlib.Algebra.BigOperators.Intervals

/-! A finite-rank real zero-free interval from the first-block recurrence. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Finset Polynomial

def positiveScale (j n : ℕ) (p s : ℝ) := p^n * (row n j).eval (1-s) / (n.factorial:ℝ)

private def signedWeight (j r : ℕ) (p s : ℝ) := tap r p * (if j≤r then 1-s else 1)

private theorem scale_step {j : ℕ} (hj : 2≤j) (n : ℕ) (p s : ℝ) :
    positiveScale j (n+1) p s =
      ∑ r ∈ Icc 1 (n+1), signedWeight j r p s * positiveScale j (n+1-r) p s := by
  unfold positiveScale
  rw [row_recurrence _ (by omega : 1≤j),eval_finsetSum,mul_sum,sum_div]
  apply sum_congr rfl
  intro r hr
  have rn := (mem_Icc.mp hr).2
  simp only [nsmul_eq_mul,eval_mul,eval_natCast,eval_pow,eval_X]
  rw [Nat.cast_choose ℝ rn,show p^(n+1)=p^r*p^(n+1-r) by rw [← pow_add]; congr 1; omega]
  unfold signedWeight tap
  split_ifs <;> simp only [pow_one,pow_zero] <;> field_simp

private theorem two_sum {j N : ℕ} {p s : ℝ} (hj : 2≤j) (jN : j≤N)
    (p1 : 1≤p) (s1 : 1≤s) (nonpos : 2-Real.exp p+s*tail j p ≤ 0) :
    0 ≤ (p-1) + ∑ r ∈ Ico 2 (N+1), signedWeight j r p s := by
  have sums (b : ℕ) (hb : 2≤b) : ∑ r ∈ Ico 2 b, tap r p = (∑ r ∈ range b, tap r p)-(1+p) := by
    rw [sum_Ico_eq_sub _ hb]
    norm_num [sum_range_succ,tap]
  have aa : ∑ r ∈ Ico 2 j, signedWeight j r p s = ∑ r ∈ Ico 2 j, tap r p := by
    apply sum_congr rfl
    intro r hr
    simp [signedWeight,not_le.mpr (mem_Ico.mp hr).2]
  have bb : ∑ r ∈ Ico j (N+1), signedWeight j r p s =
      (∑ r ∈ Ico j (N+1), tap r p)*(1-s) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro r hr
    simp [signedWeight,(mem_Ico.mp hr).1]
  rw [← sum_Ico_consecutive _ hj (by omega : j≤N+1),aa,bb,sums j hj,sum_Ico_eq_sub _ (by omega : j≤N+1)]
  have bound : ∑ r ∈ range (N+1), tap r p ≤ Real.exp p :=
    Real.sum_le_exp_of_nonneg (zero_le_one.trans p1) _
  unfold tail at nonpos
  nlinarith only [nonpos,mul_nonneg (sub_nonneg.mpr bound) (sub_nonneg.mpr s1)]

private theorem step_difference {j : ℕ} (hj : 2≤j) (n : ℕ) (p s : ℝ) :
    positiveScale j (n+1) p s - positiveScale j n p s =
      (p-1)*positiveScale j n p s +
      ∑ r ∈ Ico 2 (n+2), signedWeight j r p s * positiveScale j (n+1-r) p s := by
  rw [scale_step hj]
  have eq : Icc 1 (n+1) = insert 1 (Ico 2 (n+2)) := by ext; simp; omega
  rw [eq,sum_insert (by simp)]
  simp [signedWeight,show ¬ j≤1 by omega,tap]
  ring

/-- The scaled original row is nondecreasing at every rank if the real denominator
at a point p ≥ 1 is nonpositive. -/
theorem original_scaled_rows_monotone {j : ℕ} {p s : ℝ} (hj : 2≤j)
    (p1 : 1≤p) (s1 : 1≤s) (den0 : 2-Real.exp p+s*tail j p ≤ 0) :
    Monotone (fun n ↦ positiveScale j n p s) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let E := fun i ↦ positiveScale j i p s
    have mono {l m : ℕ} (lm : l≤m) (mn : m≤n) : E l ≤ E m := by
      induction m, lm using Nat.le_induction with
      | base => exact le_rfl
      | succ m lm inc => exact (inc (by omega)).trans (ih m (by omega))
    have pos (i : ℕ) (hi : i≤n) : 0 ≤ E i := by
      have e0 : E 0 = 1 := by simp [E,positiveScale,row_zero (by omega : 1≤j)]
      linarith only [mono (l:=0) (Nat.zero_le i) hi,e0]
    apply sub_nonneg.mp
    rw [step_difference hj]
    by_cases big : j≤n+1
    · let b := n+1-j
      have bn : b≤n := by dsimp [b]; omega
      have pcmp := mul_le_mul_of_nonneg_left (mono bn le_rfl) (sub_nonneg.mpr p1)
      have cmp : ∑ r ∈ Ico 2 (n+2), signedWeight j r p s * E b ≤
          ∑ r ∈ Ico 2 (n+2), signedWeight j r p s * E (n+1-r) := by
        apply sum_le_sum
        intro r hr
        obtain ⟨low,up⟩ := mem_Ico.mp hr
        unfold signedWeight
        have w : 0 ≤ tap r p := by unfold tap; positivity
        by_cases jr : j≤r
        · rw [if_pos jr]
          apply mul_le_mul_of_nonpos_left _ (mul_nonpos_of_nonneg_of_nonpos w (by linarith))
          apply mono _ bn
          dsimp [b]; omega
        · rw [if_neg jr,mul_one]
          apply mul_le_mul_of_nonneg_left _ w
          apply mono
          · dsimp [b]; omega
          · omega
      have non := mul_nonneg (two_sum hj big p1 s1 den0) (pos b bn)
      rw [add_mul,sum_mul] at non
      exact non.trans (add_le_add pcmp cmp)
    · apply add_nonneg (mul_nonneg (sub_nonneg.mpr p1) (pos n le_rfl))
      apply sum_nonneg
      intro r hr
      have h := mem_Ico.mp hr
      have jr : ¬ j≤r := by omega
      simp only [signedWeight,if_neg jr,mul_one]
      apply mul_nonneg _ (pos _ (by omega))
      unfold tap; positivity

theorem original_scaled_rows_lower {j n : ℕ} {p s : ℝ} (hj : 2≤j)
    (p1 : 1≤p) (s1 : 1≤s) (den0 : 2-Real.exp p+s*tail j p ≤ 0) :
    1 ≤ positiveScale j n p s := by
  have h := original_scaled_rows_monotone hj p1 s1 den0 (Nat.zero_le n)
  simpa only [positiveScale,pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one,div_one,
    row_zero (by omega : 1≤j),eval_one] using h

#print axioms original_scaled_rows_monotone
#print axioms original_scaled_rows_lower
end OrderedPartitions.CriticalEdge
