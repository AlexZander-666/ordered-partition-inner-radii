import OrderedPartitions.CriticalEdgeIndexedCells
import Mathlib.Algebra.Order.Round

/-! Phase localization for every zero and comparison of moving phase cells. -/
noncomputable section
namespace OrderedPartitions.CriticalEdgeRank
open Real Set

/-- Rounding the phase to the nearest integer multiple of π localizes every
zero, including those not initially constructed from a sign change. -/
theorem zero_phase_index {u e : ℝ} (zero : sin u + e = 0) :
    ∃ m : ℤ, |u-(m:ℝ)*π| ≤ 2*|e| := by
  let m : ℤ := round (u/π)
  have rd : |u-(m:ℝ)*π| ≤ π/2 := by
    have mul := mul_le_mul_of_nonneg_right (abs_sub_round (u/π)) pi_pos.le
    have id : (u/π-(m:ℝ))*π = u-(m:ℝ)*π := by field_simp
    rw [← id, abs_mul, abs_of_pos pi_pos]
    exact mul.trans_eq (by ring)
  have b := mul_abs_le_abs_sin rd
  rw [sin_sub_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul] at b
  rw [show sin u = -e by linarith, abs_neg] at b
  have c : 1/2 ≤ 2/π := (le_div_iff₀ pi_pos).mpr (by linarith [pi_lt_four])
  exact ⟨m,by linarith [mul_le_mul_of_nonneg_right c (abs_nonneg (u-(m:ℝ)*π))]⟩

/-- Both neighboring rows are evaluated at their actual zeros. Relative
phase errors vanish at the origin, so the comparison is uniform even for
the very first retained zero. The larger-coordinate bound is independent of rank. -/
theorem interlace_relative_cells {φ ψ : ℝ → ℝ} {x y z d p : ℝ} (hy : 0<y)
    (xd : x≤d) (yd : y≤d) (zd : z≤d) (d1 : d≤1)
    (slope : ∀ a ∈ Icc 0 d, ∀ b ∈ Icc 0 d, a≤b → b-a ≤ ψ b-ψ a)
    (xp : 0≤x) (zp : 0≤z)
    (old : |φ y-p|≤y/8) (next : |ψ x-p|≤x/8) (after : |ψ z-(p+π)|≤z/8)
    (drift_lo : y/2 ≤ ψ y-φ y) (drift_hi : ψ y-φ y ≤ π/2) : x<y ∧ y<z := by
  obtain ⟨ol,oh⟩ := abs_le.mp old
  obtain ⟨_,xh⟩ := abs_le.mp next
  obtain ⟨zl,_⟩ := abs_le.mp after
  constructor
  · by_contra! yx
    linarith [slope y ⟨hy.le,yd⟩ x ⟨xp,xd⟩ yx]
  · by_contra! zy
    linarith only [slope z ⟨zp,zd⟩ y ⟨hy.le,yd⟩ zy,pi_gt_three,zy,drift_hi,oh,zl,yd,zd,d1]

/-- A point strictly after the center cannot be the artificial central
zero once the phase grows at least as fast as the coordinate. -/
theorem positive_zero_phase_index {u e y : ℝ} (hy : 0<y) (grow : y≤u)
    (zero : sin u + e = 0) (small : |e|≤y/16) :
    ∃ k : ℕ, 1≤k ∧ |u-(k:ℝ)*π|≤2*|e| := by
  obtain ⟨m,b⟩ := zero_phase_index zero
  have pos : 0<m := by
    by_contra! h
    have hm : (m:ℝ)≤0 := by exact_mod_cast h
    linarith [(abs_le.mp b).2,mul_nonpos_of_nonpos_of_nonneg hm pi_pos.le]
  lift m to ℕ using pos.le
  exact ⟨m,by omega,by simpa using b⟩

#print axioms zero_phase_index
#print axioms interlace_relative_cells
#print axioms positive_zero_phase_index
end OrderedPartitions.CriticalEdgeRank
