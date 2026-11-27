import OrderedPartitions.CriticalEdgePhaseCounting

/-! Real phase data for the moving-index argument, retaining every zero in the chosen window. -/
noncomputable section
namespace OrderedPartitions.CriticalEdgeRank
open Real Set

structure PhaseRow (n : ℕ) (d : ℝ) (φ e : ℝ → ℝ) : Prop where
  center : φ 0=0
  phaseDiff : ∀ y ∈ Icc 0 d, DifferentiableAt ℝ φ y
  growth : ∀ y ∈ Icc 0 d, max 1 ((n:ℝ)/2) ≤ deriv φ y
  errDiff : ∀ y ∈ Icc 0 d, DifferentiableAt ℝ e y
  errVal : ∀ y ∈ Icc 0 d, |e y| ≤ y/16
  errDer : ∀ y ∈ Icc 0 d, |deriv e y| ≤ 1/4

def InPhaseCell (φ e : ℝ → ℝ) (m : ℕ) (y : ℝ) : Prop :=
  sin (φ y)+e y=0 ∧ |φ y-(m:ℝ)*π|≤π/4

namespace PhaseRow
variable {n : ℕ} {d : ℝ} {φ e : ℝ → ℝ} (R : PhaseRow n d φ e)
include R

theorem increments {x y : ℝ} (hx : x∈Icc 0 d) (hy : y∈Icc 0 d) (xy : x≤y) :
    max 1 ((n:ℝ)/2)*(y-x) ≤ φ y-φ x :=
  (convex_Icc 0 d).mul_sub_le_image_sub_of_le_deriv
    (fun t ht ↦ (R.phaseDiff t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (R.phaseDiff t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ R.growth t (interior_subset ht)) x hx y hy xy

theorem unit_increment {x y : ℝ} (hx : x∈Icc 0 d) (hy : y∈Icc 0 d) (xy : x≤y) :
    y-x ≤ φ y-φ x := by
  have h := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) ((n:ℝ)/2)) (sub_nonneg.mpr xy)
  rw [one_mul] at h
  exact h.trans (R.increments hx hy xy)

theorem cell_error {m : ℕ} {y : ℝ} (hy : y∈Icc 0 d) (hit : InPhaseCell φ e m y) :
    |φ y-(m:ℝ)*π|≤y/8 := by
  obtain ⟨z,b⟩ := hit
  have j := mul_abs_le_abs_sin (b.trans (by linarith [pi_pos] : π/4≤π/2))
  rw [sin_sub_nat_mul_pi,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    show sin (φ y) = -e y by linarith,abs_neg] at j
  have c : 1/2 ≤ 2/π := (le_div_iff₀ pi_pos).mpr (by linarith [pi_lt_four])
  linarith [mul_le_mul_of_nonneg_right c (abs_nonneg (φ y-(m:ℝ)*π)),R.errVal y hy]

/-- Every genuine positive zero receives a positive index. -/
theorem covers {y : ℝ} (hy : y∈Ioc 0 d) (d1 : d≤1) (hz : sin (φ y)+e y=0) :
    ∃ m : ℕ, 1≤m ∧ InPhaseCell φ e m y := by
  have ym : y∈Icc 0 d := ⟨hy.1.le,hy.2⟩
  have grow := R.unit_increment (left_mem_Icc.mpr (ym.1.trans ym.2)) ym ym.1
  rw [R.center,sub_zero,sub_zero] at grow
  obtain ⟨m,mp,err⟩ := positive_zero_phase_index hy.1 grow hz (R.errVal y ym)
  exact ⟨m,mp,hz,by linarith only [err,R.errVal y ym,ym.2,d1,pi_gt_three]⟩

/-- The entire range m ≤ dn/(4π) fits in the window once dn≥π. -/
theorem linear_cells (d0 : 0≤d) (d1 : d≤1) (large : π≤d*(n:ℝ))
    {m : ℕ} (mp : 1≤m) (fit : (m:ℝ)≤d*(n:ℝ)/(4*π)) :
    ∃ y ∈ Ioo 0 d, InPhaseCell φ e m y ∧ deriv (fun t ↦ sin (φ t)+e t) y ≠ 0 ∧
      ∀ z ∈ Icc 0 d, InPhaseCell φ e m z → z=y := by
  have md : (1:ℝ)≤m := by exact_mod_cast mp
  have left : φ 0≤(m:ℝ)*π-π/4 := by
    rw [R.center]; linarith [mul_le_mul_of_nonneg_right md pi_pos.le,pi_pos]
  have dphase := R.increments (left_mem_Icc.mpr d0) (right_mem_Icc.mpr d0) d0
  rw [R.center,sub_zero,sub_zero] at dphase
  have mn := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) ((n:ℝ)/2)) d0
  have fit' := (le_div_iff₀ (by positivity : 0<4*π)).mp fit
  have right : (m:ℝ)*π+π/4≤φ d := by nlinarith only [dphase,mn,fit',large]
  obtain ⟨y,hy,hz,hb,hd,uniq⟩ := indexed_sine_cell m d0 left right (le_refl (1/4:ℝ))
    (fun t ht ↦ ⟨R.phaseDiff t ht,(le_max_left ..).trans (R.growth t ht)⟩)
    (fun t ht ↦ ⟨R.errDiff t ht,by linarith only [R.errVal t ht,ht.2,d1],R.errDer t ht⟩)
  exact ⟨y,hy,⟨hz,by linarith only [hb,R.errVal y (Ioo_subset_Icc_self hy),hy.2,d1,pi_gt_three]⟩,
    hd,fun z zm h ↦ uniq z zm h.2 h.1⟩

/-- Indices are strictly ordered in physical coordinates. The claim includes
any positive zero in the window, even in the last partial phase cell. -/
theorem index_order {y z : ℝ} {i j : ℕ} (hy : y∈Icc 0 d) (hz : z∈Icc 0 d)
    (yi : InPhaseCell φ e i y) (zj : InPhaseCell φ e j z) (ij : i<j) : y<z := by
  have sep : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast ij
  by_contra! zy
  linarith [(abs_le.mp yi.2).2,(abs_le.mp zj.2).1,R.unit_increment hz hy zy,
    mul_le_mul_of_nonneg_right sep pi_pos.le,pi_pos]

end PhaseRow
#print axioms PhaseRow.covers
#print axioms PhaseRow.linear_cells
#print axioms PhaseRow.index_order
end OrderedPartitions.CriticalEdgeRank
