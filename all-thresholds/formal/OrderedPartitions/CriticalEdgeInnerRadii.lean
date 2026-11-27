import OrderedPartitions.CriticalEdgeRealWitness
import OrderedPartitions.CriticalEdgeLogRadius
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Sharp limiting distances from zero and one to the full complex root set. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Complex Filter Set Metric
open scoped Topology

def originalZeroSet (k n : ℕ) : Set ℂ := {t | (row n (k+2)).eval₂ ofRealHom t = 0}

/-- The two nearest-root distances use the full original complex zero set. -/
theorem original_inner_radii {k : ℕ} (hk : 2 ≤ k) :
    ∃ a ∈ Ioo (Real.log 2) 1, criticalTest k a = 0 ∧ 1 < ratio k a ∧
      Tendsto (fun n ↦ infDist (1:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a)) ∧
      Tendsto (fun n ↦ infDist (0:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a-1)) := by
  obtain ⟨a, lo, hi, crit, tall, mx⟩ := strict_maximum hk
  refine ⟨a, ⟨lo,hi⟩, crit, tall, ?_⟩
  have ap := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans lo
  let x := Real.pi/2
  let y := Real.pi/2 + Real.pi
  have xp : 0 < x := by dsimp [x]; positivity
  have xy : x < y := by dsimp [x,y]; linarith [Real.pi_pos]
  have sg : Real.sin x * Real.sin y < 0 := by simp [x,y,Real.sin_add_pi, Real.sin_pi_div_two]
  have witnesses := eventual_real_witness lo hi.le crit mx xp xy sg
  let C := ratio k a
  let B := edgeWidth k a * y^2
  have wpos : 0 < edgeWidth k a := by
    unfold edgeWidth
    exact div_pos (by positivity) (tail_pos _ ap)
  have ht : C * tail (k+2) a = Real.exp a - 2 := div_mul_cancel₀ _ (tail_pos _ ap).ne'
  have bd : ∀ᶠ n : ℕ in atTop,
      (C-radialLoss k a C n ≤ infDist (1:ℂ) (originalZeroSet k n) ∧
        infDist (1:ℂ) (originalZeroSet k n) ≤ C+B*((n:ℝ)⁻¹)^2) ∧
      (C-1-radialLoss k a C n ≤ infDist (0:ℂ) (originalZeroSet k n) ∧
        infDist (0:ℂ) (originalZeroSet k n) ≤ C-1+B*((n:ℝ)⁻¹)^2) := by
    filter_upwards [witnesses, eventually_ge_atTop 3] with n hw hn
    obtain ⟨u, hu, zr⟩ := hw
    let t := 1-(C+edgeWidth k a*u*((n:ℝ)⁻¹)^2)
    have mem : (t:ℂ) ∈ originalZeroSet k n := by
      change (row n (k+2)).eval₂ ofRealHom (ofRealHom t) = 0
      rw [Polynomial.eval₂_at_apply, show (row n (k+2)).eval t = 0 from zr, map_zero]
    have un : 0 ≤ u := (sq_nonneg x).trans hu.1.le
    have wn : 0 ≤ edgeWidth k a * u * ((n:ℝ)⁻¹)^2 := by positivity
    have cn : 1 < C := tall
    have tn : t ≤ 0 := by dsimp [t]; linarith
    have d1 : dist (1:ℂ) (t:ℂ) = 1-t := by
      rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have d0 : dist (0:ℂ) (t:ℂ) = -t := by
      rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos tn]
    have ub : edgeWidth k a * u * ((n:ℝ)⁻¹)^2 ≤ B*((n:ℝ)⁻¹)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2.le wpos.le) (sq_nonneg _)
    have lb (z : ℂ) (hz : z ∈ originalZeroSet k n) := root_distance_log_bound lo hi.le tall ht hn hz
    refine ⟨⟨(le_infDist ⟨_,mem⟩).2 (fun {_} hz ↦ by simpa only [dist_eq_norm] using (lb _ hz).1.le), ?_⟩,
      ⟨(le_infDist ⟨_,mem⟩).2 (fun {_} hz ↦ by simpa using (lb _ hz).2.le), ?_⟩⟩
    · apply (infDist_le_dist_of_mem mem).trans
      rw [d1]; dsimp [t]; linarith
    · apply (infDist_le_dist_of_mem mem).trans
      rw [d0]; dsimp [t]; linarith
  have lg : Tendsto (fun n : ℕ ↦ Real.log n / (n:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have loss : Tendsto (radialLoss k a C) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ (2*a*(1+C)*Real.exp a/tail (k+2) a)*(Real.log n/(n:ℝ))) atTop (𝓝 0)
    simpa only [mul_zero] using lg.const_mul (2*a*(1+C)*Real.exp a/tail (k+2) a)
  have inv : Tendsto (fun n : ℕ ↦ (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have up : Tendsto (fun n : ℕ ↦ B*((n:ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa using (inv.pow 2).const_mul B
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds (x:=C) |>.sub loss)
      (by simpa using tendsto_const_nhds (x:=C) |>.add up) (bd.mono fun _ h ↦ h.1.1)
      (bd.mono fun _ h ↦ h.1.2)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds (x:=C-1) |>.sub loss)
      (by simpa using tendsto_const_nhds (x:=C-1) |>.add up) (bd.mono fun _ h ↦ h.2.1)
      (bd.mono fun _ h ↦ h.2.2)

#print axioms original_inner_radii
end OrderedPartitions.CriticalEdge
