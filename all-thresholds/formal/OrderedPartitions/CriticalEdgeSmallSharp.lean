import OrderedPartitions.CriticalEdgeSmallComplexBarrier
import OrderedPartitions.CriticalEdgeThreeIsolation
import OrderedPartitions.CriticalEdgeRealWitness

/-! At thresholds two and three the critical marker is a strict barrier at every rank,
and an original negative root approaches it at rate O(n⁻²). -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Filter Set Metric
open scoped Topology

theorem original_small_sharp_barrier {k : ℕ} (low : k=0 ∨ k=1) :
    ∃ a ∈ Ioo (1:ℝ) 2, criticalTest k a=0 ∧ 1<ratio k a ∧
      (∀ n : ℕ, ∀ z : ℂ, (row n (k+2)).eval₂ ofRealHom z=0 →
        ∃ t : ℝ, z=(t:ℂ) ∧ t < 1-ratio k a) ∧
      (∀ᶠ n : ℕ in atTop, ∃ t : ℝ, (row n (k+2)).eval t=0 ∧
        0 < 1-ratio k a-t ∧ 1-ratio k a-t ≤
          edgeWidth k a * (3*Real.pi/2)^2 * ((n:ℝ)⁻¹)^2) := by
  obtain ⟨a,⟨lo,hi⟩,crit,tall,allRoots⟩ := original_small_complex_barrier low
  refine ⟨a,⟨lo,hi⟩,crit,tall,allRoots,?_⟩
  have ap := zero_lt_one.trans lo
  let x := Real.pi/2
  let y := Real.pi/2+Real.pi
  have xp : 0<x := by dsimp [x]; positivity
  have xy : x<y := by dsimp [x,y]; linarith [Real.pi_pos]
  have sgn : Real.sin x*Real.sin y < 0 := by simp [x,y,Real.sin_add_pi,Real.sin_pi_div_two]
  have iso (z : ℂ) (hn : ‖z‖≤a) : generatingDen (k+2) (ratio k a) z=0 → z=(a:ℂ) := by
    rcases low with rfl|rfl
    · exact (threshold_two_critical_half_plane ap crit tall.le ((Complex.re_le_norm z).trans hn)).mp
    · exact threshold_three_critical_isolation lo hi crit tall hn
  have near := eventual_real_witness_of_isolation ap crit iso xp xy sgn
  have width : 0<edgeWidth k a := by
    unfold edgeWidth
    exact div_pos (by positivity) (tail_pos _ ap)
  filter_upwards [near,eventually_ne_atTop 0] with n hit hn
  obtain ⟨u,hu,zr⟩ := hit
  refine ⟨_,zr,?_,?_⟩
  · have u0 := (sq_pos_of_pos xp).trans hu.1
    have wp : 0<edgeWidth k a*u*((n:ℝ)⁻¹)^2 := by positivity
    linarith only [wp]
  · have yy : (3*Real.pi/2)^2=y^2 := by dsimp [y]; ring
    rw [yy]
    have ub := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2.le width.le) (sq_nonneg ((n:ℝ)⁻¹))
    linarith only [ub]

#print axioms original_small_sharp_barrier
end OrderedPartitions.CriticalEdge
