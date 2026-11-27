import OrderedPartitions.CriticalEdgeAllThresholds
import OrderedPartitions.CriticalEdgeRankedWindow

/-! Unconditional bounded-gap interlacing for a positive linear proportion
of the smallest-modulus roots at every fixed threshold. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Filter Set

theorem original_linear_prefix (k H : ℕ) : SplitPhaseDisk.LinearPrefix k H := by
  obtain ⟨a,⟨lo,_⟩,crit,tall,_,r1,_⟩ := original_all_inner_edges k
  have ap := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans lo
  have iso (z : ℂ) (hn : ‖z‖≤a) (hz : generatingDen (k+2) (ratio k a) z=0) : z=(a:ℂ) := by
    by_cases hk : 2≤k
    · obtain ⟨b,bl,bh,bt,_,mx⟩ := strict_maximum hk
      have eqn := (criticalTest_strictAnti k).injOn lo.le bl.le (crit.trans bt.symm)
      subst b
      exact (critical_denominator_closed_disk lo bh.le mx hn).mp hz
    · have low : k=0 ∨ k=1 := by omega
      obtain ⟨b,⟨bl,bh⟩,bt,_,_,_⟩ := original_small_sharp_barrier low
      have blo : Real.log 2≤b := by linarith [Real.log_two_lt_d9]
      have eqn := (criticalTest_strictAnti k).injOn lo.le blo (crit.trans bt.symm)
      subst b
      rcases low with rfl|rfl
      · exact (threshold_two_critical_half_plane ap crit tall.le ((Complex.re_le_norm z).trans hn)).mp hz
      · exact threshold_three_critical_isolation bl bh crit tall hn hz
  obtain ⟨D⟩ := splitPhaseDisk_nonempty_of_isolation ap crit iso
  exact D.linear_prefix_of_infDist H ap tall r1

#print axioms original_linear_prefix
end OrderedPartitions.CriticalEdge
