import OrderedPartitions.CriticalEdgeSmallSharp
import OrderedPartitions.CriticalEdgeInnerRadii

/-! Every fixed threshold ≥2: the two limiting nearest-root radii and sinc scaling
are obtained with one and the same original critical point. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Set Filter Metric
open scoped Topology

private theorem small_distances {k : ℕ} {a : ℝ} (hi : 1<ratio k a)
    (bar : ∀ n : ℕ, ∀ z : ℂ, (row n (k+2)).eval₂ ofRealHom z=0 →
      ∃ t : ℝ, z=(t:ℂ) ∧ t<1-ratio k a)
    (near : ∀ᶠ n : ℕ in atTop, ∃ t : ℝ, (row n (k+2)).eval t=0 ∧
      0<1-ratio k a-t ∧ 1-ratio k a-t≤edgeWidth k a*(3*Real.pi/2)^2*((n:ℝ)⁻¹)^2)
    {b : ℝ} (b0 : 0≤b) :
    Tendsto (fun n : ℕ ↦ infDist (b:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a-1+b)) := by
  let B := edgeWidth k a*(3*Real.pi/2)^2
  have bd : ∀ᶠ n : ℕ in atTop, ratio k a-1+b ≤ infDist (b:ℂ) (originalZeroSet k n) ∧
      infDist (b:ℂ) (originalZeroSet k n) ≤ ratio k a-1+b+B*((n:ℝ)⁻¹)^2 := by
    filter_upwards [near] with n hit
    obtain ⟨t,zero,lo,ub⟩ := hit
    have mem : (t:ℂ) ∈ originalZeroSet k n := by
      change (row n (k+2)).eval₂ ofRealHom (ofRealHom t) = 0
      rw [Polynomial.eval₂_at_apply,zero,map_zero]
    have dst {x : ℝ} (h : x<1-ratio k a) : dist (b:ℂ) (x:ℂ)=b-x := by
      rw [dist_eq_norm,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    constructor
    · apply (le_infDist ⟨_,mem⟩).2
      intro z hz
      obtain ⟨r,rfl,hr⟩ := bar n z hz
      rw [dst hr]
      linarith
    · apply (infDist_le_dist_of_mem mem).trans
      rw [dst (by linarith)]
      dsimp [B]; linarith only [ub]
  have inv : Tendsto (fun n : ℕ ↦ (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have up : Tendsto (fun n : ℕ ↦ B*((n:ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa using (inv.pow 2).const_mul B
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_const_nhds (x:=ratio k a-1+b) |>.add up)
    (bd.mono fun _ h ↦ h.1) (bd.mono fun _ h ↦ h.2)

theorem original_all_inner_edges (k : ℕ) :
    ∃ a ∈ Ioo (Real.log 2) 2, criticalTest k a=0 ∧ 1<ratio k a ∧
      (∀ U : ℝ, TendstoUniformlyOn (fun n : ℕ ↦ normalizedInnerRow k a n) innerSinc atTop
        (closedBall (0:ℂ) U)) ∧
      Tendsto (fun n ↦ infDist (1:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a)) ∧
      Tendsto (fun n ↦ infDist (0:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a-1)) := by
  by_cases hk : 2≤k
  · obtain ⟨a,⟨lo,hi⟩,crit,tall,uniform⟩ := original_inner_sinc_limit hk
    obtain ⟨r,⟨rlo,_⟩,rcrit,_,r1,r0⟩ := original_inner_radii hk
    have ar := (criticalTest_strictAnti k).injOn lo.le rlo.le (crit.trans rcrit.symm)
    subst r
    exact ⟨a,⟨lo,hi.trans (by norm_num)⟩,crit,tall,uniform,r1,r0⟩
  · have low : k=0 ∨ k=1 := by omega
    obtain ⟨a,⟨lo,hi⟩,crit,tall,bar,near⟩ := original_small_sharp_barrier low
    have ap := zero_lt_one.trans lo
    have rho : Real.log 2<a := by linarith [Real.log_two_lt_d9]
    have iso (z : ℂ) (hn : ‖z‖≤a) : generatingDen (k+2) (ratio k a) z=0 → z=(a:ℂ) := by
      rcases low with rfl|rfl
      · exact (threshold_two_critical_half_plane ap crit tall.le ((Complex.re_le_norm z).trans hn)).mp
      · exact threshold_three_critical_isolation lo hi crit tall hn
    refine ⟨a,⟨rho,hi⟩,crit,tall,?_,?_,?_⟩
    · intro U
      let K := max 1 (U+1)
      have k1 : 1≤K := le_max_left _ _
      have ku : U≤K := by linarith only [le_max_right 1 (U+1)]
      have bd : U≤K^2 := by nlinarith only [mul_le_mul_of_nonneg_left k1 (zero_le_one.trans k1),ku]
      exact (normalizedInnerRow_tendsto_sinc_of_isolation ap crit iso (zero_lt_one.trans_le k1)).mono
        (closedBall_subset_closedBall bd)
    · simpa using small_distances tall bar near (b:=1) zero_le_one
    · simpa using small_distances tall bar near (b:=0) le_rfl

#print axioms original_all_inner_edges
end OrderedPartitions.CriticalEdge
