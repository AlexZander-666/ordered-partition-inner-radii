import OrderedPartitions.CriticalEdgeOuterDecay
import OrderedPartitions.CriticalEdgeMovingPoles
import OrderedPartitions.CriticalEdgeSincZeros

/-! The locally uniform sinc limit for the actual ordered set-partition row. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter
open scoped Topology

private theorem normalizedInnerRow_continuous (k n : ℕ) (a : ℝ) :
    Continuous (normalizedInnerRow k a n) := by
  unfold normalizedInnerRow edgeActivity
  fun_prop

/-- The normalized original row tends uniformly to the entire sinc series on each fixed marker disk. -/
theorem normalizedInnerRow_tendsto_sinc_of_isolation {k : ℕ} {a : ℝ} (ap : 0<a) (hz : criticalTest k a=0)
    (isolated : ∀ z : ℂ, ‖z‖≤a → generatingDen (k+2) (ratio k a) z=0 → z=(a:ℂ))
    {K : ℝ} (hK : 0<K) :
    TendstoUniformlyOn (fun n : ℕ ↦ normalizedInnerRow k a n) innerSinc atTop
      (closedBall (0 : ℂ) (K ^ 2)) := by
  obtain ⟨R, Ra, edge, geo⟩ := two_pole_contour_geometry_of_isolation ap hz isolated
  let M := 2 * K + 1
  have Mp : 0 < M := by dsimp [M]; positivity
  have KM : K ^ 2 < M ^ 2 := by dsimp [M]; nlinarith [sq_nonneg K]
  let Outer := fun n : ℕ ↦ fun u : ℂ ↦ edgeCoefficientScale k a n *
    circleRemainder (generatingDen (k + 2) (edgeActivity k a n u)) R n
  let Inner := fun n : ℕ ↦ fun u : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ •
    ∮ v in C(0, M), scaledKernel k a n u v
  let Limit := fun u : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ •
    ∮ v in C(0, M), Complex.exp (-v) / (v ^ 2 + u)
  have out : TendstoUniformlyOn Outer (fun _ ↦ 0) atTop (closedBall (0 : ℂ) (K ^ 2)) :=
    outer_contour_tendsto_uniformly ap Ra edge _
  have inside : TendstoUniformlyOn Inner Limit atTop (closedBall (0 : ℂ) (K ^ 2)) :=
    scaledCircle_tendsto_uniformly ap hz Mp KM
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε he
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp out (ε / 4) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp inside (ε / 4) (by positivity), geo K hK, eventually_ne_atTop 0]
    with n outSmall innerClose geom n0
  obtain ⟨inc, away, poles⟩ := geom
  have actEq (u : ℂ) : edgeActivity k a n u =
      (ratio k a : ℂ) + (edgeWidth k a : ℂ) * u / (n : ℂ) ^ 2 := by
    rw [edgeActivity, div_eq_mul_inv, inv_pow]
  have small (u : ℂ) (hu : u ∈ closedBall (0 : ℂ) (K ^ 2)) (u0 : u ≠ 0) :
      dist (innerSinc u) (normalizedInnerRow k a n u) < ε / 2 := by
    have un : ‖u‖ ≤ K ^ 2 := by simpa only [mem_closedBall, dist_zero_right] using hu
    obtain ⟨P, _, pprop, ex⟩ := poles u u0 un
    have exactRow := normalizedRow_eq_contours n0 ap (ap.trans Ra) Mp hz u inc away P
      (fun p hp ↦ (pprop p hp).1)
      (fun p hp ↦ by simpa only [actEq] using (pprop p hp).2.1)
      (fun p hp ↦ by simpa only [actEq] using (pprop p hp).2.2)
      (fun z hz0 zero ↦ ex z hz0 (by simpa only [actEq] using zero))
    have rowEq : normalizedInnerRow k a n u = Outer n u - Inner n u := exactRow
    have si : innerSinc u = -Limit u := (limiting_contour_eq_sinc Mp (un.trans_lt KM)).symm
    have i := innerClose u hu
    have o := outSmall u hu
    rw [dist_eq_norm] at i
    rw [dist_zero_left] at o
    rw [dist_eq_norm, rowEq, si, show -Limit u - (Outer n u - Inner n u) =
      (Inner n u - Limit u) - Outer n u by ring]
    have tri := norm_sub_le (Inner n u - Limit u) (Outer n u)
    rw [norm_sub_rev (Inner n u)] at tri
    linarith only [tri, i, o]
  intro u hu
  by_cases u0 : u = 0
  · subst u
    have co : ContinuousAt (fun z : ℂ ↦ dist (innerSinc z) (normalizedInnerRow k a n z)) 0 :=
      innerSinc_analytic_zero.continuousAt.dist (normalizedInnerRow_continuous k n a).continuousAt
    have nearBall : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ closedBall (0 : ℂ) (K ^ 2) :=
      nhdsWithin_le_nhds (closedBall_mem_nhds _ (pow_pos hK 2))
    have near : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        dist (innerSinc z) (normalizedInnerRow k a n z) ≤ ε / 2 := by
      filter_upwards [nearBall, self_mem_nhdsWithin] with z hball hn
      exact (small z hball hn).le
    have b := le_of_tendsto (co.tendsto.mono_left nhdsWithin_le_nhds) near
    exact b.trans_lt (half_lt_self he)
  · exact (small u hu u0).trans (half_lt_self he)

theorem normalizedInnerRow_tendsto_sinc {k : ℕ} {a : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (hz : criticalTest k a = 0) (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a)
    {K : ℝ} (hK : 0 < K) :
    TendstoUniformlyOn (fun n : ℕ ↦ normalizedInnerRow k a n) innerSinc atTop
      (closedBall (0 : ℂ) (K ^ 2)) := by
  apply normalizedInnerRow_tendsto_sinc_of_isolation ((Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha) hz _ hK
  intro z hn h
  exact (critical_denominator_closed_disk ha ha₁ hmax hn).mp h

/-- The same limit on every bounded disk, with existence of the true critical point for each
threshold `j = k+2 ≥ 4`. -/
theorem original_inner_sinc_limit {k : ℕ} (hk : 2 ≤ k) :
    ∃ a ∈ Ioo (Real.log 2) 1, criticalTest k a = 0 ∧ 1 < ratio k a ∧ ∀ U : ℝ,
      TendstoUniformlyOn (fun n : ℕ ↦ normalizedInnerRow k a n) innerSinc atTop
        (closedBall (0 : ℂ) U) := by
  obtain ⟨a, lo, hi, crit, tall, hmax⟩ := strict_maximum hk
  refine ⟨a, ⟨lo, hi⟩, crit, tall, fun U ↦ ?_⟩
  let K := max 1 (U + 1)
  have k1 : 1 ≤ K := le_max_left _ _
  have kU : U ≤ K := by linarith only [le_max_right 1 (U + 1)]
  have power : U ≤ K ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left k1 (by linarith : 0 ≤ K)
    dsimp only [K] at hp kU ⊢
    nlinarith only [hp, kU]
  exact (normalizedInnerRow_tendsto_sinc lo hi.le crit hmax (zero_lt_one.trans_le k1)).mono
    (closedBall_subset_closedBall power)

#print axioms normalizedInnerRow_tendsto_sinc
#print axioms original_inner_sinc_limit

end OrderedPartitions.CriticalEdge
