import OrderedPartitions.CriticalEdgePhaseAxis

/-! A common quantitative complex neighborhood for all finite rows. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Set Metric
open scoped Topology ComplexConjugate

/-- The n-independent phase contribution from the two residue amplitudes. -/
def splitBias (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) : ℂ → ℂ :=
  fun v ↦ -pairedLogDiff (residueUnit k a Z) v

theorem splitPhase_add (k n : ℕ) (a : ℝ) (Z : ℂ → ℂ) :
    splitPhase k a Z n = fun v ↦ ((n : ℂ)+1) * pairedLogDiff Z v + splitBias k a Z v := by
  funext v
  simp only [splitPhase, splitBias, Nat.cast_add, Nat.cast_one, sub_eq_add_neg]

theorem conj_imaginaryProjection (z : ℂ) :
    conj (imaginaryProjection z) = -imaginaryProjection z := by
  simp [imaginaryProjection, Complex.conj_I]

theorem re_zero_of_conj_eq_neg {z : ℂ} (h : conj z = -z) : z.re = 0 := by
  have r := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at r
  linarith

/-- Simultaneous closed-disk estimates for the actual local wave model. The error and its
derivative are exponentially small, with constants independent of the rank. -/
structure SplitPhaseDisk (k : ℕ) (a : ℝ) where
  pole : ℂ → ℂ
  radius : ℝ
  biasBound : ℝ
  errorBound : ℝ
  rate : ℝ
  radius_pos : 0 < radius
  biasBound_pos : 0 < biasBound
  errorBound_pos : 0 < errorBound
  rate_pos : 0 < rate
  rate_lt : rate < 1
  leading : ∀ v ∈ closedBall (0 : ℂ) radius,
    AnalyticAt ℂ (pairedLogDiff pole) v ∧ ‖deriv (pairedLogDiff pole) v - 1‖ ≤ 1 / 4
  bias : ∀ v ∈ closedBall (0 : ℂ) radius,
    AnalyticAt ℂ (splitBias k a pole) v ∧ ‖deriv (splitBias k a pole) v‖ ≤ biasBound
  error : ∀ n v, v ∈ closedBall (0 : ℂ) radius →
    AnalyticAt ℂ (splitDefect k a pole n) v ∧
      ‖splitDefect k a pole n v‖ ≤ errorBound * ‖v‖ * rate ^ n ∧
      ‖deriv (splitDefect k a pole n) v‖ ≤ (2 * errorBound) * rate ^ n
  realLeading : ∀ v ∈ closedBall (0 : ℂ) radius,
    pairedLogDiff pole (conj v) = conj (pairedLogDiff pole v)
  realBias : ∀ v ∈ closedBall (0 : ℂ) radius,
    splitBias k a pole (conj v) = conj (splitBias k a pole v)
  error_conj : ∀ n v, v ∈ closedBall (0 : ℂ) radius →
    splitDefect k a pole n (conj v) = conj (splitDefect k a pole n v)
  analyticScale : ∀ n v, v ∈ closedBall (0 : ℂ) radius →
    AnalyticAt ℂ (splitScale k a pole n) v

set_option maxHeartbeats 500000 in
theorem splitPhaseDisk_nonempty_of_isolation {k : ℕ} {a : ℝ} (ap : 0 < a)
    (crit : criticalTest k a = 0)
    (isolated : ∀ z : ℂ, ‖z‖ ≤ a → generatingDen (k+2) (ratio k a) z = 0 → z = (a : ℂ)) :
    Nonempty (SplitPhaseDisk k a) := by
  obtain ⟨R,Z,K,q,_,Kp,qp,q1,za,z0,zd,realZ,model⟩ :=
    split_phase_model_of_isolation ap crit isolated
  let W := pairedLogDiff Z
  let B := residueUnit k a Z
  let F := splitBias k a Z
  have za0 : Z 0 ∈ slitPlane := by rw [z0]; exact ofReal_mem_slitPlane.mpr ap
  have ba := residueUnit_analytic ap crit za z0 zd
  have b0 : B 0 ∈ slitPlane := by
    rw [show B 0 = (((2 * ((k : ℝ) + 1))⁻¹ : ℝ) : ℂ) from residueUnit_at_zero ap crit za z0 zd]
    exact ofReal_mem_slitPlane.mpr (by positivity)
  have wa : AnalyticAt ℂ W 0 := (paired_analytic za za0).1
  have fa : AnalyticAt ℂ F 0 := (paired_analytic ba b0).1.neg
  have wd : deriv W 0 = 1 := by
    have A : (a : ℂ) ≠ 0 := by exact_mod_cast ap.ne'
    simpa only [zd, z0, div_self A] using (pairedLogDiff_derivative za za0).deriv
  let M := 1 + ‖deriv F 0‖
  have Mp : 0 < M := by dsimp [M]; positivity
  have wclose : ∀ᶠ v : ℂ in 𝓝 0, ‖deriv W v - 1‖ ≤ 1 / 4 := by
    have CONT : ContinuousAt (fun v : ℂ ↦ ‖deriv W v - 1‖) 0 :=
      (wa.deriv.continuousAt.sub continuousAt_const).norm
    have h₀ : ‖deriv W 0 - 1‖ < 1 / 4 := by rw [wd, sub_self, norm_zero]; norm_num
    exact (CONT.eventually (gt_mem_nhds h₀)).mono fun _ h ↦ h.le
  have fclose : ∀ᶠ v : ℂ in 𝓝 0, ‖deriv F v‖ ≤ M := by
    have h₀ : ‖deriv F 0‖ < M := by dsimp [M]; linarith
    exact (fa.deriv.continuousAt.norm.eventually (gt_mem_nhds h₀)).mono fun _ h ↦ h.le
  have realW := (paired_conj_germ za.continuousAt za0 realZ).mono (fun _ r ↦ r.1)
  have realB := residueUnit_conj_germ ap crit za z0 zd realZ
  have realF : ∀ᶠ v : ℂ in 𝓝 0, F (conj v) = conj (F v) :=
    (paired_conj_germ ba.continuousAt b0 realB).mono (fun v h ↦ by
      change -pairedLogDiff B (conj v) = conj (-pairedLogDiff B v)
      rw [h.1, map_neg])
  have realE := splitDefect_conj_germ ap crit za z0 zd realZ
  have holoE := splitDefect_analytic_germ ap crit za z0 zd
  have holoScale := splitScale_analytic_germ ap crit za z0 zd
  have ev := wa.eventually_analyticAt.and (wclose.and (fa.eventually_analyticAt.and
    (fclose.and (model.and (holoE.and (realW.and (realF.and (realE.and holoScale))))))))
  obtain ⟨δ, δp, data⟩ := Metric.eventually_nhds_iff.mp ev
  let r := δ / 4
  have rp : 0 < r := by dsimp [r]; positivity
  have sub : 2 * r < δ := by dsimp [r]; linarith
  have obey (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) (2*r)) :=
    data ((mem_closedBall.mp hv).trans_lt sub)
  have le_twice (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) r) :
      v ∈ closedBall (0 : ℂ) (2*r) :=
    closedBall_subset_closedBall (by linarith) hv
  let E := splitDefect k a Z
  have errNorm (n : ℕ) (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) (2*r)) :
      ‖E n v‖ ≤ K * ‖v‖ * q^n := by
    have eq := (obey v hv).2.2.2.2.1 n
    unfold E splitDefect
    rw [eq.1, add_sub_cancel_left]
    exact eq.2
  have errAna (n : ℕ) (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) (2*r)) :
      AnalyticAt ℂ (E n) v := (obey v hv).2.2.2.2.2.1 n
  refine ⟨⟨Z,r,M,K,q,rp,Mp,Kp,qp,q1,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro v hv
    exact ⟨(obey v (le_twice v hv)).1, (obey v (le_twice v hv)).2.1⟩
  · intro v hv
    exact ⟨(obey v (le_twice v hv)).2.2.1, (obey v (le_twice v hv)).2.2.2.1⟩
  · intro n v hv
    have big := le_twice v hv
    refine ⟨errAna n v big, errNorm n v big, ?_⟩
    have nv : ‖v‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hv
    have Q (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) (2*r)) :
        ‖E n w‖ ≤ K * (2*r) * q^n := by
      have nw : ‖w‖ ≤ 2*r := by simpa only [mem_closedBall, dist_zero_right] using hw
      exact (errNorm n w hw).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left nw Kp.le) (by positivity))
    refine (deriv_bound_half_disk rp (errAna n) Q nv).trans_eq ?_
    field_simp [rp.ne']
  · intro v hv
    exact (obey v (le_twice v hv)).2.2.2.2.2.2.1
  · intro v hv
    exact (obey v (le_twice v hv)).2.2.2.2.2.2.2.1
  · intro n v hv
    exact (obey v (le_twice v hv)).2.2.2.2.2.2.2.2.1 n
  · intro n v hv
    exact (obey v (le_twice v hv)).2.2.2.2.2.2.2.2.2 n

theorem splitPhaseDisk_nonempty {k : ℕ} {a : ℝ} (ha : Real.log 2 < a) (a1 : a ≤ 1)
    (crit : criticalTest k a = 0) (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) :
    Nonempty (SplitPhaseDisk k a) := by
  apply splitPhaseDisk_nonempty_of_isolation ((Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha) crit
  intro z hn hz
  exact (critical_denominator_closed_disk ha a1 hmax hn).mp hz

#print axioms splitPhaseDisk_nonempty_of_isolation
#print axioms splitPhaseDisk_nonempty

end OrderedPartitions.CriticalEdge
