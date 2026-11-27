import OrderedPartitions.CriticalEdgeOneResidue
import Mathlib.Analysis.Analytic.Order

/-! Subtracting a displaced pole contour from a coefficient contour. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter Finset
open scoped Topology

/-- The normalized contribution of a displaced circle. -/
def displacedRemainder (g : ℂ → ℂ) (c : ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(c, r), (z ^ (n + 1) * g z)⁻¹

private def originPart (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ range (n + 1), (iteratedDeriv i f 0 / (i.factorial : ℂ)) * z ^ ((i : ℤ) - n - 1)

private theorem originPart_differentiableOn {f : ℂ → ℂ} (n : ℕ) {U : Set ℂ}
    (hne : ∀ z ∈ U, z ≠ 0) : DifferentiableOn ℂ (originPart f n) U := by
  unfold originPart
  exact DifferentiableOn.fun_sum fun i _ ↦
    (differentiableOn_id.zpow (m := (i : ℤ) - n - 1) (.inl hne)).const_mul _

private theorem originPart_integral (f : ℂ → ℂ) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(0, R), originPart f n z) =
      (2 * (Real.pi : ℂ) * I) * (iteratedDeriv n f 0 / (n.factorial : ℂ)) := by
  classical
  have notZero (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    intro e
    subst z
    have hz' : (0 : ℝ) = R := by simpa only [mem_sphere, dist_self] using hz
    exact hR.ne' hz'.symm
  unfold originPart
  rw [circleIntegral.integral_fun_sum]
  · rw [sum_eq_single n]
    · rw [circleIntegral.integral_const_mul]
      simp only [sub_self, zero_sub, zpow_neg_one]
      have h := circleIntegral.integral_sub_center_inv (0 : ℂ) hR.ne'
      rw [show (fun z : ℂ ↦ z⁻¹) = (fun z ↦ (z - 0)⁻¹) by simp, h, mul_comm]
    · intro i _ hin
      rw [circleIntegral.integral_const_mul]
      have e : (i : ℤ) - n - 1 ≠ -1 := by omega
      have he := circleIntegral.integral_sub_zpow_of_ne e (0 : ℂ) (0 : ℂ) R
      rw [show (fun z : ℂ ↦ z ^ ((i : ℤ) - n - 1)) =
        (fun z ↦ (z - 0) ^ ((i : ℤ) - n - 1)) by simp, he, mul_zero]
    · simp
  · intro i _
    exact ((continuousOn_id.zpow₀ _ (fun z hz ↦ .inl (notZero z hz))).const_mul _).circleIntegrable hR.le

private theorem originPart_remove {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ z : ℂ, z ≠ 0 →
      (z ^ (n + 1))⁻¹ * f z = F z + originPart f n z := by
  obtain ⟨F, hFa, split⟩ := hf.exists_eq_sum_add_pow_mul (n + 1)
  refine ⟨F, hFa, fun z hz ↦ ?_⟩
  rw [split z, mul_add, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul, add_comm _ (F z)]
  congr 1
  rw [originPart, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [smul_eq_mul, show (i : ℤ) - n - 1 = (i : ℤ) - ((n + 1 : ℕ) : ℤ) by omega,
    zpow_sub₀ hz, zpow_natCast, zpow_natCast, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- When every non-origin singularity is a simple pole inside the displaced circle, the
coefficient equals the outer circle integral minus that displaced circle integral. -/
theorem coefficient_eq_sub_displaced {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 ≠ 0)
    {R r : ℝ} {c : ℂ} (hR : 0 < R) (hr : 0 < r)
    (inner : closedBall c r ⊆ ball (0 : ℂ) R) (off0 : (0 : ℂ) ∉ closedBall c r)
    (P : Finset ℂ) (pinside : ∀ p ∈ P, p ∈ ball c r)
    (proot : ∀ p ∈ P, g p = 0) (psimple : ∀ p ∈ P, deriv g p ≠ 0)
    (exhaust : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0 → z ∈ P) (n : ℕ) :
    iteratedDeriv n (fun z ↦ (g z)⁻¹) 0 / (n.factorial : ℂ) =
      circleRemainder g R n - displacedRemainder g c r n := by
  classical
  let U := (ball (0 : ℂ) R ∪ {z : ℂ | g z ≠ 0}) \ {(0 : ℂ)}
  have hU : IsOpen U := (isOpen_ball.union (isOpen_ne_fun hg.continuous continuous_const)).sdiff
    isClosed_singleton
  have p0 (p : ℂ) (hp : p ∈ P) : p ≠ 0 := fun e ↦
    off0 (e ▸ ball_subset_closedBall (pinside p hp))
  let q := fun z : ℂ ↦ z ^ (n + 1) * g z
  have qd : Differentiable ℂ q := (differentiable_id.pow _).mul hg
  have qs (p : ℂ) (hp : p ∈ P) : deriv q p ≠ 0 := by
    have h := ((hasDerivAt_pow (n + 1) p).mul (hg p).hasDerivAt).deriv
    change deriv q p = _ at h
    rw [h, proot p hp, mul_zero, zero_add]
    exact mul_ne_zero (pow_ne_zero _ (p0 p hp)) (psimple p hp)
  have nearU (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) (hn : z ≠ 0) : z ∈ U := by
    refine ⟨?_, hn⟩
    by_cases e : g z = 0
    · exact .inl (inner (ball_subset_closedBall (pinside z (exhaust z hz e))))
    · exact .inr e
  obtain ⟨H, hH, split⟩ := FiniteSimplePoles.remove qd hU P
    (fun p hp ↦ by simp [q, proot p hp]) qs (fun z hz e ↦ by
      have gn : g z = 0 := (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ hz.2)
      exact exhaust z (ball_subset_closedBall (hz.1.resolve_right (fun h ↦ h gn))) gn)
  let T := fun z : ℂ ↦ ∑ p ∈ P, FiniteSimplePoles.term q p z
  let f := fun z : ℂ ↦ (g z)⁻¹
  have fa : AnalyticAt ℂ f 0 := (hg.analyticAt 0).inv hg0
  obtain ⟨F, hF, hs⟩ := originPart_remove fa n
  let A := Function.update (fun z ↦ H z - originPart f n z) (0 : ℂ) (F 0 - T 0)
  have Tdiff {V : Set ℂ} (away : ∀ z ∈ V, z ∉ P) : DifferentiableOn ℂ T V := by
    unfold T
    apply DifferentiableOn.fun_sum
    intro p hp
    unfold FiniteSimplePoles.term
    apply ((differentiableOn_id.sub_const p).inv _).const_mul
    intro z hz hz0
    have e : z = p := sub_eq_zero.mp hz0
    exact away z hz (by rw [e]; exact hp)
  have Ta : AnalyticAt ℂ T 0 := by
    let V := {z : ℂ | z ∉ P}
    have V0 : (0 : ℂ) ∈ V := fun h ↦ p0 0 h rfl
    exact (Tdiff (V := V) (fun _ h ↦ h)).analyticAt (P.finite_toSet.isClosed.isOpen_compl.mem_nhds V0)
  have A0 : DifferentiableAt ℂ A 0 := by
    apply (hF.sub Ta).differentiableAt.congr_of_eventuallyEq
    have hn : ∀ᶠ z : ℂ in 𝓝 0, z ∉ P := P.finite_toSet.isClosed.isOpen_compl.mem_nhds
      (fun h ↦ p0 0 h rfl)
    filter_upwards [hn] with z hz
    by_cases e : z = 0
    · subst z
      simp [A]
    · have he := hs z e
      have ht : (q z)⁻¹ = H z + T z := split z hz
      rw [show (q z)⁻¹ = (z ^ (n + 1))⁻¹ * f z by simp [q, f, mul_inv_rev, mul_comm], he] at ht
      simp only [A, Function.update_of_ne e, Pi.sub_apply]
      linear_combination -ht
  have Ad : DifferentiableOn ℂ A (closedBall (0 : ℂ) R) := by
    intro z hz
    by_cases e : z = 0
    · subst z
      exact A0.differentiableWithinAt
    · have Hdiff := (hH z (nearU z hz e)).differentiableAt (hU.mem_nhds (nearU z hz e))
      have OW := originPart_differentiableOn (f := f) n (U := {w | w ≠ 0}) (fun _ h ↦ h) z e
      have ODiff := OW.differentiableAt (isOpen_ne.mem_nhds e)
      apply DifferentiableAt.differentiableWithinAt
      apply (Hdiff.sub ODiff).congr_of_eventuallyEq
      have hn : ∀ᶠ w : ℂ in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds e
      exact hn.mono fun w hw ↦ by simp [A, Function.update_of_ne hw]
  have Aint : (∮ z in C(0, R), A z) = 0 :=
    (Ad.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le
  have Aint' : (∮ z in C(c, r), A z) = 0 :=
    ((Ad.mono (inner.trans ball_subset_closedBall)).diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hr.le
  have Oint' : (∮ z in C(c, r), originPart f n z) = 0 := by
    have od : DifferentiableOn ℂ (originPart f n) (closedBall c r) :=
      originPart_differentiableOn n (fun z hz e ↦ off0 (e ▸ hz))
    exact (od.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hr.le
  have outerAway (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ∉ P := fun h ↦ by
    have ho := mem_ball.mp (inner (ball_subset_closedBall (pinside z h)))
    rw [mem_sphere.mp hz] at ho
    exact (lt_irrefl _ ho)
  have innerAway (z : ℂ) (hz : z ∈ sphere c r) : z ∉ P := fun h ↦ by
    have ho := mem_ball.mp (pinside z h)
    rw [mem_sphere.mp hz] at ho
    exact (lt_irrefl _ ho)
  have sumPart {d : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (incl : closedBall d ρ ⊆ closedBall 0 R)
      (away : ∀ z ∈ sphere d ρ, z ∉ P) (no0 : ∀ z ∈ sphere d ρ, z ≠ 0) :
      (∮ z in C(d, ρ), (q z)⁻¹) = (∮ z in C(d, ρ), A z) +
        (∮ z in C(d, ρ), originPart f n z) + (∮ z in C(d, ρ), T z) := by
    have hA := (Ad.continuousOn.mono (sphere_subset_closedBall.trans incl)).circleIntegrable hρ.le
    have hO := (originPart_differentiableOn (f := f) n no0).continuousOn.circleIntegrable hρ.le
    have hT := (Tdiff away).continuousOn.circleIntegrable hρ.le
    calc
      _ = ∮ z in C(d, ρ), A z + originPart f n z + T z := by
        apply circleIntegral.integral_congr hρ.le
        intro z hz
        have h := split z (away z hz)
        simp only [A, Function.update_of_ne (no0 z hz)]
        change (q z)⁻¹ = H z - originPart f n z + originPart f n z + T z
        rw [sub_add_cancel]
        exact h
      _ = _ := by
        change (∮ z in C(d, ρ), (A + originPart f n) z + T z) = _
        rw [circleIntegral.integral_add (hA.add hO) hT]
        exact congrArg (fun x : ℂ ↦ x + (∮ z in C(d, ρ), T z)) (circleIntegral.integral_add hA hO)
  have Tint : (∮ z in C(0, R), T z) = ∮ z in C(c, r), T z := by
    unfold T
    have hpart (d : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (p : ℂ) (hin : p ∈ ball d ρ) :
        CircleIntegrable (fun z ↦ FiniteSimplePoles.term q p z) d ρ := by
      unfold FiniteSimplePoles.term
      have reg : CircleIntegrable (fun z ↦ (z - p)⁻¹) d ρ := by
        apply circleIntegrable_sub_inv_iff.mpr
        right
        rw [abs_of_pos hρ]
        intro hp
        exact (mem_ball.mp hin).ne (mem_sphere.mp hp)
      exact reg.const_mul _
    rw [circleIntegral.integral_fun_sum (fun p hp ↦ hpart 0 R hR p
      (inner (ball_subset_closedBall (pinside p hp)))),
      circleIntegral.integral_fun_sum (fun p hp ↦ hpart c r hr p (pinside p hp))]
    apply sum_congr rfl
    intro p hp
    simp only [FiniteSimplePoles.term, circleIntegral.integral_const_mul]
    rw [circleIntegral.integral_sub_inv_of_mem_ball (inner (ball_subset_closedBall (pinside p hp))),
      circleIntegral.integral_sub_inv_of_mem_ball (pinside p hp)]
  have o0 (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
    intro e
    rw [e, mem_sphere, dist_self] at hz
    exact hR.ne' hz.symm
  have i0 (z : ℂ) (hz : z ∈ sphere c r) : z ≠ 0 := fun e ↦ off0 (e ▸ sphere_subset_closedBall hz)
  have ho := sumPart hR subset_rfl outerAway o0
  have hi := sumPart hr (inner.trans ball_subset_closedBall) innerAway i0
  rw [Aint, originPart_integral f n hR, zero_add] at ho
  rw [Aint', Oint', zero_add, zero_add] at hi
  change _ = (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(0, R), (q z)⁻¹) -
    (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(c, r), (q z)⁻¹)
  rw [ho, hi, Tint, ← smul_sub, add_sub_cancel_right, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

#print axioms coefficient_eq_sub_displaced

end OrderedPartitions.CriticalEdge
