import OrderedPartitions.CriticalEdgeOnePole
import OrderedPartitions.CriticalEdgeScalar
import OrderedPartitions.ThreePoleDiskExistence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The subcritical pole tends to the positive critical boundary point, and there are no other
zeros in the closed critical disk at the critical parameter. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open CriticalEdgeCircle Real Metric Set Filter Finset
open scoped Topology

private theorem contact_eq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ratio k a * (exp a - ∑ n ∈ range (k + 2), a ^ n / (n.factorial : ℝ)) = exp a - 2 := by
  exact div_mul_cancel₀ _ (tail_pos (k + 2) ha).ne'

private theorem tail_nonneg_at {j : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tail j x :=
  sub_nonneg.mpr (Real.sum_le_exp_of_nonneg hx j)

private theorem tail_le_exp_at (j : ℕ) {x : ℝ} (hx : 0 ≤ x) : tail j x ≤ exp x := by
  exact sub_le_self _ (sum_nonneg fun _ _ ↦ div_nonneg (pow_nonneg hx _) (by positivity))

private theorem norm_tailComplex_le_exp (j : ℕ) (z : ℂ) : ‖tailComplex j z‖ ≤ exp ‖z‖ :=
  (norm_tailComplex_le j z).trans (tail_le_exp_at j (norm_nonneg z))

private theorem re_denominator (k : ℕ) (s x : ℝ) : (denominator (k + 2) s x).re = den k s x := by
  rw [denominator_ofReal, Complex.ofReal_re]
  rfl

private theorem critical_den_pos {k : ℕ} {a : ℝ} (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a)
    {x : ℝ} (hx : 0 ≤ x) (hxa : x < a) : 0 < den k (ratio k a) x := by
  rcases eq_or_lt_of_le hx with h0 | hp
  · subst x
    rw [← re_denominator, Complex.ofReal_zero, denominator_at_zero (by omega)]
    exact zero_lt_one
  · have hn := tail_pos (k + 2) hp
    have hr := (div_lt_iff₀ hn).mp (hmax x hp hxa.ne)
    dsimp [den]
    linarith only [hr]

/-- Near the critical parameter, the true real denominator has no zero in any fixed
positive real interval ending strictly before the tangency. -/
theorem near_critical_axis_nonzero {k : ℕ} {a r : ℝ}
    (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) (hr : 0 ≤ r) (hra : r < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - ratio k a| < ε → ∀ x ∈ Icc 0 r,
      denominator (k + 2) s x ≠ 0 := by
  let C := ratio k a
  have hc : Continuous (den k C) := continuous_iff_continuousAt.mpr
    (fun x ↦ (den_deriv k C x).continuousAt)
  obtain ⟨y, hy, min_y⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hr) hc.continuousOn
  have hypos : 0 < den k C y := critical_den_pos hmax hy.1 (hy.2.trans_lt hra)
  let ε := den k C y / (2 * exp a)
  have εpos : 0 < ε := div_pos hypos (by positivity)
  refine ⟨ε, εpos, ?_⟩
  intro s hs x hx hzero
  have hlow : den k C y ≤ den k C x := min_y hx
  have hbound : tail (k + 2) x ≤ exp a :=
    (tail_le_exp_at (k + 2) hx.1).trans (exp_le_exp.mpr (hx.2.trans hra.le))
  have hdelta : |den k s x - den k C x| < den k C y / 2 := by
    have hd : den k s x - den k C x = (s - C) * tail (k + 2) x := by unfold den; ring
    rw [hd, abs_mul, abs_of_nonneg (tail_nonneg_at hx.1)]
    calc
      _ ≤ |s - C| * exp a := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ < ε * exp a := mul_lt_mul_of_pos_right hs (exp_pos _)
      _ = _ := by dsimp [ε]; field_simp [exp_ne_zero a]
  have hx0 : den k s x = 0 := by
    rw [← re_denominator, hzero, Complex.zero_re]
  rw [hx0, zero_sub, abs_neg, abs_of_pos (hypos.trans_le hlow)] at hdelta
  linarith only [hlow, hypos, hdelta]

/-- Any real branch of the positive subcritical pole tends to the tangency from the left. -/
theorem positive_pole_tendsto_critical {k : ℕ} {a : ℝ}
    (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) {p : ℝ → ℝ}
    (branch : ∀ᶠ s in 𝓝[<] (ratio k a), p s ∈ Ioo 0 a ∧ denominator (k + 2) s (p s) = 0) :
    Tendsto p (𝓝[<] (ratio k a)) (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_cases ha : 0 < a
  · let r := max 0 (a - ε)
    have hr : 0 ≤ r := le_max_left _ _
    have hra : r < a := max_lt_iff.mpr ⟨ha, sub_lt_self _ hε⟩
    obtain ⟨δ, hδ, axis⟩ := near_critical_axis_nonzero hmax hr hra
    have near : ∀ᶠ s : ℝ in 𝓝[<] (ratio k a), |s - ratio k a| < δ := by
      have hb := ball_mem_nhds (ratio k a) hδ
      exact Filter.mem_of_superset (nhdsWithin_le_nhds hb) (fun s hs ↦ by
        change |s - ratio k a| < δ
        simpa only [mem_ball, Real.dist_eq] using hs)
    filter_upwards [branch, near] with s ⟨hp, hz⟩ hs
    have hgt : r < p s := lt_of_not_ge fun h ↦ axis s hs (p s) ⟨hp.1.le, h⟩ hz
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hp.2)]
    have hlow : a - ε ≤ r := le_max_right _ _
    linarith only [hgt, hlow]
  · filter_upwards [branch] with _ ⟨hp, _⟩
    exact (ha (hp.1.trans hp.2)).elim

/-- At a positive strict maximizer of the actual critical ratio, the critical denominator has
no interior zero. A hypothetical interior zero would persist under a small real perturbation,
whereas the unique subcritical zero is positive and has already moved past that disk. -/
theorem critical_denominator_ne_zero_inside {k : ℕ} {a : ℝ} (ha : log 2 < a) (ha₁ : a ≤ 1)
    (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) {w : ℂ} (hw : ‖w‖ < a) :
    denominator (k + 2) (ratio k a) w ≠ 0 := by
  let C := ratio k a
  let F := denominator (k + 2) (C : ℂ)
  intro hw0
  have ha₀ : 0 < a := (log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have hc : 0 < C := by
    apply div_pos _ (tail_pos (k + 2) ha₀)
    apply sub_pos.mpr
    rw [← exp_log (by norm_num : (0 : ℝ) < 2)]
    exact exp_lt_exp.mpr ha
  let r := (‖w‖ + a) / 2
  have hwr : ‖w‖ < r := by dsimp [r]; linarith
  have hra : r < a := by dsimp [r]; linarith
  obtain ⟨ε, εpos, axis⟩ := near_critical_axis_nonzero hmax ((norm_nonneg w).trans hwr.le) hra
  have fd : Differentiable ℂ F := denominator_differentiable _ _
  have hf : AnalyticOnNhd ℂ F univ := fun z _ ↦ fd.analyticAt z
  have hisol : ∀ᶠ z in 𝓝[≠] w, F z ≠ 0 := by
    by_contra fail
    have fzero : EqOn F 0 univ := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (mem_univ w) (by simpa only [not_not] using not_eventually.mp fail)
    have f0 := fzero (mem_univ (0 : ℂ))
    rw [show F 0 = 1 from denominator_at_zero (by omega) _] at f0
    exact one_ne_zero f0
  obtain ⟨b, bpos, isol⟩ := Metric.mem_nhdsWithin_iff.mp hisol
  let δ := min (b / 2) ((r - ‖w‖) / 2)
  have δpos : 0 < δ := lt_min (half_pos bpos) (half_pos (sub_pos.mpr hwr))
  have δb : δ < b := (min_le_left _ _).trans_lt (half_lt_self bpos)
  have δr : δ < r - ‖w‖ := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hwr))
  have fnz (z : ℂ) (hz : z ∈ sphere w δ) : F z ≠ 0 := by
    have hz' := mem_sphere.mp hz
    have hne : z ≠ w := by
      intro eq
      rw [eq, dist_self] at hz'
      exact δpos.ne' hz'.symm
    exact isol ⟨mem_ball.mpr (hz'.trans_lt δb), by simpa using hne⟩
  have slt (z : ℂ) (hz : dist z w ≤ δ) : ‖z‖ < r := by
    have h := norm_add_le (z - w) w
    rw [sub_add_cancel, ← dist_eq_norm] at h
    linarith only [h, hz, δr]
  have sne : (sphere w δ).Nonempty := by
    refine ⟨w + (δ : ℂ), ?_⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg δpos.le]
  obtain ⟨v, hv, min_v⟩ := (isCompact_sphere w δ).exists_isMinOn sne fd.continuous.norm.continuousOn
  let M := ‖F v‖
  have mpos : 0 < M := norm_pos_iff.mpr (fnz v hv)
  let η := min ε (min C (M / exp r))
  have ηpos : 0 < η := lt_min εpos (lt_min hc (div_pos mpos (exp_pos _)))
  have ηε : η ≤ ε := min_le_left _ _
  have ηC : η ≤ C := (min_le_right _ _).trans (min_le_left _ _)
  have ηM : η ≤ M / exp r := (min_le_right _ _).trans (min_le_right _ _)
  let s := C - η / 2
  have sp : 0 < s := by dsimp [s]; linarith only [ηpos, ηC]
  have hs : |s| < C := by rw [abs_of_pos sp]; dsimp [s]; linarith only [ηpos]
  have hsc : |s - C| = η / 2 := by
    rw [show s - C = -(η / 2) by dsimp [s]; ring, abs_neg, abs_of_pos (half_pos ηpos)]
  have hεs : |s - C| < ε := by rw [hsc]; linarith only [ηpos, ηε]
  let G := denominator (k + 2) (s : ℂ)
  have gd : Differentiable ℂ G := denominator_differentiable _ _
  have dom (z : ℂ) (hz : z ∈ sphere w δ) : ‖G z - F z‖ < ‖F z‖ := by
    have heq : G z - F z = ((s : ℂ) - (C : ℂ)) * tailComplex (k + 2) z := by
      dsimp [G, F, denominator]
      ring
    have ht : ‖tailComplex (k + 2) z‖ ≤ exp r :=
      (norm_tailComplex_le_exp _ _).trans (exp_le_exp.mpr (slt z (mem_sphere.mp hz).le).le)
    rw [heq, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hsc]
    calc
      _ ≤ (η / 2) * exp r := mul_le_mul_of_nonneg_left ht (half_pos ηpos).le
      _ < M := by
        apply (lt_div_iff₀ (exp_pos r)).mp
        exact (half_lt_self ηpos).trans_le ηM
      _ ≤ ‖F z‖ := min_v hz
  obtain ⟨z, hz, z0⟩ := ThreePole.exists_zero_of_boundary_dominance δpos gd fd hw0 dom
  obtain ⟨x, hx, _, _, uniq⟩ := subcritical_one_positive_pole (by omega : 1 ≤ k + 2) ha ha₁
    (contact_eq k ha₀) hs
  have hzr : ‖z‖ < r := slt z (mem_ball.mp hz).le
  have eq := uniq z (hzr.trans hra).le z0
  have hxr : x ≤ r := by
    rw [eq, Complex.norm_real, Real.norm_of_nonneg hx.1.le] at hzr
    exact hzr.le
  rw [eq] at z0
  exact axis s hεs x ⟨hx.1.le, hxr⟩ z0

/-- The critical parameter has just the tangency point as a zero on its closed critical disk. -/
theorem critical_denominator_closed_disk {k : ℕ} {a : ℝ} (ha : log 2 < a) (ha₁ : a ≤ 1)
    (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) {z : ℂ} (hz : ‖z‖ ≤ a) :
    denominator (k + 2) (ratio k a) z = 0 ↔ z = (a : ℂ) := by
  have ha₀ : 0 < a := (log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have hc : 0 ≤ ratio k a := by
    apply div_nonneg _ (tail_pos (k + 2) ha₀).le
    apply sub_nonneg.mpr
    rw [← exp_log (by norm_num : (0 : ℝ) < 2)]
    exact exp_le_exp.mpr ha.le
  have hsn : ‖(ratio k a : ℂ)‖ ≤ ratio k a := by rw [Complex.norm_real, Real.norm_of_nonneg hc]
  have hEq (z : ℂ) (hz : ‖z‖ = a) := denominator_zero_on_circle_iff ha ha₁ hz
    (contact_eq k ha₀) hsn
  constructor
  · intro h
    rcases lt_or_eq_of_le hz with hlt | heq
    · exact (critical_denominator_ne_zero_inside ha ha₁ hmax hlt h).elim
    · exact ((hEq z heq).mp h).1
  · intro heq
    subst z
    have an : ‖(a : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_of_nonneg ha₀.le]
    exact (hEq (a : ℂ) an).mpr ⟨rfl, rfl⟩

/-- A real branch of the unique positive pole can be chosen for the whole subcritical interval. -/
theorem exists_positive_pole_branch {k : ℕ} {a : ℝ} (ha : log 2 < a) (ha₁ : a ≤ 1)
    (hmax : ∀ x : ℝ, 0 < x → x ≠ a → ratio k x < ratio k a) :
    ∃ p : ℝ → ℝ, (∀ s : ℝ, |s| < ratio k a → p s ∈ Ioo 0 a ∧
      denominator (k + 2) s (p s) = 0 ∧ deriv (denominator (k + 2) s) (p s) ≠ 0 ∧
        ∀ w : ℂ, ‖w‖ ≤ a → denominator (k + 2) s w = 0 → w = (p s : ℂ)) ∧
      Tendsto p (𝓝[<] (ratio k a)) (𝓝 a) := by
  classical
  let C := ratio k a
  have ha₀ : 0 < a := (log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have hc : 0 < C := by
    apply div_pos _ (tail_pos (k + 2) ha₀)
    apply sub_pos.mpr
    rw [← exp_log (by norm_num : (0 : ℝ) < 2)]
    exact exp_lt_exp.mpr ha
  have ex (s : ℝ) (hs : |s| < C) :=
    subcritical_one_positive_pole (by omega : 1 ≤ k + 2) ha ha₁ (contact_eq k ha₀) hs
  choose p hpos hzero hsimple huniq using ex
  let p₀ := fun s : ℝ ↦ if hs : |s| < C then p s hs else a
  have all s (hs : |s| < C) : p₀ s ∈ Ioo 0 a ∧ denominator (k + 2) s (p₀ s) = 0 ∧
      deriv (denominator (k + 2) s) (p₀ s) ≠ 0 ∧
        ∀ w : ℂ, ‖w‖ ≤ a → denominator (k + 2) s w = 0 → w = (p₀ s : ℂ) := by
    simpa only [p₀, dif_pos hs] using And.intro (hpos s hs)
      (And.intro (hzero s hs) (And.intro (hsimple s hs) (huniq s hs)))
  refine ⟨p₀, all, positive_pole_tendsto_critical hmax ?_⟩
  have near : Ioo (-C) C ∈ 𝓝[<] C := Ioo_mem_nhdsLT (by linarith only [hc])
  filter_upwards [near] with s hs
  exact ⟨(all s (abs_lt.mpr hs)).1, (all s (abs_lt.mpr hs)).2.1⟩

/-- Every threshold `j=k+2≥4` has one critical tangency on the closed critical disk. -/
theorem exists_critical_closed_disk {k : ℕ} (hk : 2 ≤ k) :
    ∃ a ∈ Ioo (log 2) 1, criticalTest k a = 0 ∧ 1 < ratio k a ∧
      ∀ z : ℂ, ‖z‖ ≤ a → (denominator (k + 2) (ratio k a) z = 0 ↔ z = (a : ℂ)) := by
  obtain ⟨a, hlo, hhi, zero, cgt, hmax⟩ := strict_maximum hk
  exact ⟨a, ⟨hlo, hhi⟩, zero, cgt, fun _ hz ↦ critical_denominator_closed_disk hlo hhi.le hmax hz⟩

#print axioms near_critical_axis_nonzero
#print axioms positive_pole_tendsto_critical
#print axioms critical_denominator_ne_zero_inside
#print axioms critical_denominator_closed_disk
#print axioms exists_positive_pole_branch
#print axioms exists_critical_closed_disk

end OrderedPartitions.CriticalEdge
