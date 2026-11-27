import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Localization of every near-minimal complex root and comparison of neighboring
phase indices. The analytic estimates supplying these inputs are separate. -/
namespace OrderedPartitions.CriticalEdgeRank
open Complex

/-- The two relevant disks are internally tangent at the negative real point. -/
theorem tangent_identity (r : ℝ) (z : ℂ) :
    ‖z + (r:ℂ)‖ ^ 2 =
      (1+r)*‖z‖^2 + r*(1+r) - r*‖1-z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

theorem tangent_bound {r e : ℝ} {z : ℂ} (hr : 0 ≤ r) (he : 0 ≤ e) (h1 : e ≤ 1)
    (outer : ‖z‖ ≤ r+e) (inner : 1+r-e ≤ ‖1-z‖) :
    ‖z+(r:ℂ)‖^2 ≤ (1+r)*(4*r+1)*e := by
  have ho : ‖z‖^2 ≤ (r+e)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg z) outer 2
  have hi : (1+r-e)^2 ≤ ‖1-z‖^2 := by
    have hpos : 0 ≤ ‖1-z‖+(1+r-e) := by linarith [norm_nonneg (1-z)]
    nlinarith [mul_nonneg (sub_nonneg.mpr inner) hpos]
  rw [tangent_identity]
  have h := mul_le_mul_of_nonneg_left ho (show 0 ≤ 1+r by linarith)
  have h' := mul_le_mul_of_nonneg_left hi hr
  nlinarith [mul_nonneg he (sub_nonneg.mpr h1), mul_nonneg hr he]

/-- A lower estimate on all translated root distances localizes every root
of almost minimal modulus in the same small neighborhood. -/
theorem localize_family {r : ℝ} (hr : 0 ≤ r) (root : ℕ → ℂ → Prop)
    (lower : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ∀ z, root n z → 1+r-e ≤ ‖1-z‖)
    {radius : ℝ} (positive : 0 < radius) :
    ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z, root n z → ‖z‖ ≤ r+e → ‖z+(r:ℂ)‖ < radius := by
  let M := (1+r)*(4*r+1)
  have hp : 0 < M := by dsimp [M]; positivity
  let e := min 1 (radius^2/(2*M))
  have ep : 0 < e := lt_min (by norm_num) (by positivity)
  obtain ⟨N,hN⟩ := lower e ep
  refine ⟨e,ep,N,?_⟩
  intro n hn z hz ho
  have bound := tangent_bound hr ep.le (min_le_left _ _) ho (hN n hn z hz)
  have le : e*(2*M) ≤ radius^2 := (le_div_iff₀ (by positivity : 0 < 2*M)).mp (min_le_right _ _)
  change ‖z+(r:ℂ)‖^2 ≤ M*e at bound
  nlinarith [sq_pos_of_pos positive, norm_nonneg (z+(r:ℂ))]

/-- Two rows with common bounded phase error preserve strict order when the
phase displacement lies between the two accumulated errors and one period. -/
theorem ordered_phase_gap {φ : ℝ → ℝ} (mono : StrictMono φ)
    {a b c y step period err : ℝ}
    (left : |φ a-y| ≤ err) (mid : |φ b-(y+step)| ≤ err)
    (right : |φ c-(y+period)| ≤ err)
    (lo : 2*err < step) (hi : step+2*err < period) : a<b ∧ b<c := by
  obtain ⟨l₁,l₂⟩ := abs_le.mp left
  obtain ⟨m₁,m₂⟩ := abs_le.mp mid
  obtain ⟨r₁,r₂⟩ := abs_le.mp right
  exact ⟨mono.lt_iff_lt.mp (by linarith), mono.lt_iff_lt.mp (by linarith)⟩

#print axioms tangent_identity
#print axioms tangent_bound
#print axioms localize_family
#print axioms ordered_phase_gap
end OrderedPartitions.CriticalEdgeRank
