import OrderedPartitions.CriticalEdgePhaseCoordinate

/-! Exact finite phase model and a uniform exponential error for the original row. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Set Metric
open scoped Topology ComplexConjugate

/-- The complex phase of the split residue pair. -/
def splitPhase (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  (n + 1 : ℕ) * pairedLogDiff Z v - pairedLogDiff (residueUnit k a Z) v

/-- Nonvanishing factor away from the central splitting coordinate v=0. -/
def splitScale (k : ℕ) (a : ℝ) (Z : ℂ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  v * pairedMean Z v ^ (n+1) / (2 * pairedMean (residueUnit k a Z) v)

/-- Exact outer-contour contribution in the phase normalization. -/
def splitError (k : ℕ) (a R : ℝ) (Z : ℂ → ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  splitScale k a Z n v * circleRemainder (splitDen k a v) R n

theorem splitScale_ne_zero {k n : ℕ} {a : ℝ} {Z : ℂ → ℂ} {v : ℂ} (vn : v ≠ 0) :
    splitScale k a Z n v ≠ 0 := by
  unfold splitScale
  exact div_ne_zero (mul_ne_zero vn (pow_ne_zero _ (pairedMean_ne_zero Z v)))
    (mul_ne_zero (by norm_num) (pairedMean_ne_zero _ _))

private theorem split_residue_pair (A B X Y : ℂ → ℂ) (v : ℂ) (n : ℕ)
    (hAnn : A v ≠ 0) (hBnn : B v ≠ 0) :
    let θ := (n + 1 : ℕ) * X v - Y v
    let N := A v ^ (n+1) / (2 * B v)
    N * (B v * Complex.exp (Y v) / (A v * Complex.exp (X v)) ^ (n+1)) =
        Complex.exp (-θ) / 2 ∧
      N * (B v * Complex.exp (-Y v) / (A v * Complex.exp (-X v)) ^ (n+1)) =
        Complex.exp θ / 2 := by
  dsimp only
  constructor
  · rw [mul_pow, ← Complex.exp_nat_mul,
      show -((n + 1 : ℕ) * X v - Y v) = Y v - (n + 1 : ℕ) * X v by ring, Complex.exp_sub]
    field_simp [hAnn, hBnn, Complex.exp_ne_zero]
  · rw [mul_pow, ← Complex.exp_nat_mul, Complex.exp_sub, mul_neg, Complex.exp_neg]
    field_simp [hAnn, hBnn, Complex.exp_ne_zero]
    rw [Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _)]

private theorem finite_phase_identity {k : ℕ} {a R : ℝ} {Z : ℂ → ℂ}
    (ap : 0 < a) (crit : criticalTest k a = 0) (z0 : Z 0 = (a : ℂ))
    (Rp : 0 < R) {v : ℂ} (vn : v ≠ 0) (pR : ‖Z v‖ < R) (qR : ‖Z (-v)‖ < R)
    (pq : Z v ≠ Z (-v))
    (zeros : ∀ z : ℂ, ‖z‖ ≤ R → (splitDen k a v z = 0 ↔ z = Z v ∨ z = Z (-v)))
    (simple : ∀ z : ℂ, ‖z‖ ≤ R → splitDen k a v z = 0 → deriv (splitDen k a v) z ≠ 0)
    (BZp : Z v ≠ 0) (BZn : Z (-v) ≠ 0)
    (BRp : residueUnit k a Z v ≠ 0) (BRn : residueUnit k a Z (-v) ≠ 0) (n : ℕ) :
    splitScale k a Z n v * splitRow k a n v =
      Complex.sinh (splitPhase k a Z n v) + splitError k a R Z n v := by
  let B := residueUnit k a Z
  let g := pairedMean Z
  let U := pairedMean B
  let W := pairedLogDiff Z
  let Y := pairedLogDiff B
  let θ := splitPhase k a Z n v
  let E := circleRemainder (splitDen k a v) R n
  let N := g v ^ (n+1) / (2 * U v)
  have ep := splitRow_poles Rp pR qR pq zeros simple n
  have unitp : v * (deriv (splitDen k a v) (Z v))⁻¹ = B v := by
    dsimp only [B]
    rw [residueUnit_formula ap crit z0 vn, div_eq_mul_inv]
  have unitn : v * (deriv (splitDen k a v) (Z (-v)))⁻¹ = -B (-v) := by
    dsimp only [B]
    rw [residueUnit_formula ap crit z0 (neg_ne_zero.mpr vn), splitDen_even, neg_div, neg_neg, div_eq_mul_inv]
  have expand : v * splitRow k a n v =
      v * E - B v / (Z v)^(n+1) + B (-v) / (Z (-v))^(n+1) := by
    rw [ep, mul_sub, mul_sub, ← mul_div_assoc, ← mul_div_assoc, unitp, unitn, neg_div, sub_neg_eq_add]
  obtain ⟨zP, zN⟩ := paired_specialization BZp BZn
  obtain ⟨bP,bN⟩ := paired_specialization BRp BRn
  change U v * Complex.exp (Y v) = B v at bP
  change U v * Complex.exp (-Y v) = B (-v) at bN
  obtain ⟨termP, termN⟩ := split_residue_pair g U W Y v n
    (pairedMean_ne_zero Z v) (pairedMean_ne_zero B v)
  have termP' : N * (B v / (Z v)^(n+1)) = Complex.exp (-θ) / 2 := by
    rw [← zP, ← bP]
    exact termP
  have termN' : N * (B (-v) / (Z (-v))^(n+1)) = Complex.exp θ / 2 := by
    rw [← zN, ← bN]
    exact termN
  have factor : splitScale k a Z n v = N * v := by
    unfold splitScale
    dsimp [N, g, U, B]
    ring
  rw [factor, mul_assoc, expand, mul_add, mul_sub, termP', termN', splitError, factor, mul_assoc]
  change N * (v * E) - Complex.exp (-θ) / 2 + Complex.exp θ / 2 =
    Complex.sinh θ + N * (v * E)
  rw [Complex.sinh]
  ring

theorem splitError_bound {k : ℕ} {a R G B D : ℝ} {Z : ℂ → ℂ} {v : ℂ}
    (Rp : 0 < R) (Gp : 0 < G) (Bp : 0 < B) (Dp : 0 < D)
    (gm : ‖pairedMean Z v‖ ≤ G) (um : D ≤ ‖pairedMean (residueUnit k a Z) v‖)
    (margin : ∀ z : ℂ, ‖z‖ = R → B ≤ ‖splitDen k a v z‖) (n : ℕ) :
    ‖splitError k a R Z n v‖ ≤ (G / (2 * D * B)) * ‖v‖ * (G / R) ^ n := by
  have err := norm_circleRemainder_le (g := splitDen k a v) Rp Bp margin n
  have den : 2 * D ≤ ‖(2 : ℂ) * pairedMean (residueUnit k a Z) v‖ := by
    rw [norm_mul]
    norm_num
    linarith
  unfold splitError splitScale
  rw [norm_mul, norm_div, norm_mul, norm_pow]
  have s : ‖v‖ * ‖pairedMean Z v‖^(n+1) / ‖(2 : ℂ) * pairedMean (residueUnit k a Z) v‖ ≤
      ‖v‖ * G ^ (n+1) / (2 * D) := by
    apply div_le_div₀ _ _ (by positivity) den
    · positivity
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) gm _) (norm_nonneg _)
  refine (mul_le_mul s err (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [pow_succ G n, div_pow]
  field_simp [Rp.ne', Bp.ne', Dp.ne']

set_option maxHeartbeats 450000 in
/-- Uniform phase model on a fixed complex neighborhood, based on the true denominator
and the closed critical-disk exclusion. All sizes use the same splitting coordinate. -/
theorem split_phase_model_of_isolation {k : ℕ} {a : ℝ} (ap : 0 < a)
    (crit : criticalTest k a = 0)
    (isolated : ∀ z : ℂ, ‖z‖ ≤ a → generatingDen (k+2) (ratio k a) z = 0 → z = (a : ℂ)) :
    ∃ (R : ℝ) (Z : ℂ → ℂ) (K q : ℝ),
      a < R ∧ 0 < K ∧ 0 < q ∧ q < 1 ∧
      AnalyticAt ℂ Z 0 ∧ Z 0 = (a : ℂ) ∧ deriv Z 0 = (a : ℂ) ∧
      (∀ᶠ v : ℂ in 𝓝 0, Z (conj v) = conj (Z v)) ∧
      (∀ᶠ v : ℂ in 𝓝 0, ∀ n : ℕ,
        splitScale k a Z n v * splitRow k a n v =
          Complex.sinh (splitPhase k a Z n v) + splitError k a R Z n v ∧
        ‖splitError k a R Z n v‖ ≤ K * ‖v‖ * q ^ n) := by
  obtain ⟨R,Z,Ra,za,z0,zd,geo⟩ := actual_two_poles_of_isolation ap crit isolated
  have Rp := ap.trans Ra
  have realZ : ∀ᶠ v : ℂ in 𝓝 0, Z (conj v) = conj (Z v) :=
    splitPole_conj_germ ap za z0 zd (geo.mono fun _ h ↦ ⟨h.1.1, h.2.1⟩)
  have geo0 := geo.self_of_nhds
  have fixed : ∀ z : ℂ, ‖z‖ = R → splitDen k a 0 z ≠ 0 := by
    intro z zr zero
    have r := (geo0.2.1 z (le_of_eq zr)).mp zero
    have eq : z = (a : ℂ) := by simpa only [z0, neg_zero, or_self] using r
    have bound : R = a := by rw [← zr, eq, Complex.norm_of_nonneg ap.le]
    exact Ra.ne bound.symm
  obtain ⟨B,Bp,outer⟩ := splitDen_outer_margin Rp fixed
  let G := (a+R)/2
  have aG : a < G := by dsimp [G]; linarith
  have GR : G < R := by dsimp [G]; linarith
  have Gp := ap.trans aG
  let b := (2 * ((k : ℝ) + 1))⁻¹
  have bp : 0 < b := by dsimp [b]; positivity
  let D := b / 2
  have Dp : 0 < D := half_pos bp
  let U := residueUnit k a Z
  have u0 : U 0 = (b : ℂ) := residueUnit_at_zero ap crit za z0 zd
  have ua : AnalyticAt ℂ U 0 := residueUnit_analytic ap crit za z0 zd
  have z0n : Z 0 ≠ 0 := z0.trans_ne (by exact_mod_cast ap.ne')
  have u0n : U 0 ≠ 0 := u0.trans_ne (by exact_mod_cast bp.ne')
  have zbranch : Z 0 ∈ slitPlane := by rw [z0]; exact ofReal_mem_slitPlane.mpr ap
  have ubranch : U 0 ∈ slitPlane := by rw [u0]; exact ofReal_mem_slitPlane.mpr bp
  have gm0 : ‖pairedMean Z 0‖ = a := by
    rw [pairedMean_center z0n, z0, Complex.norm_of_nonneg ap.le]
  have um0 : ‖pairedMean U 0‖ = b := by
    rw [pairedMean_center u0n, u0, Complex.norm_of_nonneg bp.le]
  have gBound : ∀ᶠ v : ℂ in 𝓝 0, ‖pairedMean Z v‖ < G :=
    (paired_analytic za zbranch).2.continuousAt.norm.eventually (gt_mem_nhds (gm0.trans_lt aG))
  have smallAtZero : D < ‖pairedMean U 0‖ := by rw [um0]; exact half_lt_self bp
  have uBound : ∀ᶠ v : ℂ in 𝓝 0, D < ‖pairedMean U v‖ :=
    (paired_analytic ua ubranch).2.continuousAt.norm.eventually (lt_mem_nhds smallAtZero)
  have negNear : Tendsto (fun v : ℂ ↦ -v) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
  have znon := za.continuousAt.eventually_ne z0n
  have unon := ua.continuousAt.eventually_ne u0n
  refine ⟨R,Z,G/(2*D*B),G/R,Ra,by positivity,by positivity,(div_lt_one Rp).mpr GR,
    za,z0,zd,realZ,?_⟩
  filter_upwards [geo, outer, gBound, uBound, znon, negNear.eventually znon, unon, negNear.eventually unon]
    with v ge ov gv uv zp zn up un
  intro n
  refine ⟨?_, splitError_bound Rp Gp Bp Dp gv.le uv.le ov n⟩
  by_cases vn : v = 0
  · simp [vn, splitScale, splitPhase, splitError]
  · obtain ⟨distinct, ds⟩ := ge.2.2 vn
    exact finite_phase_identity ap crit z0 Rp vn ge.1.1 ge.1.2 distinct ge.2.1 ds zp zn up un n

#print axioms splitScale_ne_zero
#print axioms splitError_bound
#print axioms split_phase_model_of_isolation

end OrderedPartitions.CriticalEdge
