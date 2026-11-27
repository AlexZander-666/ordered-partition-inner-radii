import OrderedPartitions.CriticalEdgeContours
import OrderedPartitions.CriticalEdgeScaling
import OrderedPartitions.CriticalEdgeOnePole

/-! Exact normalization of the two-pole moving contour for the original ordered row. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter
open scoped Topology

/-- The affine change of a circle by a real scaling factor and a translation. -/
theorem circleIntegral_affine (f : ℂ → ℂ) (c : ℂ) (x r : ℝ) :
    (∮ z in C(c, x * r), f z) = (x : ℂ) * ∮ v in C(0, r), f (c + (x : ℂ) * v) := by
  have cm (d : ℂ) (θ : ℝ) : circleMap d (x * r) θ = d + (x : ℂ) * circleMap 0 r θ := by
    simp only [circleMap, Complex.ofReal_mul, zero_add, mul_assoc]
  unfold circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [deriv_circleMap, cm, zero_add, smul_eq_mul]
  ring

/-- The normalized small parameter in the exact quadratic scaling. -/
def edgeActivity (k : ℕ) (a : ℝ) (n : ℕ) (u : ℂ) : ℂ :=
  (ratio k a : ℂ) + (edgeWidth k a : ℂ) * u * ((n : ℂ)⁻¹) ^ 2

/-- The common scaling of the coefficient and its two contour integrals. -/
def edgeCoefficientScale (k : ℕ) (a : ℝ) (n : ℕ) : ℂ :=
  (a : ℂ) ^ n * ((a : ℂ) * ((k : ℂ) + 1)) * (n : ℂ)⁻¹

/-- The original ordered row in the critical inner-edge scale. -/
def normalizedInnerRow (k : ℕ) (a : ℝ) (n : ℕ) (u : ℂ) : ℂ :=
  edgeCoefficientScale k a n *
    ((row n (k + 2)).eval₂ Complex.ofRealHom (1 - edgeActivity k a n u) / (n.factorial : ℂ))

/-- The small contour after substituting `z = a + a v/n`. -/
def scaledKernel (k : ℕ) (a : ℝ) (n : ℕ) (u v : ℂ) : ℂ :=
  ((a : ℂ) * ((k : ℂ) + 1)) *
    (((1 + (n : ℂ)⁻¹ * v) ^ (n + 1)) *
      rescaledDen (k + 2) a (ratio k a) (edgeWidth k a) u v ((n : ℂ)⁻¹))⁻¹

theorem scaled_displaced_exact {k n : ℕ} (hn : n ≠ 0) {a : ℝ} (ha : 0 < a)
    (hz : criticalTest k a = 0) (u : ℂ) (M : ℝ) :
    edgeCoefficientScale k a n * displacedRemainder (generatingDen (k + 2) (edgeActivity k a n u))
      a (a / (n : ℝ) * M) n =
        (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), scaledKernel k a n u v := by
  let h := (n : ℂ)⁻¹
  let J : ℂ := (a : ℂ) * ((k : ℂ) + 1)
  let D := generatingDen (k + 2) (edgeActivity k a n u)
  let A : ℂ := ((a : ℂ) ^ (n + 1) * h ^ 2)⁻¹
  let f := fun v : ℂ ↦ (((1 + h * v) ^ (n + 1)) *
    rescaledDen (k + 2) a (ratio k a) (edgeWidth k a) u v h)⁻¹
  have an : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hh : h ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have cast : ((a / (n : ℝ) : ℝ) : ℂ) = (a : ℂ) * h := by simp [h, div_eq_mul_inv]
  obtain ⟨d0, d1, _⟩ := cden_contact k ha hz
  have funEq (v : ℂ) :
      (((a : ℂ) + ((a / (n : ℝ) : ℝ) : ℂ) * v) ^ (n + 1) *
        D ((a : ℂ) + ((a / (n : ℝ) : ℝ) : ℂ) * v))⁻¹ = A * f v := by
    rw [cast]
    have eq : (a : ℂ) + (a : ℂ) * h * v = (a : ℂ) + h * ((a : ℂ) * v) := by ring
    rw [eq]
    have dens : D ((a : ℂ) + h * ((a : ℂ) * v)) =
        h ^ 2 * rescaledDen (k + 2) a (ratio k a) (edgeWidth k a) u v h :=
      rescaled_identity d0 d1 (edgeWidth k a) u v h
    rw [dens, show (a : ℂ) + h * ((a : ℂ) * v) = (a : ℂ) * (1 + h * v) by ring,
      mul_pow]
    simp only [A, f, mul_inv_rev]
    ring
  have scaleEq : edgeCoefficientScale k a n * ((a : ℂ) * h) * A = J := by
    change (a : ℂ) ^ n * J * h * ((a : ℂ) * h) * ((a : ℂ) ^ (n + 1) * h ^ 2)⁻¹ = J
    rw [pow_succ]; field_simp [an, hh]
  change edgeCoefficientScale k a n * displacedRemainder D a (a / (n : ℝ) * M) n =
    (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), J * f v
  unfold displacedRemainder
  rw [circleIntegral_affine, funext funEq, cast]
  simp only [circleIntegral.integral_const_mul, smul_eq_mul]
  calc
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
      (edgeCoefficientScale k a n * ((a : ℂ) * h) * A) * (∮ v in C(0, M), f v) := by ring
    _ = _ := by rw [scaleEq, mul_assoc]

/-- Exact decomposition of the scaled original row whenever the finite simple pole set lies
inside the moving circle and exhausts the denominator zeros on the outer disk. -/
theorem normalizedRow_eq_contours {k n : ℕ} (hn : n ≠ 0) {a R M : ℝ} (ha : 0 < a)
    (hR : 0 < R) (hM : 0 < M) (hz : criticalTest k a = 0) (u : ℂ)
    (inner : closedBall (a : ℂ) (a / (n : ℝ) * M) ⊆ ball (0 : ℂ) R)
    (off0 : (0 : ℂ) ∉ closedBall (a : ℂ) (a / (n : ℝ) * M)) (P : Finset ℂ)
    (pinside : ∀ p ∈ P, p ∈ ball (a : ℂ) (a / (n : ℝ) * M))
    (proot : ∀ p ∈ P, generatingDen (k + 2) (edgeActivity k a n u) p = 0)
    (psimple : ∀ p ∈ P, deriv (generatingDen (k + 2) (edgeActivity k a n u)) p ≠ 0)
    (exhaust : ∀ z ∈ closedBall (0 : ℂ) R, generatingDen (k + 2) (edgeActivity k a n u) z = 0 → z ∈ P) :
    normalizedInnerRow k a n u = edgeCoefficientScale k a n *
      circleRemainder (generatingDen (k + 2) (edgeActivity k a n u)) R n -
        (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ v in C(0, M), scaledKernel k a n u v := by
  have hg : Differentiable ℂ (generatingDen (k + 2) (edgeActivity k a n u)) :=
    CriticalEdgeCircle.denominator_differentiable (k + 2) (edgeActivity k a n u)
  have zero : generatingDen (k + 2) (edgeActivity k a n u) 0 = 1 :=
    CriticalEdgeCircle.denominator_at_zero (by omega : 1 ≤ k + 2) (edgeActivity k a n u)
  have hr : 0 < a / (n : ℝ) * M := mul_pos (div_pos ha (by exact_mod_cast Nat.pos_of_ne_zero hn)) hM
  unfold normalizedInnerRow
  rw [← inverse_den_coeff (by omega : 1 ≤ k + 2),
    coefficient_eq_sub_displaced hg (zero.trans_ne one_ne_zero) hR hr inner off0 P pinside proot psimple exhaust,
    mul_sub, scaled_displaced_exact hn ha hz]

#print axioms circleIntegral_affine
#print axioms scaled_displaced_exact
#print axioms normalizedRow_eq_contours

end OrderedPartitions.CriticalEdge
