import OrderedPartitions.CriticalEdgeExplicitGap
import OrderedPartitions.CriticalEdgeOnePole
import OrderedPartitions.CriticalEdgeOneResidue

/-! An explicit finite-size zero-free criterion for the original ordered set-partition row. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Finset Set

/-- Exact coefficient decomposition for every original row in the open subcritical parameter disk.
The pole is shared by all values of `n`. -/
theorem original_coeff_one_residue {j : ℕ} (hj : 1 ≤ j) {a C : ℝ} {s : ℂ}
    (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * (Real.exp a - ∑ m ∈ range j, a ^ m / (m.factorial : ℝ)) = Real.exp a - 2)
    (hs : ‖s‖ < C) :
    ∃ p : ℂ, ‖p‖ < a ∧ p ≠ 0 ∧ generatingDen j s p = 0 ∧
      deriv (generatingDen j s) p ≠ 0 ∧
      ∀ n : ℕ, (row n j).eval₂ Complex.ofRealHom (1 - s) / (n.factorial : ℂ) =
        circleRemainder (generatingDen j s) a n - (deriv (generatingDen j s) p)⁻¹ / p ^ (n + 1) := by
  obtain ⟨p, hp, gp, gd, only⟩ := CriticalEdgeCircle.subcritical_one_simple_pole ha ha₁ height hs
  have hp0 : p ≠ 0 := by
    intro e
    rw [e, CriticalEdgeCircle.denominator_at_zero hj] at gp
    exact one_ne_zero gp
  refine ⟨p, hp, hp0, gp, gd, fun n ↦ ?_⟩
  have ha₀ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  rw [← inverse_den_coeff hj s n]
  exact coefficient_one_pole (CriticalEdgeCircle.denominator_differentiable j s) ha₀ hp hp0 gp gd only n

/-- Radius fraction used in the finite-size criterion. -/
def subcriticalFraction (k : ℕ) (a C S : ℝ) :=
  (C - S) * tail (k + 2) a / (a * ((1 + S) * Real.exp a))

/-- The margin fraction lies strictly between zero and one throughout the subcritical range. -/
theorem subcriticalFraction_pos_lt_one {k : ℕ} {a C S : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * tail (k + 2) a = Real.exp a - 2) (hS : 0 ≤ S) (hSC : S < C) :
    0 < subcriticalFraction k a C S ∧ subcriticalFraction k a C S < 1 := by
  let M := (1 + S) * Real.exp a
  let b := (C - S) * tail (k + 2) a
  have ha₀ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have bpos : 0 < b := mul_pos (sub_pos.mpr hSC) (tail_pos (k + 2) ha₀)
  have Mpos : 0 < M := mul_pos (by linarith) (Real.exp_pos _)
  have rho : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : ‖((Real.log 2 : ℝ) : ℂ)‖ = Real.log 2 :=
    Complex.norm_real _ |>.trans (Real.norm_of_nonneg rho.le)
  have zero : generatingDen (k + 2) 0 ((Real.log 2 : ℝ) : ℂ) = 0 := by
    unfold generatingDen
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have gap := pole_gap ha ha₁ height (s := 0) (by simpa only [norm_zero] using hS)
    (hp.trans_le ha.le) (by exact_mod_cast rho.ne') zero
  rw [hp] at gap
  change 0 < b / (a * M) ∧ b / (a * M) < 1
  refine ⟨div_pos bpos (mul_pos ha₀ Mpos), (div_lt_one (mul_pos ha₀ Mpos)).mpr ?_⟩
  calc
    b ≤ M * (a - Real.log 2) := gap
    _ < M * a := mul_lt_mul_of_pos_left (sub_lt_self _ rho) Mpos
    _ = _ := mul_comm _ _

private theorem deriv_power_lt_of_gap {a b M p d : ℝ} (n : ℕ) (ha : 0 < a)
    (hM : 0 < M) (hp : 0 ≤ p) (hda : d ≤ M)
    (hpa : p ≤ a) (gap : b ≤ M * (a - p))
    (enough : (1 - b / (a * M)) ^ n < b / (a * M)) : d * p ^ (n + 1) < b * a ^ n := by
  let y := b / (a * M)
  have product : M * a * y = b := by dsimp [y]; field_simp [ha.ne', hM.ne']
  have scaled : p ≤ a * (1 - y) := by
    apply le_of_mul_le_mul_left _ hM
    have h := calc
      M * (a * (1 - y)) = M * a - M * a * y := by ring
      _ = M * a - b := by rw [product]
    rw [h]
    linarith only [gap]
  have power := (pow_le_pow_left₀ hp scaled n).trans_eq (mul_pow a (1 - y) n)
  calc
    _ = (d * p) * p ^ n := by rw [pow_succ]; ring
    _ ≤ (M * a) * (a ^ n * (1 - y) ^ n) :=
      mul_le_mul (mul_le_mul hda hpa hp hM.le) power (pow_nonneg hp _) (by positivity)
    _ = (M * a * a ^ n) * (1 - y) ^ n := by ring
    _ < (M * a * a ^ n) * y := mul_lt_mul_of_pos_left enough (by positivity)
    _ = b * a ^ n := by rw [mul_right_comm, product]

/-- The whole closed parameter disk `‖s‖ ≤ S` is zero-free in rank `n` when the explicit
geometric condition holds. The original row is evaluated at `t = 1 - s`. -/
theorem original_no_zero_of_gap {k n : ℕ} {a C S : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * tail (k + 2) a = Real.exp a - 2) (hS : 0 ≤ S) (hSC : S < C)
    (enough : (1 - subcriticalFraction k a C S) ^ n < subcriticalFraction k a C S)
    {s : ℂ} (hs : ‖s‖ ≤ S) : (row n (k + 2)).eval₂ Complex.ofRealHom (1 - s) ≠ 0 := by
  let g := generatingDen (k + 2) s
  let b := (C - S) * tail (k + 2) a
  let M := (1 + S) * Real.exp a
  have ha₀ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ha
  have Bpos := tail_pos (k + 2) ha₀
  have bpos : 0 < b := mul_pos (sub_pos.mpr hSC) Bpos
  have mpos : 0 < M := mul_pos (by linarith) (Real.exp_pos _)
  obtain ⟨p, hp, hp0, zero, simple, coeff⟩ := original_coeff_one_residue (by omega : 1 ≤ k + 2)
    ha ha₁ height (hs.trans_lt hSC)
  have edge (z : ℂ) (hz : ‖z‖ = a) : b ≤ ‖g z‖ := by
    refine (mul_le_mul_of_nonneg_right (show C - S ≤ C - ‖s‖ by linarith) Bpos.le).trans ?_
    exact CriticalEdgeCircle.norm_denominator_lower_on_circle ha.le ha₁ hz height
  have Restimate := norm_circleRemainder_le ha₀ bpos edge n
  have gderiv := norm_den_deriv_le k hp.le hs
  have gap := pole_gap ha ha₁ height hs hp.le hp0 zero
  have hnorm : 0 < ‖deriv g p‖ * ‖p‖ ^ (n + 1) :=
    mul_pos (norm_pos_iff.mpr simple) (pow_pos (norm_pos_iff.mpr hp0) _)
  have large := deriv_power_lt_of_gap n ha₀ mpos (norm_nonneg p) gderiv hp.le gap enough
  have Rlt : ‖circleRemainder g a n‖ < ‖(deriv g p)⁻¹ / p ^ (n + 1)‖ := by
    refine Restimate.trans_lt ?_
    have hEq : ‖(deriv g p)⁻¹ / p ^ (n + 1)‖ = (‖deriv g p‖ * ‖p‖ ^ (n + 1))⁻¹ := by
      rw [norm_div, norm_inv, norm_pow, div_eq_mul_inv, mul_inv_rev]
      exact mul_comm _ _
    rw [hEq, one_div]
    exact (inv_lt_inv₀ (by positivity) hnorm).mpr large
  intro h
  have eq := coeff n
  rw [h, zero_div] at eq
  have same : circleRemainder g a n = (deriv g p)⁻¹ / p ^ (n + 1) := sub_eq_zero.mp eq.symm
  exact (lt_irrefl _) (by simpa only [same] using Rlt)

/-- Parameter-disk formulation centered at the original marker `t = 1`. -/
theorem original_no_zero_in_disk {k n : ℕ} {a C S : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * tail (k + 2) a = Real.exp a - 2) (hS : 0 ≤ S) (hSC : S < C)
    (enough : (1 - subcriticalFraction k a C S) ^ n < subcriticalFraction k a C S)
    {t : ℂ} (ht : ‖1 - t‖ ≤ S) : (row n (k + 2)).eval₂ Complex.ofRealHom t ≠ 0 := by
  have h := original_no_zero_of_gap ha ha₁ height hS hSC enough ht
  simpa only [sub_sub_cancel] using h

/-- The logarithmic sufficient condition for the geometric inequality. -/
theorem geometric_condition_of_log {n : ℕ} {y : ℝ} (hy₀ : 0 < y) (hy₁ : y ≤ 1)
    (h : -Real.log y < (n : ℝ) * y) : (1 - y) ^ n < y := by
  have h₀ : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  calc
    _ ≤ Real.exp (-y) ^ n := pow_le_pow_left₀ (sub_nonneg.mpr hy₁) h₀ n
    _ = Real.exp (-((n : ℝ) * y)) := by rw [← Real.exp_nat_mul, mul_neg]
    _ < Real.exp (Real.log y) := Real.exp_lt_exp.mpr (by linarith only [h])
    _ = y := Real.exp_log hy₀

/-- The original row has no zero in the selected disk whenever `n > -log(y)/y`. -/
theorem original_no_zero_in_disk_of_log {k n : ℕ} {a C S : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * tail (k + 2) a = Real.exp a - 2) (hS : 0 ≤ S) (hSC : S < C)
    (enough : -Real.log (subcriticalFraction k a C S) < (n : ℝ) * subcriticalFraction k a C S)
    {t : ℂ} (ht : ‖1 - t‖ ≤ S) : (row n (k + 2)).eval₂ Complex.ofRealHom t ≠ 0 := by
  obtain ⟨h₀, h₁⟩ := subcriticalFraction_pos_lt_one ha ha₁ height hS hSC
  exact original_no_zero_in_disk ha ha₁ height hS hSC (geometric_condition_of_log h₀ h₁.le enough) ht

/-- Every fixed smaller parameter disk is zero-free in all sufficiently high original rows. -/
theorem eventually_original_no_zero_in_disk {k : ℕ} {a C S : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (height : C * tail (k + 2) a = Real.exp a - 2) (hS : 0 ≤ S) (hSC : S < C) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℂ, ‖1 - t‖ ≤ S → (row n (k + 2)).eval₂ Complex.ofRealHom t ≠ 0 := by
  let y := subcriticalFraction k a C S
  obtain ⟨hy₀, hy₁⟩ := subcriticalFraction_pos_lt_one ha ha₁ height hS hSC
  have converge := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr (show y ≤ 1 from hy₁.le))
    (sub_lt_self (1 : ℝ) (show 0 < y from hy₀))
  exact (converge.eventually (gt_mem_nhds hy₀)).mono fun _ enough _ ht ↦
    original_no_zero_in_disk ha ha₁ height hS hSC enough ht

/-- For each actual threshold `j=k+2≥4`, the real critical point gives the explicit disk criterion. -/
theorem original_effective_critical_disk {k : ℕ} (hk : 2 ≤ k) :
    ∃ a ∈ Ioo (Real.log 2) 1, criticalTest k a = 0 ∧ 1 < ratio k a ∧
      ∀ S ∈ Ico 0 (ratio k a),
        let y := subcriticalFraction k a (ratio k a) S
        (0 < y ∧ y < 1) ∧ ∀ n : ℕ, (1 - y) ^ n < y →
          ∀ t : ℂ, ‖1 - t‖ ≤ S → (row n (k + 2)).eval₂ Complex.ofRealHom t ≠ 0 := by
  obtain ⟨a, alo, ahi, critical, tall, _⟩ := strict_maximum hk
  have pos := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans alo
  have height : ratio k a * tail (k + 2) a = Real.exp a - 2 :=
    div_mul_cancel₀ _ (tail_pos _ pos).ne'
  refine ⟨a, ⟨alo, ahi⟩, critical, tall, fun _ hs ↦ ⟨?_, ?_⟩⟩
  · exact subcriticalFraction_pos_lt_one alo ahi.le height hs.1 hs.2
  · exact fun _ enough _ ht ↦ original_no_zero_in_disk alo ahi.le height hs.1 hs.2 enough ht

#print axioms original_coeff_one_residue
#print axioms subcriticalFraction_pos_lt_one
#print axioms original_no_zero_of_gap
#print axioms original_no_zero_in_disk
#print axioms geometric_condition_of_log
#print axioms original_no_zero_in_disk_of_log
#print axioms eventually_original_no_zero_in_disk
#print axioms original_effective_critical_disk

end OrderedPartitions.CriticalEdge
