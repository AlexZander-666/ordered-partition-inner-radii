import OrderedPartitions.CriticalEdgeInnerLimit

/-! Real roots of the original row from sign changes of the entire inner-edge limit. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Complex Filter Set Metric
open scoped Topology

private def realMarker (k n : ℕ) (a u : ℝ) :=
  1 - (ratio k a + edgeWidth k a * u * ((n : ℝ)⁻¹)^2)

private theorem realRow_re (k n : ℕ) (a u : ℝ) :
    (normalizedInnerRow k a n u).re =
      (a^n * (a*((k:ℝ)+1)) * (n:ℝ)⁻¹ / (n.factorial:ℝ)) *
      (row n (k+2)).eval (realMarker k n a u) := by
  have hm : 1 - edgeActivity k a n (u:ℂ) = (realMarker k n a u : ℝ) := by
    unfold realMarker edgeActivity
    push_cast
    rfl
  have ev := Polynomial.eval₂_at_apply (p := row n (k+2)) Complex.ofRealHom (realMarker k n a u)
  rw [normalizedInnerRow, hm, show (row n (k+2)).eval₂ Complex.ofRealHom (realMarker k n a u : ℂ) =
    (((row n (k+2)).eval (realMarker k n a u) : ℝ) : ℂ) from ev]
  unfold edgeCoefficientScale
  have eq : (a:ℂ)^n * ((a:ℂ)*((k:ℂ)+1)) * (n:ℂ)⁻¹ *
      ((((row n (k+2)).eval (realMarker k n a u) : ℝ) : ℂ) / (n.factorial:ℂ)) =
      (((a^n * (a*((k:ℝ)+1)) * (n:ℝ)⁻¹ / (n.factorial:ℝ)) *
      (row n (k+2)).eval (realMarker k n a u) : ℝ) : ℂ) := by push_cast; ring
  exact congrArg Complex.re eq

/-- For every sign change of sinc between two positive real phases, eventually the original
ordered row has a real zero strictly between the corresponding quadratic-scale markers. -/
theorem eventual_real_witness_of_isolation {k : ℕ} {a x y : ℝ} (ap : 0 < a)
    (hz : criticalTest k a = 0) (isolated : ∀ z : ℂ, ‖z‖≤a → generatingDen (k+2) (ratio k a) z=0 → z=(a:ℂ))
    (xp : 0 < x) (xy : x < y) (signs : Real.sin x * Real.sin y < 0) :
    ∀ᶠ n : ℕ in atTop, ∃ u ∈ Ioo (x^2) (y^2),
      (row n (k+2)).eval (1-(ratio k a + edgeWidth k a * u * ((n:ℝ)⁻¹)^2)) = 0 := by
  have yp := xp.trans xy
  have xys : x^2 < y^2 := by nlinarith
  have conv (v : ℝ) (vp : 0 < v) :
      Tendsto (fun n : ℕ ↦ (normalizedInnerRow k a n ((v^2:ℝ):ℂ)).re) atTop
        (𝓝 (Real.sin v/v)) := by
    have hv : ((v^2:ℝ):ℂ) ∈ closedBall (0:ℂ) (v^2) := by
      simp [mem_closedBall, Complex.norm_real, Real.norm_eq_abs]
    have lim := (normalizedInnerRow_tendsto_sinc_of_isolation ap hz isolated vp).tendsto_at hv
    have vne : (v:ℂ) ≠ 0 := by exact_mod_cast vp.ne'
    have val : (innerSinc ((v^2:ℝ):ℂ)).re = Real.sin v/v := by
      rw [Complex.ofReal_pow, innerSinc_square vne, ← Complex.ofReal_sin, ← Complex.ofReal_div]
      rfl
    simpa only [Function.comp_def, val] using (Complex.continuous_re.continuousAt.tendsto.comp lim)
  have limprod := (conv x xp).mul (conv y yp)
  have lt : (Real.sin x/x)*(Real.sin y/y)<0 := by
    rw [div_mul_div_comm]
    exact div_neg_of_neg_of_pos signs (mul_pos xp yp)
  filter_upwards [limprod.eventually (gt_mem_nhds lt), eventually_ne_atTop 0] with n ss hn
  let f : ℝ → ℝ := fun u ↦ (row n (k+2)).eval (realMarker k n a u)
  have cont : Continuous f := by unfold f realMarker; fun_prop
  have neg : f (x^2) * f (y^2) < 0 := by
    change (normalizedInnerRow k a n _).re * (normalizedInnerRow k a n _).re < 0 at ss
    rw [realRow_re, realRow_re] at ss
    have p : 0 < a^n*(a*((k:ℝ)+1))*(n:ℝ)⁻¹/(n.factorial:ℝ) := by positivity
    dsimp only [f]
    by_contra! bad
    nlinarith only [ss, mul_nonneg (mul_nonneg p.le p.le) bad]
  obtain ⟨u, hu, zero⟩ : ∃ u ∈ Icc (x^2) (y^2), f u = 0 := by
    rcases mul_neg_iff.mp neg with h | h
    · exact intermediate_value_Icc' xys.le cont.continuousOn ⟨h.2.le,h.1.le⟩
    · exact intermediate_value_Icc xys.le cont.continuousOn ⟨h.1.le,h.2.le⟩
  have ulo : x^2 ≠ u := by rintro rfl; simp [zero] at neg
  have uhi : u ≠ y^2 := by rintro rfl; simp [zero] at neg
  exact ⟨u, ⟨lt_of_le_of_ne hu.1 ulo, lt_of_le_of_ne hu.2 uhi⟩, zero⟩

theorem eventual_real_witness {k : ℕ} {a x y : ℝ} (ha : Real.log 2 < a) (ha₁ : a ≤ 1)
    (hz : criticalTest k a = 0) (hmax : ∀ z : ℝ, 0 < z → z ≠ a → ratio k z < ratio k a)
    (xp : 0 < x) (xy : x < y) (signs : Real.sin x * Real.sin y < 0) :
    ∀ᶠ n : ℕ in atTop, ∃ u ∈ Ioo (x^2) (y^2),
      (row n (k+2)).eval (1-(ratio k a + edgeWidth k a * u * ((n:ℝ)⁻¹)^2)) = 0 := by
  apply eventual_real_witness_of_isolation ((Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha) hz _ xp xy signs
  intro z h1 h2
  exact (critical_denominator_closed_disk ha ha₁ hmax h1).mp h2

#print axioms eventual_real_witness
end OrderedPartitions.CriticalEdge
