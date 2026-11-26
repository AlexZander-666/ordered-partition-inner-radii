import OrderedPartitions.CriticalEdgeTwoPoles
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Uniform location and simplicity of the two genuine poles in the moving coefficient contour. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Filter Metric Set
open scoped Topology

private theorem inverse_bound {Z : ℂ → ℂ} {a : ℝ} (a0 : 0<a)
    (an : AnalyticAt ℂ Z 0) (center : Z 0=a) (slope : deriv Z 0=a) :
    ∀ᶠ v : ℂ in 𝓝 0, ‖Z v-(a:ℂ)‖ ≤ (2*a)*‖v‖ := by
  have hd : HasDerivAt Z (a:ℂ) 0 := slope ▸ an.differentiableAt.hasDerivAt
  filter_upwards [hd.isLittleO.bound a0] with v hv
  simp only [sub_zero, center, smul_eq_mul] at hv
  have tri := norm_sub_le (Z v-(a:ℂ)-v*(a:ℂ)) (-(v*(a:ℂ)))
  rw [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_mul,Complex.norm_of_nonneg a0.le] at tri
  linarith

theorem two_pole_contour_geometry {k : ℕ} {a : ℝ} (ha : Real.log 2<a) (a1 : a≤1)
    (crit : criticalTest k a=0) (hmax : ∀ x : ℝ, 0<x → x≠a → ratio k x<ratio k a) :
    ∃ R : ℝ, a<R ∧
      (∀ z : ℂ, ‖z‖=R → generatingDen (k+2) (ratio k a) z≠0) ∧
      ∀ K : ℝ, 0<K → ∀ᶠ n : ℕ in atTop,
        let M := 2*K+1
        let rad := a/(n:ℝ)*M
        closedBall (a:ℂ) rad ⊆ ball (0:ℂ) R ∧ (0:ℂ)∉closedBall (a:ℂ) rad ∧
        ∀ u : ℂ, u≠0 → ‖u‖≤K^2 →
          let f := generatingDen (k+2) ((ratio k a:ℂ)+(edgeWidth k a:ℂ)*u/(n:ℂ)^2)
          ∃ P : Finset ℂ, P.card=2 ∧
            (∀ p∈P, p∈ball (a:ℂ) rad ∧ f p=0 ∧ deriv f p≠0) ∧
            (∀ z∈closedBall (0:ℂ) R, f z=0 → z∈P) := by
  classical
  obtain ⟨R,Z,Ra,an,center,slope,geo⟩ := actual_two_poles ha a1 crit hmax
  have a0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha
  have anorm : ‖(a:ℂ)‖=a := Complex.norm_of_nonneg a0.le
  let C : ℂ := ratio k a
  let L : ℂ := edgeWidth k a
  have z0 := geo.self_of_nhds
  refine ⟨R,Ra,?_,?_⟩
  · intro z hz bad
    have same := (z0.2.1 z hz.le).1 (by simpa using bad)
    rcases same with h|h <;> simp [center] at h <;> rw [h,anorm] at hz <;> linarith
  intro K K0
  have bound := inverse_bound a0 an center slope
  have negT : Tendsto (fun w : ℂ ↦ -w) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x:=(0:ℂ))).tendsto
  obtain ⟨e,ep,small⟩ := Metric.eventually_nhds_iff.mp (geo.and (bound.and (negT bound)))
  let M := 2*K+1
  have M0 : 0<M := by dsimp [M];linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (max (K/e) (max M (a*M/(R-a))))
  apply eventually_atTop.2
  refine ⟨N,?_⟩
  intro n hn
  have big := hN.trans_le (Nat.cast_le.mpr hn)
  obtain ⟨near,large⟩ := max_lt_iff.mp big
  obtain ⟨nM,outer⟩ := max_lt_iff.mp large
  have n0 := M0.trans nM
  let rad := a/(n:ℝ)*M
  have mult : rad*(n:ℝ)=a*M := by dsimp [rad];field_simp
  have smallR : rad<R-a := by nlinarith only [mult,(div_lt_iff₀ (sub_pos.mpr Ra)).1 outer,n0]
  have smallA : rad<a := by
    apply (lt_of_mul_lt_mul_right _ n0.le)
    rw [mult]
    exact mul_lt_mul_of_pos_left nM a0
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro z hz
    have distZ : ‖z-(a:ℂ)‖≤rad := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have tr := norm_sub_le (z-(a:ℂ)) (-(a:ℂ))
    rw [sub_neg_eq_add,sub_add_cancel,norm_neg,anorm] at tr
    simpa using (show ‖z‖<R by linarith)
  · simpa [rad,M,dist_eq_norm,abs_of_pos a0] using smallA
  intro u un uK
  obtain ⟨w,ws⟩ := IsAlgClosed.exists_pow_nat_eq (-u) (by decide : 0<2)
  have wK : ‖w‖≤K := by
    have ee := congrArg norm ws
    rw [norm_pow,norm_neg] at ee
    nlinarith [norm_nonneg w]
  let v := w/(n:ℂ)
  have vn : v≠0 := by
    apply div_ne_zero _ (by exact_mod_cast n0.ne')
    intro wz;rw [wz] at ws;simp [un] at ws
  have nv : ‖v‖=‖w‖/(n:ℝ) := by simp [v]
  have vsmall : dist v 0<e := by
    rw [dist_zero_right,nv]
    apply (div_lt_iff₀ n0).2
    exact wK.trans_lt (by linarith only [(div_lt_iff₀ ep).1 near])
  obtain ⟨g,plus,minus⟩ := small vsmall
  obtain ⟨neq,ds⟩ := g.2.2 vn
  have radius : 2*a*‖v‖<rad := by
    apply lt_of_mul_lt_mul_right _ n0.le
    rw [nv,mult,mul_assoc,div_mul_cancel₀ _ n0.ne']
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left wK a0.le]
  have marker : C+L*u/(n:ℂ)^2=C-L*v^2 := by
    rw [show u= -w^2 by rw [ws,neg_neg]]
    dsimp [v];ring
  change ∃ P : Finset ℂ, P.card=2 ∧
    (∀ p∈P, p∈ball (a:ℂ) rad ∧ generatingDen (k+2) (C+L*u/(n:ℂ)^2) p=0 ∧
      deriv (generatingDen (k+2) (C+L*u/(n:ℂ)^2)) p≠0) ∧ _
  rw [marker]
  refine ⟨{Z v,Z (-v)},by simp [neq],?_,?_⟩
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    have nR := hp.elim (fun h ↦ h ▸ g.1.1) (fun h ↦ h ▸ g.1.2)
    have zero := (g.2.1 p nR.le).2 hp
    refine ⟨?_,zero,ds p nR.le zero⟩
    rcases hp with rfl|rfl
    · simpa only [mem_ball,dist_eq_norm] using plus.trans_lt radius
    · have := minus.trans_lt (by simpa using radius : 2*a*‖-v‖<rad)
      simpa only [mem_ball,dist_eq_norm] using this
  · intro z hz zero
    have zn : ‖z‖≤R := by simpa using hz
    simpa using (g.2.1 z zn).1 zero

#print axioms two_pole_contour_geometry
end OrderedPartitions.CriticalEdge
