import OrderedPartitions.CriticalEdgeSquareCoordinate
import OrderedPartitions.CriticalEdgePoleEndpoint

/-! Global two-pole localization under a perturbation of the critical marker. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Filter Metric Set
open scoped Topology

/-- Keep all zeros in the specified open neighborhood, with an outer
disk strictly larger than the original critical disk. -/
theorem enlarge_disk {F : ℂ → ℂ → ℂ} (ct : Continuous fun w : ℂ × ℂ ↦ F w.1 w.2)
    {a : ℝ} {C : ℂ} {U : Set ℂ} (op : IsOpen U)
    (at_critical : ∀ z : ℂ, ‖z‖≤a → F C z=0 → z∈U) :
    ∃ R : ℝ, a<R ∧ ∀ᶠ s in 𝓝 C, ∀ z : ℂ, ‖z‖≤R → F s z=0 → z∈U := by
  let K := closedBall (0:ℂ) (a+1)
  have compact : IsCompact K := isCompact_closedBall _ _
  have uniform : ∀ᶠ p : (ℂ × ℝ) in 𝓝 (C,a), ∀ z∈K,
      F p.1 z≠0 ∨ z∈U ∨ p.2<‖z‖ := by
    apply compact.eventually_forall_of_forall_eventually
    intro z _
    by_cases nz : F C z≠0
    · have cont : ContinuousAt (fun w : ((ℂ × ℝ) × ℂ) ↦ F w.1.1 w.2) ((C,a),z) :=
        ct.continuousAt.comp (continuousAt_fst.fst.prodMk continuousAt_snd)
      exact (cont.eventually_ne nz).mono fun _ h ↦ Or.inl h
    by_cases inside : z∈U
    · have stay : ∀ᶠ w : ((ℂ × ℝ) × ℂ) in 𝓝 ((C,a),z), w.2 ∈ U :=
        continuous_snd.continuousAt.preimage_mem_nhds (op.mem_nhds inside)
      exact stay.mono fun _ h ↦ Or.inr (Or.inl h)
    · have gt : a<‖z‖ := lt_of_not_ge fun h ↦ inside (at_critical z h (not_ne_iff.mp nz))
      have cut : ∀ᶠ w : ((ℂ × ℝ) × ℂ) in 𝓝 ((C,a),z), w.1.2<‖w.2‖ :=
        continuousAt_fst.snd.eventually_lt continuousAt_snd.norm gt
      exact cut.mono fun _ h ↦ Or.inr (Or.inr h)
  obtain ⟨e,ep,bound⟩ := Metric.eventually_nhds_iff.mp uniform
  let δ := min (e/2) (1/2)
  have dp : 0<δ := lt_min (by positivity) (by norm_num)
  have de : δ<e := (min_le_left _ _).trans_lt (by linarith)
  have d1 : δ≤1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨a+δ,by linarith,?_⟩
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨e,ep,?_⟩
  intro s hs z hz h0
  have hdist : dist (s,a+δ) (C,a)<e := by
    rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,add_sub_cancel_left,abs_of_pos dp]
    exact ⟨hs,de⟩
  have mem : z∈K := by simpa [K] using hz.trans (show a+δ≤a+1 by linarith only [d1])
  rcases bound hdist z mem with nonzero|inside|outside
  · exact (nonzero h0).elim
  · exact inside
  · exact (not_lt_of_ge hz outside).elim

/-- A neighborhood of the collision in which every split pole is simple,
with both the center and the remote radii unscaled. -/
theorem split_zero_simple {k : ℕ} {a : ℝ} (ha : 0<a) (crit : criticalTest k a=0) :
    ∀ᶠ z : ℂ in 𝓝 (a:ℂ), ∀ v : ℂ, v≠0 →
      let f := generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2)
      f z=0 → deriv f z≠0 := by
  let W := poleCoordinate (k+2) (a:ℂ) (ratio k a) (edgeWidth k a)
  let B := fun z : ℂ ↦ (edgeWidth k a:ℂ)*CriticalEdgeCircle.tailComplex (k+2) z
  have Ban (z : ℂ) : AnalyticAt ℂ B z := by dsimp [B]; unfold CriticalEdgeCircle.tailComplex;fun_prop
  obtain ⟨_,Wa,wd,fac⟩ := poleCoordinate_factor_data ha crit
  obtain ⟨_,_,_,roots⟩ := poleCoordinate_data ha crit
  have wn : deriv W (a:ℂ)≠0 := by rw [show deriv W (a:ℂ)=(a:ℂ)⁻¹ from wd]; exact inv_ne_zero (by exact_mod_cast ha.ne')
  have b0 : B a≠0 := by
    have e := (rescaled_critical ha crit 1 0)
    have p : 0 < a*((k:ℝ)+1) := by positivity
    have rhs : (a:ℂ)*((k:ℂ)+1)≠0 := by exact_mod_cast p.ne'
    have val : B a=(a:ℂ)*((k:ℂ)+1) := by simpa [rescaledDen,B] using e
    exact val.trans_ne rhs
  filter_upwards [eventually_eventually_nhds.mpr fac,Wa.eventually_analyticAt,
    Wa.deriv.continuousAt.eventually_ne wn,(Ban a).continuousAt.eventually_ne b0,roots] with z localFac Wz dn bn rz
  intro v vn
  dsimp only
  intro zero
  have wz : W z=v ∨ W z= -v := (rz v).mp zero
  have wz0 : W z≠0 := wz.elim (fun h ↦ h.trans_ne vn) (fun h ↦ h.trans_ne (neg_ne_zero.mpr vn))
  have eq : (W z)^2-v^2=0 := sub_eq_zero.mpr (sq_eq_sq_iff_eq_or_eq_neg.mpr wz)
  have germ : generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2) =ᶠ[𝓝 z]
      fun y ↦ ((W y)^2-v^2)*B y := localFac.mono fun y h ↦ h v
  rw [germ.deriv_eq]
  have Wder : HasDerivAt W (deriv W z) z := Wz.differentiableAt.hasDerivAt
  have formula := (((Wder.fun_pow 2).sub_const (v^2)).mul (Ban z).differentiableAt.hasDerivAt).deriv
  change deriv ((fun y ↦ W y ^ 2-v^2)*B) z≠0
  rw [formula]
  have dw : deriv W z≠0 := dn
  simp [eq,wz0,dw,bn]


/-- On a fixed enlarged disk the two analytic inverse branches exhaust the
genuine poles for every sufficiently small complex parameter. -/
theorem actual_two_poles {k : ℕ} {a : ℝ} (ha : Real.log 2<a) (a1 : a≤1)
    (crit : criticalTest k a=0) (hmax : ∀ x : ℝ, 0<x → x≠a → ratio k x<ratio k a) :
    ∃ (R : ℝ) (Z : ℂ → ℂ), a<R ∧ AnalyticAt ℂ Z 0 ∧ Z 0=a ∧ deriv Z 0=a ∧
      ∀ᶠ v : ℂ in 𝓝 0,
        let f := generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2)
        (‖Z v‖<R ∧ ‖Z (-v)‖<R) ∧
        (∀ z : ℂ, ‖z‖≤R → (f z=0 ↔ z=Z v ∨ z=Z (-v))) ∧
        (v≠0 → Z v≠Z (-v) ∧ ∀ z : ℂ, ‖z‖≤R → f z=0 → deriv f z≠0) := by
  let A : ℂ := a
  let W := poleCoordinate (k+2) A (ratio k a) (edgeWidth k a)
  let G := fun v : ℂ ↦ generatingDen (k+2) ((ratio k a:ℂ)-(edgeWidth k a:ℂ)*v^2)
  have pos := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans ha
  obtain ⟨Z,Za,Z0,Zd,right,left⟩ := inverse_poleCoordinate pos crit
  obtain ⟨_,_,_,roots⟩ := poleCoordinate_data pos crit
  have simpRoot := split_zero_simple pos crit
  obtain ⟨d,dp,loc⟩ := Metric.eventually_nhds_iff.mp (left.and (roots.and simpRoot))
  let U := ball A d
  have gCont : Continuous fun w : ℂ × ℂ ↦ G w.1 w.2 := by unfold G generatingDen; fun_prop
  have center : ∀ z : ℂ, ‖z‖≤a → G 0 z=0 → z∈U := by
    intro z hn hz
    have gc : CriticalEdgeCircle.denominator (k+2) (ratio k a) z=0 := by
      simpa [G,generatingDen,CriticalEdgeCircle.denominator,CriticalEdgeCircle.tailComplex] using hz
    obtain rfl := (critical_denominator_closed_disk ha a1 hmax hn).mp gc
    exact mem_ball_self dp
  obtain ⟨R,Ra,allLoc⟩ := enlarge_disk gCont isOpen_ball center
  have conv : Tendsto Z (𝓝 0) (𝓝 A) := by simpa only [Z0] using Za.continuousAt.tendsto
  have negT : Tendsto (fun v : ℂ ↦ -v) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.continuousAt (x:= (0:ℂ))).tendsto
  have reach : ∀ᶠ v in 𝓝 (0:ℂ), Z v ∈ U ∧ ‖Z v‖<R := by
    have toward : ‖A‖<R := by simpa [A,Real.norm_of_nonneg pos.le] using Ra
    have near : ∀ᶠ v in 𝓝 (0:ℂ), Z v∈U := conv (ball_mem_nhds A dp)
    exact near.and (conv.norm.eventually_lt_const toward)
  refine ⟨R,Z,Ra,Za,Z0,Zd,?_⟩
  filter_upwards [allLoc,right,negT right,reach,negT reach] with v global rv rn zv zn
  change W (Z v)=v at rv
  change W (Z (-v))= -v at rn
  dsimp only
  refine ⟨⟨zv.2,zn.2⟩,?_,?_⟩
  · intro z hn
    constructor
    · intro hz
      have h := loc (global z hn hz)
      rcases (h.2.1 v).mp hz with p | p
      · exact Or.inl (h.1.symm.trans (congrArg Z p))
      · exact Or.inr (h.1.symm.trans (congrArg Z p))
    · rintro (rfl|rfl)
      · exact ((loc zv.1).2.1 v).mpr (Or.inl rv)
      · exact ((loc zn.1).2.1 v).mpr (Or.inr rn)
  · intro nz
    refine ⟨?_,fun z hn hz ↦ (loc (global z hn hz)).2.2 v nz hz⟩
    intro equal
    have opposite : v= -v := rv.symm.trans ((congrArg W equal).trans rn)
    exact nz (by linear_combination opposite/2)

#print axioms actual_two_poles
#print axioms enlarge_disk
#print axioms split_zero_simple
end OrderedPartitions.CriticalEdge
