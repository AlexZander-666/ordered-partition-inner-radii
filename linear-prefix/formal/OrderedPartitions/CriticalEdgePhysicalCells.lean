import OrderedPartitions.CriticalEdgePhaseReadout
import OrderedPartitions.CriticalEdgePhaseRows

/-! Linear phase ranks and bounded row-gap comparisons for the true split wave. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge.SplitPhaseDisk
open Real Filter Set CriticalEdgeRank
open scoped Topology
variable {k : ℕ} {a : ℝ} (D : SplitPhaseDisk k a)

theorem eventually_phase_row :
    ∀ᶠ n : ℕ in atTop, ∀ d ≤ D.radius, PhaseRow n d (D.realPhase n) (D.realError n) := by
  have grow := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (4*(D.biasBound+1))
  have decay := (tendsto_pow_atTop_nhds_zero_of_lt_one D.rate_pos.le D.rate_lt).const_mul D.errorBound
  rw [mul_zero] at decay
  filter_upwards [grow,decay.eventually_lt_const (by norm_num : (0:ℝ)<1/16)] with n hn small
  intro d dr
  have inside {y : ℝ} (h : y∈Icc 0 d) : |y|≤D.radius := by rw [abs_of_nonneg h.1]; exact h.2.trans dr
  refine ⟨D.realPhase_zero n,fun y h ↦ (D.phase_diff n (inside h)).differentiableAt,?_,
    fun y h ↦ (D.error_diff n (inside h)).differentiableAt,?_,?_⟩
  · intro y h
    have lo := (D.phase_axis_derivative_bounds n (inside h)).1
    exact max_le (by linarith [D.biasBound_pos]) (by linarith)
  · intro y h
    have e := (D.error_axis_bounds n (inside h)).1
    rw [abs_of_nonneg h.1] at e
    nlinarith only [e,mul_le_mul_of_nonneg_right small.le h.1]
  · intro y h
    linarith only [(D.error_axis_bounds n (inside h)).2,show
      (2*D.errorBound)*D.rate^n=2*(D.errorBound*D.rate^n) by ring,small]

theorem leading_size {d y : ℝ} (dr : d≤D.radius) (hy : y∈Icc 0 d) :
    (3/4)*y ≤ D.realLeadingPhase y ∧ D.realLeadingPhase y ≤ (5/4)*y := by
  let I := Icc (0:ℝ) d
  have inside {z : ℝ} (h : z∈I) : |z|≤D.radius := by rw [abs_of_nonneg h.1]; exact h.2.trans dr
  have diff (z : ℝ) (hz : z∈I) : DifferentiableAt ℝ D.realLeadingPhase z := by
    have funEq : D.realLeadingPhase = fun t ↦ D.realPhase 1 t - D.realPhase 0 t := by
      funext t
      have h := D.phase_increment 0 1 t
      simp only [zero_add,Nat.cast_one,one_mul] at h
      linarith
    rw [funEq]
    exact (D.phase_diff 1 (inside hz)).differentiableAt.fun_sub (D.phase_diff 0 (inside hz)).differentiableAt
  have ct : ContinuousOn D.realLeadingPhase I := fun z h ↦ (diff z h).continuousAt.continuousWithinAt
  have dt : DifferentiableOn ℝ D.realLeadingPhase (interior I) :=
    fun z h ↦ (diff z (interior_subset h)).differentiableWithinAt
  have org := left_mem_Icc.mpr (hy.1.trans hy.2)
  have lo := (convex_Icc 0 d).mul_sub_le_image_sub_of_le_deriv ct dt
    (fun z h ↦ (D.leading_derivative_bounds (inside (interior_subset h))).1) 0 org y hy hy.1
  have hi := (convex_Icc 0 d).image_sub_le_mul_sub_of_deriv_le ct dt
    (fun z h ↦ (D.leading_derivative_bounds (inside (interior_subset h))).2) 0 org y hy hy.1
  simpa only [D.realLeadingPhase_zero,sub_zero] using And.intro lo hi

theorem physical_cell_interlace {d : ℝ} (dr : d≤D.radius) (d1 : d≤1)
    {n h i : ℕ} (hp : 1≤h) (short : (h:ℝ)*d≤1)
    (R : PhaseRow n d (D.realPhase n) (D.realError n))
    (S : PhaseRow (n+h) d (D.realPhase (n+h)) (D.realError (n+h)))
    {x y z : ℝ} (hx : x∈Ioo 0 d) (hy : y∈Ioo 0 d) (hz : z∈Ioo 0 d)
    (old : InPhaseCell (D.realPhase n) (D.realError n) i y)
    (next : InPhaseCell (D.realPhase (n+h)) (D.realError (n+h)) i x)
    (after : InPhaseCell (D.realPhase (n+h)) (D.realError (n+h)) (i+1) z) :
    x<y ∧ y<z := by
  have hc : (1:ℝ)≤h := by exact_mod_cast hp
  have ym := Ioo_subset_Icc_self hy
  obtain ⟨lo,hi⟩ := D.leading_size dr ym
  have inc := D.phase_increment n h y
  have up := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg h (α:=ℝ))
  have low := mul_le_mul_of_nonneg_right hc (show 0≤D.realLeadingPhase y by linarith [hy.1])
  have ymax := mul_le_mul_of_nonneg_left hy.2.le (Nat.cast_nonneg h (α:=ℝ))
  apply interlace_relative_cells hy.1 hx.2.le hy.2.le hz.2.le d1
    (fun _ u _ v ord ↦ S.unit_increment u v ord) hx.1.le hz.1.le (R.cell_error ym old)
    (S.cell_error (Ioo_subset_Icc_self hx) next)
  · simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using S.cell_error (Ioo_subset_Icc_self hz) after
  · linarith only [inc,lo,low,hy.1]
  · nlinarith only [inc,up,ymax,short,pi_gt_three]

#print axioms eventually_phase_row
#print axioms leading_size
#print axioms physical_cell_interlace
end OrderedPartitions.CriticalEdge.SplitPhaseDisk
