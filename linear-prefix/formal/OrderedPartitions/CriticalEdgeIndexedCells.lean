import OrderedPartitions.CriticalEdgeMovingCells

/-! Selection, simplicity and ordering of reachable phase cells on a fixed interval. -/
noncomputable section
namespace OrderedPartitions.CriticalEdgeRank
open Real Set

/-- A full phase cell contained in the phase range on [0,d] contains exactly
one zero of the original perturbed sine, with nonzero derivative. -/
theorem indexed_sine_cell {φ e : ℝ → ℝ} {d η : ℝ} (k : ℕ) (d0 : 0≤d)
    (left : φ 0 ≤ k*π-π/4) (right : k*π+π/4 ≤ φ d) (small : η≤1/4)
    (phase : ∀ t ∈ Icc 0 d, DifferentiableAt ℝ φ t ∧ 1≤deriv φ t)
    (err : ∀ t ∈ Icc 0 d, DifferentiableAt ℝ e t ∧ |e t|≤η ∧ |deriv e t|≤1/4) :
    ∃ y ∈ Ioo 0 d, sin (φ y)+e y=0 ∧ |φ y-k*π|≤2*|e y| ∧
      deriv (fun t ↦ sin (φ t)+e t) y ≠ 0 ∧
      ∀ z ∈ Icc 0 d, |φ z-k*π|≤π/4 → sin (φ z)+e z=0 → z=y := by
  let s : ℝ := (-1)^k
  have sa : |s|=1 := by simp [s,abs_pow]
  have sn : s≠0 := by simp [s]
  have cont : ContinuousOn φ (Icc 0 d) := fun t ht ↦ (phase t ht).1.continuousAt.continuousWithinAt
  have mono := strictMonoOn_of_deriv_pos (convex_Icc 0 d) cont (fun t ht ↦
    zero_lt_one.trans_le (phase t (interior_subset ht)).2)
  obtain ⟨l,hl,lv⟩ := intermediate_value_Icc d0 cont
    (show (k:ℝ)*π-π/4∈Icc (φ 0) (φ d) from ⟨left,by linarith [pi_pos]⟩)
  obtain ⟨r,hr,rv⟩ := intermediate_value_Icc d0 cont
    (show (k:ℝ)*π+π/4∈Icc (φ 0) (φ d) from ⟨by linarith [pi_pos],right⟩)
  have lr : l<r := (mono.lt_iff_lt hl hr).mp (by rw [lv,rv]; linarith [pi_pos])
  have sub : Icc l r ⊆ Icc 0 d := Icc_subset_Icc hl.1 hr.2
  have scaled (t : ℝ) (ht : t ∈ Icc l r) :
      DifferentiableAt ℝ (fun z ↦ s*e z) t ∧ |s*e t|≤η ∧ |deriv (fun z ↦ s*e z) t|≤1/4 := by
    obtain ⟨hd,he,hde⟩ := err t (sub ht)
    refine ⟨hd.const_mul s,?_,?_⟩
    · rwa [abs_mul,sa,one_mul]
    · rwa [deriv_const_mul s hd,abs_mul,sa,one_mul]
  obtain ⟨y,hy,zero,bd,der,unique⟩ := unique_sine_cell lr lv rv small (fun t ht ↦ phase t (sub ht)) scaled
  have ident : (fun t ↦ sin (φ t-k*π)+s*e t) = fun t ↦ s*(sin (φ t)+e t) := by
    funext t; rw [sin_sub_nat_mul_pi,mul_add]
  have formula (t : ℝ) := congrFun ident t
  have zeroy := (formula y).symm.trans zero
  have ym := sub (Ioo_subset_Icc_self hy)
  refine ⟨y,⟨hl.1.trans_lt hy.1,hy.2.trans_le hr.2⟩,(mul_eq_zero.mp zeroy).resolve_left sn,?_,?_,?_⟩
  · simpa only [abs_mul,sa,one_mul] using bd
  · have hd : DifferentiableAt ℝ (fun t ↦ sin (φ t)+e t) y :=
      ((phase y ym).1.sin).fun_add (err y ym).1
    rw [ident,deriv_const_mul s hd] at der
    exact fun h ↦ by rw [h,mul_zero] at der; exact (lt_irrefl _ der)
  · intro z hz hcell hz0
    obtain ⟨low,high⟩ := abs_le.mp hcell
    exact unique z ⟨(mono.le_iff_le hl hz).mp (by rw [lv]; linarith),
        (mono.le_iff_le hz hr).mp (by rw [rv]; linarith)⟩ ((formula z).trans (by rw [hz0,mul_zero]))

#print axioms indexed_sine_cell
end OrderedPartitions.CriticalEdgeRank
