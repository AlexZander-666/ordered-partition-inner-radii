import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A one-zero Rouché theorem on the closed disk. -/

noncomputable section

namespace OrderedPartitions.CriticalEdgeDisk

open Complex Metric Set
open scoped ComplexConjugate Topology

private abbrev disk : Set ℂ := closedBall 0 1
private abbrev interiorDisk : Set ℂ := ball 0 1

private def mobius (p z : ℂ) : ℂ := (z - p) / (1 - conj p * z)

private theorem denom_ne {p z : ℂ} (hp : ‖p‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj p * z ≠ 0 := by
  intro h
  have e := congrArg (fun w : ℂ ↦ ‖w‖) ((sub_eq_zero.mp h).symm)
  simp only [norm_mul, norm_conj, norm_one] at e
  have bn := mul_le_mul_of_nonneg_left hz (norm_nonneg p)
  linarith [show ‖p‖ * 1 = ‖p‖ by ring]

private theorem mobius_norm_diff (p z : ℂ) :
    ‖1 - conj p * z‖ ^ 2 - ‖z - p‖ ^ 2 = (1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

private theorem mobius_norm_one {p z : ℂ} (hp : ‖p‖ < 1) (hz : ‖z‖ = 1) :
    ‖mobius p z‖ = 1 := by
  have h := mobius_norm_diff p z
  rw [hz] at h
  have hnorm : ‖z - p‖ = ‖1 - conj p * z‖ := by
    have heq : ‖z - p‖ ^ 2 = ‖1 - conj p * z‖ ^ 2 := by nlinarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq
  rw [mobius, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr (denom_ne hp hz.le))]

private theorem mobius_norm_lt_one {p z : ℂ} (hp : ‖p‖ < 1) (hz : ‖z‖ < 1) :
    ‖mobius p z‖ < 1 := by
  have h := mobius_norm_diff p z
  have hpos (v : ℂ) (hv : ‖v‖ < 1) : 0 < (1 : ℝ) - ‖v‖ ^ 2 := by
    have hs := (sq_lt_sq₀ (norm_nonneg v) (zero_le_one : (0 : ℝ) ≤ 1)).mpr hv
    nlinarith
  have hdiff : ‖z - p‖ ^ 2 < ‖1 - conj p * z‖ ^ 2 := by
    have hpz := mul_pos (hpos p hp) (hpos z hz)
    linarith
  rw [mobius, norm_div, div_lt_one (norm_pos_iff.mpr (denom_ne hp hz.le))]
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hdiff

private theorem norm_lt_one_of_boundary {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (edge : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ < 1) {z : ℂ} (hz : z ∈ disk) : ‖f z‖ < 1 := by
  have ne : (sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp [mem_sphere_iff_norm]⟩
  obtain ⟨p, hp, hm⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn ne
    (hf.continuousOn.norm.mono sphere_subset_closedBall)
  have hreg : DiffContOnCl ℂ f interiorDisk :=
    ⟨hf.mono ball_subset_closedBall, by simpa only [closure_ball _ one_ne_zero] using hf.continuousOn⟩
  have hb := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := 1))
    hreg (C := ‖f p‖) (fun w hw ↦ hm (frontier_ball_subset_sphere hw))
    (show z ∈ closure interiorDisk by rw [closure_ball _ one_ne_zero]; exact hz)
  exact hb.trans_lt (edge p hp)

private theorem exists_fixed {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (hm : ∀ z ∈ disk, ‖f z‖ < 1) : ∃ z ∈ interiorDisk, f z = z := by
  by_contra! none
  have hne (z : ℂ) (hz : z ∈ disk) : z - f z ≠ 0 := by
    intro eq
    have he := (sub_eq_zero.mp eq).symm
    have hi := hm z hz
    rw [he] at hi
    exact none z (by simpa [mem_ball_iff_norm] using hi) he
  let G := fun z : ℂ ↦ Complex.exp (-(z / (z - f z)))
  have hG : DifferentiableOn ℂ G disk :=
    Complex.differentiable_exp.comp_differentiableOn
      (differentiableOn_id.div (differentiableOn_id.sub hf) hne).neg
  have edge (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) : ‖G z‖ < 1 := by
    have hb := sphere_subset_closedBall hz
    have hnorm : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
    have hlt : ‖(z - f z) - z‖ < ‖z‖ := by
      simpa [sub_sub_cancel_left, norm_neg, hnorm] using hm z hb
    have hsq := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hlt
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub] at hsq
    have hreal : 0 < (z / (z - f z)).re := by
      rw [Complex.div_re, ← add_div]
      apply div_pos _ (Complex.normSq_pos.mpr (hne z hb))
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hsq
      linarith [Complex.normSq_nonneg (z - f z)]
    simp only [G, Complex.norm_exp, Complex.neg_re]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hreal)
  have hzero := norm_lt_one_of_boundary hG edge (mem_closedBall_self zero_le_one)
  simp [G] at hzero

private theorem unique_fixed {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (hm : ∀ z ∈ disk, ‖f z‖ < 1) {p : ℂ} (hp : p ∈ interiorDisk) (hpfix : f p = p) :
    (∀ z ∈ disk, f z = z → z = p) ∧ deriv f p ≠ 1 := by
  have hpn : ‖p‖ < 1 := by simpa [mem_ball_iff_norm] using hp
  let G := fun z : ℂ ↦ mobius p (f z)
  have hG : DifferentiableOn ℂ G disk := by
    apply (hf.sub_const p).div ((differentiableOn_const (c := (1 : ℂ))).sub (hf.const_mul (conj p)))
    exact fun z hz ↦ denom_ne hpn (hm z hz).le
  have hGp : G p = 0 := by simp [G, hpfix, mobius]
  let Q := fun z : ℂ ↦ (1 - conj p * z) * dslope G p z
  have hnear : disk ∈ nhds p :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hp) ball_subset_closedBall
  have hQ : DifferentiableOn ℂ Q disk :=
    ((differentiableOn_const (c := (1 : ℂ))).sub (differentiableOn_id.const_mul (conj p))).mul
      ((differentiableOn_dslope hnear).mpr hG)
  have Qmul (z : ℂ) (hz : ‖z‖ ≤ 1) : mobius p z * Q z = G z := by
    have h := sub_smul_dslope G p z
    rw [hGp, sub_zero, smul_eq_mul] at h
    unfold mobius Q
    calc
      _ = (z - p) * dslope G p z := by rw [← mul_assoc, div_mul_cancel₀ _ (denom_ne hpn hz)]
      _ = G z := h
  have edge (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) : ‖Q z‖ < 1 := by
    have hzn : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
    have h := congrArg (fun w : ℂ ↦ ‖w‖) (Qmul z hzn.le)
    rw [norm_mul, mobius_norm_one hpn hzn, one_mul] at h
    exact h.trans_lt (mobius_norm_lt_one hpn (hm z (sphere_subset_closedBall hz)))
  have qb := fun z hz ↦ norm_lt_one_of_boundary hQ edge (z := z) hz
  constructor
  · intro z hz fz
    by_contra hzp
    have hzn : ‖z‖ ≤ 1 := by simpa [mem_closedBall_iff_norm] using hz
    have h := Qmul z hzn
    change mobius p z * Q z = mobius p (f z) at h
    rw [fz] at h
    have hn : mobius p z ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzp) (denom_ne hpn hzn)
    have q1 : Q z = 1 := mul_left_cancel₀ hn (by simpa only [mul_one] using h)
    have u := qb z hz
    rw [q1, norm_one] at u
    exact (lt_irrefl _ u)
  · intro one
    have dn := denom_ne hpn hpn.le
    have hfp := (hf p (ball_subset_closedBall hp)).differentiableAt hnear
    have hderiv : HasDerivAt G (1 / (1 - conj p * p)) p := by
      have h := (hfp.hasDerivAt.sub_const p).div
        ((hasDerivAt_const p (1 : ℂ)).sub (hfp.hasDerivAt.const_mul (conj p)))
        (show 1 - conj p * f p ≠ 0 by rwa [hpfix])
      change HasDerivAt G ((deriv f p * (1 - conj p * f p) -
        (f p - p) * (0 - conj p * deriv f p)) / (1 - conj p * f p) ^ 2) p at h
      rw [hpfix, one, sub_self, zero_mul, sub_zero, one_mul, sq, div_mul_eq_div_div,
        div_self dn] at h
      exact h
    have q1 : Q p = 1 := by
      simp only [Q, dslope_same, hderiv.deriv, one_div, mul_inv_cancel₀ dn]
    have u := qb p (ball_subset_closedBall hp)
    rw [q1, norm_one] at u
    exact (lt_irrefl _ u)

/-- If the comparison function has exactly one zero on the closed unit disk and its zero is
simple and interior, strict Rouché domination gives exactly one simple interior zero. -/
theorem one_simple_zero_unit {F G : ℂ → ℂ} {p : ℂ} (hp : ‖p‖ < 1)
    (hdF : DifferentiableOn ℂ F (closedBall 0 1))
    (hdG : DifferentiableOn ℂ G (closedBall 0 1))
    (hF : ∀ z : ℂ, ‖z‖ ≤ 1 → (F z = 0 ↔ z = p)) (hFp : deriv F p ≠ 0)
    (dom : ∀ z : ℂ, ‖z‖ = 1 → ‖G z - F z‖ < ‖F z‖) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ G z = 0 ∧ deriv G z ≠ 0 ∧
      ∀ w : ℂ, ‖w‖ ≤ 1 → G w = 0 → w = z := by
  have hball : p ∈ interiorDisk := by simpa [mem_ball_iff_norm] using hp
  have hnear : disk ∈ nhds p :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hball) ball_subset_closedBall
  have fp0 := (hF p hp.le).mpr rfl
  let P := fun z : ℂ ↦ (1 - conj p * z) * dslope F p z
  have hPd : DifferentiableOn ℂ P disk :=
    ((differentiableOn_const (c := (1 : ℂ))).sub (differentiableOn_id.const_mul (conj p))).mul
      ((differentiableOn_dslope hnear).mpr hdF)
  have hP (z : ℂ) (hz : ‖z‖ ≤ 1) : F z = mobius p z * P z := by
    have hs := sub_smul_dslope F p z
    rw [fp0, sub_zero, smul_eq_mul] at hs
    dsimp only [mobius, P]
    rw [← mul_assoc, div_mul_cancel₀ _ (denom_ne hp hz), hs]
  have P_ne (z : ℂ) (hz : ‖z‖ ≤ 1) : P z ≠ 0 := by
    by_cases e : z = p
    · subst z
      exact mul_ne_zero (denom_ne hp hp.le) (by simpa only [dslope_same] using hFp)
    · intro zero
      have hfz : F z = 0 := by simp [hP z hz, zero]
      exact e ((hF z hz).mp hfz)
  let H := fun z : ℂ ↦ (F z - G z) / P z
  have hHd : DifferentiableOn ℂ H disk := (hdF.sub hdG).div hPd
    (fun z hz ↦ P_ne z (by simpa [mem_closedBall_iff_norm] using hz))
  have H_lt (z : ℂ) (hz : z ∈ disk) : ‖H z‖ < 1 := by
    apply norm_lt_one_of_boundary hHd _ hz
    intro w hw
    have hn : ‖w‖ = 1 := by simpa [mem_sphere_iff_norm] using hw
    have pnorm : ‖F w‖ = ‖P w‖ := by
      rw [hP w hn.le, norm_mul, mobius_norm_one hp hn, one_mul]
    dsimp only [H]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (P_ne w hn.le)), ← pnorm, norm_sub_rev]
    exact dom w hn
  let f := fun z : ℂ ↦ mobius (-p) (H z)
  have f_lt (z : ℂ) (hz : z ∈ disk) : ‖f z‖ < 1 :=
    mobius_norm_lt_one (by simpa only [norm_neg] using hp) (H_lt z hz)
  have f_d : DifferentiableOn ℂ f disk := by
    apply (hHd.sub_const (-p)).div
      ((differentiableOn_const (c := (1 : ℂ))).sub (hHd.const_mul (conj (-p))))
    exact fun z hz ↦ denom_ne (by simpa only [norm_neg] using hp) (H_lt z hz).le
  let A := fun z : ℂ ↦ (1 - conj (-p) * H z) * P z / (1 - conj p * z)
  have A_d : DifferentiableOn ℂ A disk :=
    (((differentiableOn_const (c := (1 : ℂ))).sub (hHd.const_mul (conj (-p)))).mul hPd).div
      ((differentiableOn_const (c := (1 : ℂ))).sub (differentiableOn_id.const_mul (conj p)))
      (fun z hz ↦ denom_ne hp (by simpa [mem_closedBall_iff_norm] using hz))
  have A_ne (z : ℂ) (hz : z ∈ disk) : A z ≠ 0 := by
    have hn : ‖z‖ ≤ 1 := by simpa [mem_closedBall_iff_norm] using hz
    exact div_ne_zero (mul_ne_zero
      (denom_ne (by simpa only [norm_neg] using hp) (H_lt z hz).le) (P_ne z hn)) (denom_ne hp hn)
  have fact (z : ℂ) (hz : z ∈ disk) : G z = (z - f z) * A z := by
    have hn : ‖z‖ ≤ 1 := by simpa [mem_closedBall_iff_norm] using hz
    have hmul : H z * P z = F z - G z := div_mul_cancel₀ _ (P_ne z hn)
    calc
      G z = F z - H z * P z := by rw [hmul]; ring
      _ = (mobius p z - H z) * P z := by rw [hP z hn, sub_mul]
      _ = (z - f z) * A z := by
        have d₁ := denom_ne hp hn
        have d₂ : 1 + conj p * H z ≠ 0 := by
          simpa only [map_neg, neg_mul, sub_neg_eq_add] using
            denom_ne (p := -p) (z := H z) (by simpa only [norm_neg] using hp) (H_lt z hz).le
        dsimp only [f, A, mobius]
        simp only [map_neg, neg_mul, sub_neg_eq_add]
        let L := 1 - conj p * z
        let R := 1 + conj p * H z
        let N := z - p - H z * L
        change ((z - p) / L - H z) * P z = (z - (H z + p) / R) * (R * P z / L)
        have hl : (z - p) / L - H z = N / L := by
          apply (eq_div_iff d₁).mpr
          rw [sub_mul, div_mul_cancel₀ _ d₁]
        have hr : z - (H z + p) / R = N / R := by
          apply (eq_div_iff d₂).mpr
          rw [sub_mul, div_mul_cancel₀ _ d₂]
          dsimp [N, L, R]
          ring
        rw [hl, hr]
        calc
          N / L * P z = (N * P z) / L := by ring
          _ = ((N / R * R) * P z) / L := by rw [div_mul_cancel₀ _ (show R ≠ 0 from d₂)]
          _ = _ := by ring
  obtain ⟨z, hz, fix⟩ := exists_fixed f_d f_lt
  have z_disk := ball_subset_closedBall hz
  obtain ⟨uniq, hderiv⟩ := unique_fixed f_d f_lt hz fix
  have hnear : disk ∈ nhds z :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hfact : G =ᶠ[nhds z] fun w ↦ (w - f w) * A w :=
    Filter.mem_of_superset hnear fun w hw ↦ fact w hw
  have fz_d := ((f_d z z_disk).differentiableAt hnear).hasDerivAt
  have Az_d := ((A_d z z_disk).differentiableAt hnear).hasDerivAt
  have g_deriv : deriv G z = (1 - deriv f z) * A z := by
    rw [hfact.deriv_eq]
    have he := (((hasDerivAt_id z).sub fz_d).mul Az_d).deriv
    change deriv (fun w ↦ (w - f w) * A w) z =
      (1 - deriv f z) * A z + (z - f z) * deriv A z at he
    simpa only [fix, sub_self, zero_mul, add_zero] using he
  refine ⟨z, by simpa [mem_ball_iff_norm] using hz, by simp [fact z z_disk, fix], ?_, ?_⟩
  · rw [g_deriv]
    exact mul_ne_zero (sub_ne_zero.mpr hderiv.symm) (A_ne z z_disk)
  · intro w hw wz
    have wd : w ∈ disk := by simpa [mem_closedBall_iff_norm] using hw
    have fix' := (mul_eq_zero.mp ((fact w wd).symm.trans wz)).resolve_right (A_ne w wd)
    exact uniq w wd (sub_eq_zero.mp fix').symm

/-- The simple one-zero comparison on a circle of arbitrary positive radius. -/
theorem one_simple_zero {F G : ℂ → ℂ} {a : ℝ} {p : ℂ} (ha : 0 < a) (hp : ‖p‖ < a)
    (hdF : Differentiable ℂ F) (hdG : Differentiable ℂ G)
    (hF : ∀ z : ℂ, ‖z‖ ≤ a → (F z = 0 ↔ z = p)) (hFp : deriv F p ≠ 0)
    (dom : ∀ z : ℂ, ‖z‖ = a → ‖G z - F z‖ < ‖F z‖) :
    ∃ z : ℂ, ‖z‖ < a ∧ G z = 0 ∧ deriv G z ≠ 0 ∧
      ∀ w : ℂ, ‖w‖ ≤ a → G w = 0 → w = z := by
  let F' := fun z : ℂ ↦ F ((a : ℂ) * z)
  let G' := fun z : ℂ ↦ G ((a : ℂ) * z)
  have an : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have unscale (z : ℂ) : (a : ℂ) * (z / (a : ℂ)) = z := by
    rw [mul_comm, div_mul_cancel₀ _ an]
  have scale_norm (z : ℂ) : ‖(a : ℂ) * z‖ = a * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have div_norm (z : ℂ) : ‖z / (a : ℂ)‖ = ‖z‖ / a := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have scaled_deriv {f : ℂ → ℂ} (fd : Differentiable ℂ f) (z : ℂ) :
      deriv (fun w : ℂ ↦ f ((a : ℂ) * w)) z = deriv f ((a : ℂ) * z) * (a : ℂ) := by
    have h := (fd ((a : ℂ) * z)).hasDerivAt.comp z ((hasDerivAt_id z).const_mul (a : ℂ))
    simpa only [Function.comp_def, id_eq, mul_one] using h.deriv
  have hF' (z : ℂ) (hz : ‖z‖ ≤ 1) : F' z = 0 ↔ z = p / (a : ℂ) := by
    have hn : ‖(a : ℂ) * z‖ ≤ a := by
      rw [scale_norm]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz ha.le
    change F ((a : ℂ) * z) = 0 ↔ _
    rw [hF _ hn]
    constructor
    · intro h
      exact mul_left_cancel₀ an (h.trans (unscale p).symm)
    · rintro rfl
      exact unscale p
  have hFp' : deriv F' (p / (a : ℂ)) ≠ 0 := by
    dsimp only [F']
    rw [scaled_deriv hdF, unscale]
    exact mul_ne_zero hFp an
  have hp' : ‖p / (a : ℂ)‖ < 1 := by rw [div_norm, div_lt_one ha]; exact hp
  have dom' (z : ℂ) (hz : ‖z‖ = 1) : ‖G' z - F' z‖ < ‖F' z‖ :=
    dom _ (by rw [scale_norm, hz, mul_one])
  have fd : Differentiable ℂ F' := hdF.comp (differentiable_id.const_mul _)
  have gd : Differentiable ℂ G' := hdG.comp (differentiable_id.const_mul _)
  obtain ⟨z, hz, gz, dg, uniq⟩ := one_simple_zero_unit hp' fd.differentiableOn
    gd.differentiableOn hF' hFp' dom'
  refine ⟨(a : ℂ) * z, ?_, gz, ?_, ?_⟩
  · rw [scale_norm]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hz ha
  · dsimp only [G'] at dg
    rw [scaled_deriv hdG] at dg
    exact (mul_ne_zero_iff.mp dg).1
  · intro w hw hg
    have hd : ‖w / (a : ℂ)‖ ≤ 1 := by rw [div_norm, div_le_one ha]; exact hw
    have w0 : G' (w / (a : ℂ)) = 0 := by simpa only [G', unscale] using hg
    rw [← uniq _ hd w0, unscale]

#print axioms one_simple_zero_unit
#print axioms one_simple_zero

end OrderedPartitions.CriticalEdgeDisk
