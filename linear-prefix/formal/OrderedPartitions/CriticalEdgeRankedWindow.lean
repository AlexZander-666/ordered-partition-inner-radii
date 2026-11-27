import OrderedPartitions.CriticalEdgePhysicalCells
import OrderedPartitions.CriticalEdgePhaseOriginal

/-! Ordering all complex roots up to the last retained rank in the original marker. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge.SplitPhaseDisk
open Filter Set CriticalEdgeRank Real
open scoped Topology
variable {k : ℕ} {a : ℝ} (D : SplitPhaseDisk k a)

private def Certified (d : ℝ) (n i : ℕ) (y : ℝ) : Prop :=
  y∈Ioo 0 d ∧ InPhaseCell (D.realPhase n) (D.realError n) i y ∧
  deriv (fun t ↦ sin (D.realPhase n t)+D.realError n t) y ≠ 0 ∧
  ∀ z ∈ Icc 0 d, InPhaseCell (D.realPhase n) (D.realError n) i z → z=y

def rankedCoord (d : ℝ) (n i : ℕ) : ℝ := Classical.epsilon (D.Certified d n i)

private theorem certified_coord {n i : ℕ} {d : ℝ} (d0 : 0≤d) (d1 : d≤1)
    (large : π≤d*(n:ℝ)) (R : PhaseRow n d (D.realPhase n) (D.realError n))
    (ip : 1≤ i) (fit : (i:ℝ)≤d*(n:ℝ)/(4*π)) : D.Certified d n i (D.rankedCoord d n i) :=
  Classical.epsilon_spec (R.linear_cells d0 d1 large ip fit)

def rankedMarker (d : ℝ) (n i : ℕ) : ℝ := axisMarker k a (D.rankedCoord d n i)

/-- The real marker at a certified coordinate is a simple negative root. -/
private theorem root_facts {n i : ℕ} {d : ℝ} (dr : d≤D.radius) (Lp : 0<edgeWidth k a)
    (tall : 1<ratio k a) (s : D.Certified d n i (D.rankedCoord d n i)) :
    D.rankedMarker d n i < 0 ∧ (row n (k+2)).eval (D.rankedMarker d n i)=0 ∧
    (row n (k+2)).derivative.eval (D.rankedMarker d n i)≠0 := by
  let y := D.rankedCoord d n i
  have yr : |y|<D.radius := by rw [abs_of_nonneg s.1.1.le]; exact s.1.2.trans_le dr
  have wave := (D.axis_wave_identity n yr.le).trans s.2.1.1
  have root := (D.wave_zero_iff_original_zero n yr.le s.1.1.ne').mp wave
  refine ⟨axisMarker_negative Lp tall _,root,D.original_simple_of_wave_simple n yr.le root ?_⟩
  have nh : ∀ᶠ t : ℝ in 𝓝 y, |t|<D.radius := continuous_abs.continuousAt.eventually (gt_mem_nhds yr)
  have eqn : D.realWave n =ᶠ[𝓝 y] fun t ↦ sin (D.realPhase n t)+D.realError n t :=
    nh.mono (fun t ht ↦ D.axis_wave_identity n ht.le)
  rw [eqn.deriv_eq]
  exact s.2.2.1

/-- Exhaustion is in the full complex plane. Every global root with modulus
at most that of the i-th root must equal one of the first i selected markers. -/
private theorem exhausted {n i : ℕ} {d b ε : ℝ} (d0 : 0<d) (d1 : d≤1)
    (br : b≤D.radius) (Lp : 0<edgeWidth k a) (tall : 1<ratio k a)
    (width : edgeWidth k a*d^2 ≤ ε)
    (rep : ∀ t : ℂ, t ∈ originalZeroSet k n → ‖t‖≤ratio k a-1+ε →
      ∃ w ∈ Ioo 0 b, t=(axisMarker k a w : ℂ) ∧ D.realWave n w=0)
    (R : PhaseRow n d (D.realPhase n) (D.realError n)) (large : π≤d*(n:ℝ))
    (ip : 1≤ i) (fit : (i:ℝ)≤d*(n:ℝ)/(4*π))
    {t : ℂ} (ht : t∈originalZeroSet k n) (small : ‖t‖≤|D.rankedMarker d n i|) :
    ∃ m : ℕ, 1≤m ∧ m≤ i ∧ t=(D.rankedMarker d n m : ℂ) := by
  let y := D.rankedCoord d n i
  have cert := D.certified_coord d0.le d1 large R ip fit
  have yi : y∈Ioo 0 d := cert.1
  have anti := axisMarker_strictAnti (k:=k) (a:=a) Lp
  have ymod : |D.rankedMarker d n i|=ratio k a-1+edgeWidth k a*y^2 := by
    change |axisMarker k a y|=_
    rw [abs_of_neg (axisMarker_negative Lp tall y)]
    unfold axisMarker
    ring
  have sq := mul_le_mul_of_nonneg_left (sq_le_sq₀ yi.1.le d0.le |>.mpr yi.2.le) Lp.le
  obtain ⟨w,wi,tw,wave⟩ := rep t ht (small.trans (by rw [ymod]; linarith))
  have le : w≤y := by
    by_contra! h
    have s := anti yi.1.le wi.1.le h
    change ‖t‖ ≤ |axisMarker k a y| at small
    rw [tw, Complex.norm_real,Real.norm_eq_abs,abs_of_neg (axisMarker_negative Lp tall w),
      abs_of_neg (axisMarker_negative Lp tall y)] at small
    change -axisMarker k a w ≤ -axisMarker k a y at small
    linarith
  have wm : w∈Icc 0 d := ⟨wi.1.le,le.trans yi.2.le⟩
  have wr : |w|≤D.radius := by rw [abs_of_nonneg wi.1.le]; exact wi.2.le.trans br
  obtain ⟨m,mp,hit⟩ := R.covers ⟨wi.1,wm.2⟩ d1 ((D.axis_wave_identity n wr).symm.trans wave)
  have mi : m≤ i := by
    by_contra! im
    exact (not_lt_of_ge le) (R.index_order (Ioo_subset_Icc_self yi) wm cert.2.1 hit im)
  have mfit : (m:ℝ)≤d*(n:ℝ)/(4*π) := (Nat.cast_le.mpr mi).trans fit
  have same := (D.certified_coord d0.le d1 large R mp mfit).2.2.2 w wm hit
  exact ⟨m,mp,mi,by rw [tw,same]; rfl⟩

/-- The first floor(c n) roots, ordered by complex modulus, and their bounded-gap interlacing. -/
def LinearPrefix (k H : ℕ) : Prop :=
  ∃ c : ℝ, 0<c ∧ ∃ T : ℕ → ℕ → ℝ, ∀ᶠ n : ℕ in atTop,
    (∀ i : ℕ, 1≤ i → i≤⌊c*(n:ℝ)⌋₊ →
      T n i<0 ∧ (row n (k+2)).eval (T n i)=0 ∧ (row n (k+2)).derivative.eval (T n i)≠0 ∧
      ∀ t ∈ originalZeroSet k n, ‖t‖≤|T n i| → ∃ m : ℕ, 1≤m ∧ m≤ i ∧ t=(T n m : ℂ)) ∧
    (∀ i j : ℕ, 1≤ i → i<j → j≤⌊c*(n:ℝ)⌋₊ → T n j < T n i) ∧
    (∀ h i : ℕ, 1≤h → h≤H → 1≤ i → i<⌊c*(n:ℝ)⌋₊ →
      T (n+h) (i+1)<T n i ∧ T n i<T (n+h) i)

include D in
theorem linear_prefix_of_infDist (H : ℕ) (ap : 0<a) (tall : 1<ratio k a)
    (lim : Tendsto (fun n ↦ Metric.infDist (1:ℂ) (originalZeroSet k n)) atTop (𝓝 (ratio k a))) :
    LinearPrefix k H := by
  let L := edgeWidth k a
  have Lp : 0<L := by dsimp [L,edgeWidth]; exact div_pos (by positivity) (tail_pos _ ap)
  let b := min D.radius (1/((H:ℝ)+1))
  have bp : 0<b := lt_min D.radius_pos (by positivity)
  have br : b≤D.radius := min_le_left .. 
  obtain ⟨ε,ep,rep⟩ := D.eventually_represent_global_roots_of_infDist bp br ap tall lim
  let d := min b (sqrt (ε/L))
  have dp : 0<d := lt_min bp (Real.sqrt_pos.2 (div_pos ep Lp))
  have db : d≤b := min_le_left ..
  have dr := db.trans br
  have hshort : d*((H:ℝ)+1)≤1 := (le_div_iff₀ (by positivity)).mp
    (db.trans (min_le_right D.radius (1/((H:ℝ)+1))))
  have d1 : d≤1 := by nlinarith only [hshort,mul_nonneg dp.le (Nat.cast_nonneg H (α:=ℝ))]
  have width : L*d^2≤ε := by
    have sq := (sq_le_sq₀ dp.le (Real.sqrt_nonneg (ε/L))).mpr (min_le_right b (sqrt (ε/L)))
    rw [Real.sq_sqrt (div_nonneg ep.le Lp.le)] at sq
    linarith only [(le_div_iff₀ Lp).mp sq]
  let c := d/(4*π)
  have cp : 0<c := div_pos dp (by positivity)
  refine ⟨c,cp,D.rankedMarker d,?_⟩
  obtain ⟨N,good⟩ := eventually_atTop.1 D.eventually_phase_row
  have huge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (π/d)
  filter_upwards [eventually_ge_atTop N,huge,rep] with n hn high localize
  have large : π≤d*(n:ℝ) := by linarith only [(div_lt_iff₀ dp).mp high]
  have fit {i m : ℕ} (nm : n≤m) (hi : i≤⌊c*(n:ℝ)⌋₊) : (i:ℝ) ≤ d*(m:ℝ)/(4*π) := by
    have floorBound := Nat.floor_le (mul_nonneg cp.le (Nat.cast_nonneg n (α:=ℝ)))
    have cmp : (i:ℝ) ≤ c*(m:ℝ) := ((Nat.cast_le.mpr hi).trans floorBound).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr nm) cp.le)
    convert cmp using 1
    dsimp [c]
    ring
  have grow {m : ℕ} (nm : n≤m) : π≤d*(m:ℝ) :=
    large.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr nm) dp.le)
  have cert {i m : ℕ} (nm : n≤m) (ip : 1≤ i) (ib : i≤⌊c*(n:ℝ)⌋₊) :=
    D.certified_coord dp.le d1 (grow nm) (good m (hn.trans nm) d dr) ip (fit nm ib)
  have anti := axisMarker_strictAnti (k:=k) (a:=a) Lp
  constructor
  · intro i ip ib
    obtain ⟨neg,zr,simple⟩ := D.root_facts dr Lp tall (cert le_rfl ip ib)
    exact ⟨neg,zr,simple,fun _ ht sm ↦ D.exhausted dp d1 br Lp tall width localize
      (good n hn d dr) large ip (fit le_rfl ib) ht sm⟩
  constructor
  · intro i j ip ij jb
    have ci := cert le_rfl ip (ij.le.trans jb)
    have cj := cert le_rfl (ip.trans ij.le) jb
    exact anti ci.1.1.le cj.1.1.le ((good n hn d dr).index_order
      (Ioo_subset_Icc_self ci.1) (Ioo_subset_Icc_self cj.1) ci.2.1 cj.2.1 ij)
  · intro h i hp hH ip ib
    have up : n≤n+h := Nat.le_add_right _ _
    have ci := cert le_rfl ip ib.le
    have cx := cert up ip ib.le
    have cz := cert up (i:=i+1) (by omega) (by omega)
    have sh : (h:ℝ)*d≤1 := by
      have hcast : (h:ℝ)≤(H:ℝ)+1 := by exact_mod_cast (show h≤H+1 by omega)
      linarith only [mul_le_mul_of_nonneg_right hcast dp.le,hshort]
    obtain ⟨xy,yz⟩ := D.physical_cell_interlace dr d1 hp sh (good n hn d dr)
      (good (n+h) (hn.trans up) d dr) cx.1 ci.1 cz.1 ci.2.1 cx.2.1 cz.2.1
    exact ⟨anti ci.1.1.le cz.1.1.le yz,anti cx.1.1.le ci.1.1.le xy⟩

#print axioms linear_prefix_of_infDist
end OrderedPartitions.CriticalEdge.SplitPhaseDisk
