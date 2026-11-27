import OrderedPartitions.CriticalEdgeTwoPoles
import OrderedPartitions.FinitePoleCircle

/-! Coefficient extraction from the genuine split poles, on a fixed contour. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

/-- Activity at a fixed splitting coordinate. -/
def splitActivity (k : ℕ) (a : ℝ) (v : ℂ) : ℂ :=
  (ratio k a : ℂ) - (edgeWidth k a : ℂ) * v ^ 2

/-- The actual denominator considered as a family in the splitting coordinate. -/
def splitDen (k : ℕ) (a : ℝ) (v : ℂ) : ℂ → ℂ :=
  generatingDen (k + 2) (splitActivity k a v)

/-- Original rank coefficient at the marker cut out by the splitting coordinate. -/
def splitRow (k : ℕ) (a : ℝ) (n : ℕ) (v : ℂ) : ℂ :=
  (row n (k + 2)).eval₂ Complex.ofRealHom (1 - splitActivity k a v) / (n.factorial : ℂ)

theorem splitDen_conj (k : ℕ) (a : ℝ) (v z : ℂ) :
    splitDen k a (conj v) (conj z) = conj (splitDen k a v z) := by
  have s : splitActivity k a (conj v) = conj (splitActivity k a v) := by
    simp [splitActivity]
  exact (congrArg (fun y : ℂ ↦ generatingDen (k + 2) y (conj z)) s).trans
    (CriticalEdgeCircle.denominator_conj (k+2) (splitActivity k a v) z)

theorem splitDen_even (k : ℕ) (a : ℝ) (v : ℂ) : splitDen k a (-v) = splitDen k a v := by
  simp [splitDen, splitActivity]

theorem splitDen_diff (k : ℕ) (a : ℝ) (v : ℂ) : Differentiable ℂ (splitDen k a v) :=
  CriticalEdgeCircle.denominator_differentiable (k+2) (splitActivity k a v)

theorem splitDen_joint_continuous (k : ℕ) (a : ℝ) :
    Continuous fun x : ℂ × ℂ ↦ splitDen k a x.1 x.2 := by
  unfold splitDen splitActivity generatingDen
  fun_prop

/-- The original coefficient has an exact two-residue formula when both poles are simple
and exhaust the zeros in the fixed disk of the denominator. -/
theorem splitRow_poles {k : ℕ} {a R : ℝ} (Rp : 0 < R) {v p q : ℂ}
    (pR : ‖p‖ < R) (qR : ‖q‖ < R) (pq : p ≠ q)
    (zeros : ∀ z : ℂ, ‖z‖ ≤ R → (splitDen k a v z = 0 ↔ z = p ∨ z = q))
    (simple : ∀ z : ℂ, ‖z‖ ≤ R → splitDen k a v z = 0 → deriv (splitDen k a v) z ≠ 0)
    (n : ℕ) :
    splitRow k a n v = circleRemainder (splitDen k a v) R n -
      (deriv (splitDen k a v) p)⁻¹ / p ^ (n+1) -
      (deriv (splitDen k a v) q)⁻¹ / q ^ (n+1) := by
  classical
  let g := splitDen k a v
  let S : Finset ℂ := {p,q}
  have pz : g p = 0 := (zeros p pR.le).mpr (Or.inl rfl)
  have qz : g q = 0 := (zeros q qR.le).mpr (Or.inr rfl)
  have atZero : g 0 = 1 := CriticalEdgeCircle.denominator_at_zero (by omega) (splitActivity k a v)
  have pm : p ≠ 0 := fun hp ↦ one_ne_zero (atZero.symm.trans (hp ▸ pz))
  have qm : q ≠ 0 := fun hq ↦ one_ne_zero (atZero.symm.trans (hq ▸ qz))
  have loc (z : ℂ) (hz : z ∈ S) : ‖z‖ < R ∧ z ≠ 0 := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨pR, pm⟩
    · exact ⟨qR, qm⟩
  have root (z : ℂ) (hz : z ∈ S) : g z = 0 := by
    apply (zeros z (loc z hz).1.le).mpr
    simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hz
  have ex (z : ℂ) (hz : ‖z‖ ≤ R) (zero : g z = 0) : z ∈ S := by
    simpa only [S, Finset.mem_insert, Finset.mem_singleton] using (zeros z hz).mp zero
  have eq := FinitePoleCircle.coefficient (splitDen_diff k a v) Rp S loc root
    (fun z hz ↦ simple z (loc z hz).1.le (root z hz)) ex n
  have coefficient : FinitePoleCircle.coeff (fun z ↦ (g z)⁻¹) n = splitRow k a n v :=
    inverse_den_coeff (by omega : 1 ≤ k+2) (s := splitActivity k a v) n
  rw [coefficient] at eq
  have ins : p ∉ ({q} : Finset ℂ) := by simpa only [Finset.mem_singleton] using pq
  rw [show S = insert p {q} from rfl, Finset.sum_insert ins, Finset.sum_singleton] at eq
  linear_combination eq

/-- On a sphere free of critical zeros, a positive lower bound on the actual denominator
persists for all sufficiently small complex splitting parameters. -/
theorem splitDen_outer_margin {k : ℕ} {a R : ℝ} (Rp : 0 < R)
    (free : ∀ z : ℂ, ‖z‖ = R → splitDen k a 0 z ≠ 0) :
    ∃ b > 0, ∀ᶠ v : ℂ in 𝓝 0, ∀ z : ℂ, ‖z‖ = R → b ≤ ‖splitDen k a v z‖ := by
  have hK := isCompact_sphere (0 : ℂ) R
  have kn : (sphere (0 : ℂ) R).Nonempty := by
    refine ⟨(R : ℂ), ?_⟩
    simp [Real.norm_of_nonneg Rp.le]
  have cont := (splitDen_diff k a 0).continuous.norm
  obtain ⟨z₀, hz₀, minz⟩ := hK.exists_isMinOn kn cont.continuousOn
  have zR : ‖z₀‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz₀
  let b := ‖splitDen k a 0 z₀‖ / 2
  have bp : 0 < b := half_pos (norm_pos_iff.mpr (free z₀ zR))
  refine ⟨b, bp, ?_⟩
  have e : ∀ᶠ v : ℂ in 𝓝 0, ∀ z ∈ sphere (0 : ℂ) R, b < ‖splitDen k a v z‖ := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have b0 : b < ‖splitDen k a 0 z‖ := (half_lt_self (norm_pos_iff.mpr (free z₀ zR))).trans_le (minz hz)
    exact (splitDen_joint_continuous k a).continuousAt.norm.eventually (lt_mem_nhds b0)
  filter_upwards [e] with v hv z hz
  exact (hv z (by simpa only [mem_sphere, dist_zero_right] using hz)).le

#print axioms splitDen_conj
#print axioms splitRow_poles
#print axioms splitDen_outer_margin

end OrderedPartitions.CriticalEdge
