import OrderedPartitions.CriticalEdgeSmallBarrier
import OrderedPartitions.TwoPoleAllSizes
import OrderedPartitions.ThreePoleAllSizes

/-! The closed critical disk is zero-free at every size for j = 2 and j = 3. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge

open Polynomial InterlacingStep Complex Set

private theorem array_complex_root {d : ℕ} {P : ℝ[X]} {x : Fin d → ℝ}
    (hx : RootArray P x) {z : ℂ} (hz : P.eval₂ ofRealHom z=0) :
    ∃ i, z=(x i:ℂ) := by
  have sp : P.Splits := splits_iff_card_roots.mpr (by simp [hx.exact.roots,hx.degree])
  have hmem : z ∈ (P.map ofRealHom).roots := by
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hx.ne_zero)).mpr
    simpa only [IsRoot.def,eval_map] using hz
  rw [sp.roots_map,hx.exact.roots,Multiset.mem_map] at hmem
  obtain ⟨r,hr,eq⟩ := hmem
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (show r ∈ List.ofFn x from hr)
  exact ⟨i, eq.symm.trans (congrArg Complex.ofReal hi.symm)⟩

theorem original_small_complex_barrier {k : ℕ} (small : k=0 ∨ k=1) :
    ∃ a ∈ Ioo (1:ℝ) 2, criticalTest k a=0 ∧ 1<ratio k a ∧
      ∀ n : ℕ, ∀ z : ℂ, (row n (k+2)).eval₂ ofRealHom z=0 →
        ∃ t : ℝ, z=(t:ℂ) ∧ t < 1-ratio k a := by
  obtain ⟨a,Ia,crit,tall,bar⟩ := original_small_critical_barrier small
  refine ⟨a,Ia,crit,tall,fun n z hz ↦ ?_⟩
  have pairs : RootTracking.OrderedPair (n/(k+2)) (row n (k+2)) (row (n+1) (k+2)) := by
    rcases small with rfl|rfl
    · exact original_threshold_two_window _ (Or.inl rfl)
    · exact ThreePole.original_all _ _ le_rfl (by decide)
  obtain ⟨xs,hx,_⟩ := pairs
  obtain ⟨i,eq⟩ := array_complex_root hx hz
  refine ⟨xs i,eq,?_⟩
  by_contra! bad
  have h := (bar (1-xs i) ⟨by linarith [hx.negative i],by linarith⟩ n).2
  rw [sub_sub_cancel,hx.zeros i] at h
  exact lt_irrefl _ h

#print axioms original_small_complex_barrier
end OrderedPartitions.CriticalEdge
