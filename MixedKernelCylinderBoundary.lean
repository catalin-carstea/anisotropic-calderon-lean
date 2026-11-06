import MixedKernelUniformLowerSide
import Calderon.ReferenceRadiusScaling
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric ConformalDepth RadiusProfile
open scoped Topology

/-- Closedness of the literal selected coordinate cylinder. -/
theorem isClosed_cylinder : IsClosed cylinder := by
  change IsClosed ({y : R3 | y 0 ^ 2 + y 1 ^ 2 ≤ 1} ∩
    ({y : R3 | (-1 : ℝ) ≤ y 2} ∩ {y : R3 | y 2 ≤ 1}))
  exact (isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const))

/-- Simultaneous strictness places a point in the interior of the same cylinder. -/
theorem mem_interior_cylinder_of_strict (y : R3)
    (h0 : y 0 ^ 2 + y 1 ^ 2 < 1) (hlo : (-1 : ℝ) < y 2) (hhi : y 2 < 1) :
    y ∈ interior cylinder := by
  let V : Set R3 := {z | z 0 ^ 2 + z 1 ^ 2 < 1 ∧ (-1 : ℝ) < z 2 ∧ z 2 < 1}
  have hV : IsOpen V := by
    change IsOpen ({z : R3 | z 0 ^ 2 + z 1 ^ 2 < 1} ∩
      ({z : R3 | (-1 : ℝ) < z 2} ∩ {z : R3 | z 2 < 1}))
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      ((isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const))
  have hsub : V ⊆ cylinder := fun z hz => ⟨hz.1.le,hz.2.1.le,hz.2.2.le⟩
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hV.mem_nhds ⟨h0,hlo,hhi⟩) hsub)

/-- The genuine topological boundary lies on one of the three original faces. -/
theorem cylinder_frontier_faces (y : R3) (hy : y ∈ frontier cylinder) :
    y 0 ^ 2 + y 1 ^ 2 = 1 ∨ y 2 = -1 ∨ y 2 = 1 := by
  have hyC : y ∈ cylinder := by
    have hh := frontier_subset_closure hy
    rwa [isClosed_cylinder.closure_eq] at hh
  by_cases h0 : y 0 ^ 2 + y 1 ^ 2 = 1
  · exact Or.inl h0
  by_cases hlo : y 2 = -1
  · exact Or.inr (Or.inl hlo)
  by_cases hhi : y 2 = 1
  · exact Or.inr (Or.inr hhi)
  exact False.elim (hy.2 (mem_interior_cylinder_of_strict y
    (lt_of_le_of_ne hyC.1 h0) (lt_of_le_of_ne hyC.2.1 (Ne.symm hlo))
    (lt_of_le_of_ne hyC.2.2 hhi)))

/-- A fixed Euclidean bound for every point of the selected cylinder. -/
theorem norm_le_two_of_mem_cylinder (y : R3) (hy : y ∈ cylinder) : ‖y‖ ≤ 2 := by
  have hn : ‖y‖^2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,add_assoc]
  have hsq : y 2 ^ 2 ≤ 1 := by
    have hh := mul_nonneg (show 0 ≤ y 2 + 1 by linarith [hy.2.1])
      (show 0 ≤ 1-y 2 by linarith [hy.2.2])
    nlinarith
  have hnorm := norm_nonneg y
  nlinarith [hy.1]

/-- A boundary point is either uniformly below the separator or has positive depth. -/
theorem cylinder_frontier_lower_or_depth (y : R3) (hy : y ∈ frontier cylinder) :
    y 2 < -(1/4 : ℝ) ∨ (1/4 : ℝ) ≤ referenceCoordinateDepth y := by
  by_cases hh : y 2 < -(1/4 : ℝ)
  · exact Or.inl hh
  right
  have hheight : -(1/4 : ℝ) ≤ y 2 := le_of_not_gt hh
  rcases cylinder_frontier_faces y hy with hface | hlo | hhi
  · unfold referenceCoordinateDepth
    linarith
  · exfalso
    rw [hlo] at hheight
    norm_num at hheight
  · unfold referenceCoordinateDepth
    rw [hhi]
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]

/-- The actual exponential transformed depth is strictly increasing for positive L. -/
theorem depthPrimitive_strictMono (L s0 : ℝ) (hL : 0 < L) :
    StrictMono (depthPrimitive L s0) := by
  intro a b hab
  unfold depthPrimitive
  apply (div_lt_div_iff_of_pos_right (show 0 < 2*L by positivity)).mpr
  have he : Real.exp (-2*L*b) < Real.exp (-2*L*a) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  linarith

/-- A positive, L-dependent depth margin at the boundary threshold. -/
theorem depthPrimitive_quarter_pos (L : ℝ) (hL : 0 < L) :
    0 < depthPrimitive L (1/8) (1/4) := by
  have hh := depthPrimitive_strictMono L (1/8) hL (show (1/8 : ℝ) < 1/4 by norm_num)
  simpa only [depthPrimitive,sub_self,zero_div] using hh

/-- The literal logarithmic softplus radius has this lower bound for EVERY positive delta. -/
theorem referenceRadius_lower_of_quarter_depth (L delta Rstar : ℝ) (p : ℕ)
    (hL : 0 < L) (hd : 0 < delta) (hR : 0 ≤ Rstar) (y : R3)
    (hy : (1/4 : ℝ) ≤ referenceCoordinateDepth y) :
    Rstar * (depthPrimitive L (1/8) (1/4))^p ≤ referenceRadius delta Rstar p L y := by
  have hb := depthPrimitive_quarter_pos L hL
  have ht : depthPrimitive L (1/8) (1/4) ≤ referenceDepth L y :=
    (depthPrimitive_strictMono L (1/8) hL).monotone hy
  have hs := ht.trans (le_softplus delta (referenceDepth L y) hd)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hs p) hR

/-- One lambda ceiling, chosen before all radius and smoothing data, handles the WHOLE boundary. -/
theorem exists_uniform_cylinder_boundary_seed_dichotomy (S : KnownSideSourceData) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ L : ℝ, 0 < L → ∀ delta : ℝ, 0 < delta →
        ∀ Rstar : ℝ, 0 ≤ Rstar → ∀ p : ℕ, ∀ y ∈ frontier cylinder,
          lam • y ∈ S.W ∨
            Rstar * (depthPrimitive L (1/8) (1/4))^p ≤ referenceRadius delta Rstar p L y := by
  obtain ⟨lam0,hpos,H⟩ := exists_uniform_scaled_lower_strip S 2 (1/4) (by norm_num) (by norm_num)
  refine ⟨lam0,hpos,fun lam hlam hsmall L hL delta hd Rstar hR p y hy => ?_⟩
  rcases cylinder_frontier_lower_or_depth y hy with hlo | hdepth
  · left
    have hyC : y ∈ cylinder := by
      have hh := frontier_subset_closure hy
      rwa [isClosed_cylinder.closure_eq] at hh
    exact H lam hlam hsmall y (norm_le_two_of_mem_cylinder y hyC) hlo.le
  · right
    exact referenceRadius_lower_of_quarter_depth L delta Rstar p hL hd hR y hdepth

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
