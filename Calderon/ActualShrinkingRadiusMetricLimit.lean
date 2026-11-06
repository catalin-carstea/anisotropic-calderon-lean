import Calderon.ReferenceRadiusScaling
import Calderon.CoordinateBootstrapJets
import Calderon.NormalizedPrincipalMetricSmooth
import Calderon.MixedKernelConstruction.MixedKernelCylinderBoundary
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile CoordinateBootstrapJets NormalizedPrincipalMetric

/-- The exact fixed-radius coefficient bound at every positive shrinkage
forces its nonnegative left side to vanish at nonpositive reference depth. -/
theorem eq_zero_of_le_referenceRadius_forall_delta
    (L R eps H : ℝ) (p : ℕ) (x : R3)
    (hR : 0 ≤ R) (heps : 0 ≤ eps) (hH : 0 ≤ H)
    (hp : 1 ≤ p) (hx : referenceDepth L x ≤ 0)
    (hbound : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      H ≤ eps * referenceRadius delta R p L x) : H = 0 := by
  have hlim : Tendsto (fun delta : ℝ => eps * R * (delta * Real.log 2)^p)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun delta : ℝ => eps * R * (delta * Real.log 2)^p) := by fun_prop
    have h : Tendsto (fun delta : ℝ => eps * R * (delta * Real.log 2)^p)
        (𝓝[>] (0 : ℝ)) (𝓝 (eps * R * ((0 : ℝ) * Real.log 2)^p)) :=
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa [zero_pow (by omega : p ≠ 0)] using h
  have hle : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
      H ≤ eps * R * (delta * Real.log 2)^p := by
    have hmem : Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)]
      exact self_mem_nhdsWithin
    filter_upwards [hmem] with delta hd
    have hsoft := softplus_le_delta_log_two delta (referenceDepth L x) hd.1 hx
    have hpow := pow_le_pow_left₀ (softplus_pos delta _ hd.1).le hsoft p
    exact (hbound delta hd.1 hd.2).trans (by
      unfold referenceRadius
      calc
        eps * (R * softplus delta (referenceDepth L x)^p)
            ≤ eps * (R * (delta * Real.log 2)^p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hR) heps
        _ = _ := by ring)
  exact le_antisymm (ge_of_tendsto hlim hle) hH

/-- The zeroth multiindex is part of the actual H8 sum. -/
theorem matrixField_eq_zero_of_coordinateH8_eq_zero
    (h : MatrixField) (x : R3) (hh : coordinateH8 h x = 0) : h x = 0 := by
  ext i j
  have hi := abs_component_partial_le_H8 zeroMultiIndex h x
    (by rw [multiIndexOrder_zero]; norm_num) i j
  rw [canonicalCoordinatePartial_zero, hh] at hi
  exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))

/-- Endpoint of the actual all-delta bootstrap: given the bound for every delta, the
SAME fixed matrix field vanishes on the negative-depth part of the cylinder. -/
theorem eqOn_zero_on_negative_depth_of_coordinateH8_forall_delta
    (h : MatrixField) (L R eps : ℝ) (p : ℕ)
    (hR : 0 ≤ R) (heps : 0 ≤ eps) (hp : 1 ≤ p)
    (hbound : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ cylinder,
      coordinateH8 h x ≤ eps * referenceRadius delta R p L x) :
    EqOn h (fun _ => 0) {x | x ∈ cylinder ∧ referenceDepth L x < 0} := by
  intro x hx
  apply matrixField_eq_zero_of_coordinateH8_eq_zero
  exact eq_zero_of_le_referenceRadius_forall_delta L R eps (coordinateH8 h x)
    p x hR heps (coordinateH8_nonneg h x) hp hx.2.le
    (fun delta hd hd1 => hbound delta hd hd1 x hx.1)

/-- The actual reference depth is negative on one fixed open neighborhood
of the origin, so the all-delta bootstrap gives local principal vanishing. -/
theorem exists_open_neighborhood_zero_of_coordinateH8_forall_delta
    (h : MatrixField) (L R eps : ℝ) (p : ℕ)
    (hL : 0 < L) (hR : 0 ≤ R) (heps : 0 ≤ eps) (hp : 1 ≤ p)
    (hbound : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ cylinder,
      coordinateH8 h x ≤ eps * referenceRadius delta R p L x) :
    ∃ U : Set R3, IsOpen U ∧ (0 : R3) ∈ U ∧ U ⊆ cylinder ∧ EqOn h (fun _ => 0) U := by
  let U : Set R3 := interior cylinder ∩ {x | referenceDepth L x < 0}
  have hU : IsOpen U := isOpen_interior.inter
    (isOpen_lt (contDiff_referenceDepth L).continuous continuous_const)
  have h0 : (0 : R3) ∈ U := by
    refine ⟨mem_interior_cylinder_of_strict 0 ?_ ?_ ?_, referenceDepth_zero_neg L hL⟩ <;> norm_num
  refine ⟨U,hU,h0,fun x hx => interior_subset hx.1,?_⟩
  intro x hx
  exact eqOn_zero_on_negative_depth_of_coordinateH8_forall_delta h L R eps p hR heps hp
    hbound ⟨interior_subset hx.1,hx.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
