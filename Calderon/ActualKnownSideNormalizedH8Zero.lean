import Calderon.CoordinateH8FrechetRecovery
import Calderon.ActualMixedKernelOneDensityTwoUniformBounds

set_option autoImplicit false
noncomputable section
open Set Metric Filter WithLp
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge MetricVolume ConformalDepth RadiusProfile ReferenceDensityBounds
  CoordinateBootstrapJets NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth

private theorem normalizedPrincipalDifference_smul_self_zero
    (B : Mat) (hB : B.PosDef) (c : ℝ) (hc : c ≠ 0) :
    normalizedPrincipalDifference (c • B) B = 0 := by
  have hUnit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have hMul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hUnit
  have hDen : Matrix.trace ((c • B) * B⁻¹) = 3 * c := by
    rw [Matrix.smul_mul, hMul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one]
    norm_num <;> ring
  letI : Invertible c := invertibleOfNonzero hc
  have hInv : (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul B c hUnit
  have hScalar : 3 / (3 * c) = c⁻¹ := by
    field_simp [hc]
  change (3 / Matrix.trace ((c • B) * B⁻¹)) • B⁻¹ - (c • B)⁻¹ = 0
  rw [hDen, hInv, hScalar]
  exact sub_self _

/-- Exact vanishing of the original eight-jet on the open scaled known side. -/
theorem coordinateH8_referenceNormalizedPrincipalDifference_zero_of_known_side
    (S : KnownSideSourceData) (L lam : ℝ) (y : R3)
    (hy : lam • y ∈ S.W) :
    coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y = 0 := by
  have hPoint (z : R3) (hz : lam • z ∈ S.W) :
      referenceNormalizedPrincipalDifference S.g1 S.g2 L lam z = 0 := by
    change normalizedPrincipalDifference
      (Real.exp (2 * (-L * referenceCoordinateDepth z)) • S.g1 (lam • z))
      (S.g2 (lam • z)) = 0
    rw [S.metrics_match hz]
    exact normalizedPrincipalDifference_smul_self_zero
      (S.g2 (lam • z)) (S.g2_admissible.posDef (lam • z))
      _ (Real.exp_ne_zero _)
  have hMap : Continuous (fun z : R3 => lam • z) := continuous_const_smul lam
  have hOpen : IsOpen ((fun z : R3 => lam • z) ⁻¹' S.W) :=
    S.W_open.preimage hMap
  have hLocal : referenceNormalizedPrincipalDifference S.g1 S.g2 L lam =ᶠ[𝓝 y]
      (fun _ : R3 => (0 : Mat)) := by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact hPoint z hz
  have hDerivZero (n : ℕ) :
      iteratedFDeriv ℝ n (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y = 0 := by
    have hn := (Filter.EventuallyEq.iteratedFDeriv ℝ hLocal n).eq_of_nhds
    simpa using hn
  have hSmooth : ContDiff ℝ ∞
      (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_referenceNormalizedPrincipalDifference_entry
      S.g1 S.g2 S.g1_admissible S.g2_admissible L lam i j
  obtain ⟨A,_,hA⟩ := exists_coordinateH8_le_frechet_jet_sum
  have hBound := hA (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) hSmooth y
  have hSum : ∑ n ∈ Finset.range 9,
      ‖iteratedFDeriv ℝ n (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y‖ = 0 := by
    simp only [hDerivZero, norm_zero, Finset.sum_const_zero]
  rw [hSum, mul_zero] at hBound
  exact le_antisymm hBound (coordinateH8_nonneg _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
