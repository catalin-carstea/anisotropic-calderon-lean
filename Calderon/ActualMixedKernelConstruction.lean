import Calderon.MixedKernelConstruction.MixedKernelNativeParameterAssembly
import Calderon.MixedKernelConstruction.MixedKernelClosedTubeConstruction
import Calderon.MixedKernelConstruction.MixedKernelClosedCoarseSeed
import Calderon.MixedKernelConstruction.MixedKernelMonotoneCurrentPair
import Calderon.MixedKernelConstruction.MixedKernelPositiveChartAgreement
import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
import Calderon.MixedKernelConstruction.MixedKernelCurrentCommonPair
import Calderon.MixedKernelConstruction.MixedKernelProductOpenUCP
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
import Calderon.MixedKernelConstruction.MixedKernelFiniteInterpolation
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
import Calderon.MixedKernelConstruction.MixedKernelAnnulusGeometry
import Calderon.MixedKernelConstruction.MixedKernelKnownSideCompactBuffer
import Calderon.MixedKernelConstruction.MixedKernelActualSeparatorAnchors
import Calderon.MixedKernelConstruction.MixedKernelKnownSideNeighborhood
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
import Calderon.MixedKernelConstruction.MixedKernelFullCrossAssembly
import Calderon.MixedKernelConstruction.MixedKernelAnchoredKernelConstruction
import Calderon.CollaboratorUCPCarlemanOct17
import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
import Calderon.MixedKernelConstruction.MixedKernelFullCrossExtension
import Calderon.MixedKernelConstruction.MixedKernelNativeRadialCoordinates
import Calderon.MixedKernelConstruction.MixedKernelActualChartZeroBox
import Calderon.MixedKernelConstruction.MixedKernelNativeFullCrossLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry


theorem original_kernel_joint_regular : OriginalKernelJointRegularityGoal :=
  v021_original_kernel_joint_regular
theorem normal_packet_cover_exists : NativeNormalPacketCoverGoal :=
  v021_normal_packet_cover_exists
theorem initial_cross_product : InitialCrossProductGoal := v021_initial_cross_product

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## The scaled tube criterion and one lambda0 on the compact sweep (N55-N60) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

/-- The source normalization `a = ⟪M b, b⟫⁻¹ • b` of a native covector `b`. -/
def stNormal (M : R3 →L[ℝ] R3) (b : R3) : R3 := (⟪M b, b⟫_ℝ)⁻¹ • b

/-- The universal clause of `ProductHessianStrictAt` for explicit fields. -/
abbrev StFieldStrict (M1 M2 : R3 →L[ℝ] R3) (b1 b2 : R3) (h : R3 × R3 → R3 × R3 → ℝ) : Prop :=
  ∀ v1 v2 : R3, ⟪M1 v1, stNormal M1 b1⟫_ℝ = 0 →
    ⟪M1 v1, v1⟫_ℝ = ⟪M1 (stNormal M1 b1), stNormal M1 b1⟫_ℝ →
    ⟪M2 v2, stNormal M2 b2⟫_ℝ = 0 →
    ⟪M2 v2, v2⟫_ℝ = ⟪M2 (stNormal M2 b2), stNormal M2 b2⟫_ℝ →
    0 < h (stNormal M1 b1, -stNormal M2 b2) (stNormal M1 b1, -stNormal M2 b2) + h (v1, v2) (v1, v2)

/-- A violating characteristic pair for explicit fields. -/
abbrev StFieldBad (M1 M2 : R3 →L[ℝ] R3) (b1 b2 : R3) (h : R3 × R3 → R3 × R3 → ℝ)
    (v : R3 × R3) : Prop :=
  ⟪M1 v.1, stNormal M1 b1⟫_ℝ = 0 ∧ ⟪M1 v.1, v.1⟫_ℝ = ⟪M1 (stNormal M1 b1), stNormal M1 b1⟫_ℝ ∧
    ⟪M2 v.2, stNormal M2 b2⟫_ℝ = 0 ∧ ⟪M2 v.2, v.2⟫_ℝ = ⟪M2 (stNormal M2 b2), stNormal M2 b2⟫_ℝ ∧
    h (stNormal M1 b1, -stNormal M2 b2) (stNormal M1 b1, -stNormal M2 b2) + h v v ≤ 0

/-- N55: `ProductHessianStrictAt` with its native lets replaced by equal explicit fields. -/
theorem productHessianStrictAt_iff_fields {g1 g2 : MatrixField} {x0 y0 : R3}
    {rho : R3 × R3 → ℝ} (M1 M2 : R3 →L[ℝ] R3) (b1 b2 : R3) (Γ1 Γ2 : R3 →L[ℝ] R3 →L[ℝ] R3)
    (h : R3 × R3 → R3 × R3 → ℝ)
    (hM1 : MetricOperator.metricOperatorField g1 x0 = M1)
    (hM2 : MetricOperator.metricOperatorField g2 y0 = M2)
    (hb1 : MetricOperator.matrixOperatorMap ((g1 x0)⁻¹) (WithLp.toLp 2 (fun i : Fin 3 =>
      ((fderiv ℝ rho (x0, y0)).comp (ContinuousLinearMap.inl ℝ R3 R3))
        (MetricVolume.coordinateVector i))) = b1)
    (hb2 : MetricOperator.matrixOperatorMap ((g2 y0)⁻¹) (WithLp.toLp 2 (fun i : Fin 3 =>
      ((fderiv ℝ rho (x0, y0)).comp (ContinuousLinearMap.inr ℝ R3 R3))
        (MetricVolume.coordinateVector i))) = b2)
    (hΓ1 : ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g1))
      (MetricOperator.metricOperatorField g1) x0 = Γ1)
    (hΓ2 : ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g2))
      (MetricOperator.metricOperatorField g2) y0 = Γ2)
    (hh : (fun W V : R3 × R3 => fderiv ℝ (fderiv ℝ rho) (x0, y0) W V -
      fderiv ℝ rho (x0, y0) (Γ1 W.1 V.1, Γ2 W.2 V.2)) = h) :
    ProductHessianStrictAt g1 g2 x0 y0 rho ↔
      ((fderiv ℝ rho (x0, y0)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
        (fderiv ℝ rho (x0, y0)).comp (ContinuousLinearMap.inr ℝ R3 R3) ≠ 0 ∧
        StFieldStrict M1 M2 b1 b2 h) := by
  subst hh
  subst hM1 hM2 hb1 hb2 hΓ1 hΓ2
  exact Iff.rfl

/-- The Riesz vector of the second partial covector of the actual UNSCALED tube phase. -/
def stGrad2 (M e0 a σ : ℝ) (X Y : R3) : R3 :=
  -(X - Y) - (tubeRadius M e0 a σ Y * (a * (1 + σ) * tubeHeight M e0 Y ^ σ)) •
    (InnerProductSpace.toDual ℝ R3).symm (tubeHeightDeriv e0 Y)

/-- The literal connection of the dilated metric `g(λ ·)` at `x`: `λ Γ_g(λ x)`. -/
def stGamma (g : MatrixField) (lam : ℝ) (x : R3) : R3 →L[ℝ] R3 →L[ℝ] R3 :=
  lam • ConnectionError.coordinateConnectionField
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
    (MetricOperator.metricOperatorField g) (lam • x)

/-- The first jet `ℓ(u) = ⟪X - Y, u₁ - u₂⟫ - r k dt_Y(u₂)` of the actual tube phase (J3). -/
def stEll (M e0 a σ : ℝ) (X Y : R3) (u : R3 × R3) : ℝ :=
  ⟪X - Y, u.1 - u.2⟫_ℝ - tubeRadius M e0 a σ Y *
    (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y u.2)

/-- J6's second jet with `r · a(1+σ)σ t^(σ-1)` written as `a²(1+σ)σ t^(2σ)` (equal for `t > 0`). -/
def stHess0 (M e0 a σ : ℝ) (Y : R3) (W V : R3 × R3) : ℝ :=
  ⟪W.1 - W.2, V.1 - V.2⟫_ℝ -
    (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y W.2) *
      (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y V.2) -
    a ^ 2 * (1 + σ) * σ * tubeHeight M e0 Y ^ (2 * σ) * tubeHeightDeriv e0 Y W.2 *
      tubeHeightDeriv e0 Y V.2 -
    tubeRadius M e0 a σ Y * (a * (1 + σ) * tubeHeight M e0 Y ^ σ *
      (2 * e0 * (W.2 0 * V.2 0 + W.2 1 * V.2 1)))

/-- The actual Hessian field `D²ρ - ℓ(Γ₁, Γ₂)` for the dilated metrics `S.g_i(λ ·)`. -/
def stHess (S : KnownSideSourceData) (M e0 a σ lam : ℝ) (X Y : R3) (W V : R3 × R3) : ℝ :=
  stHess0 M e0 a σ Y W V -
    stEll M e0 a σ X Y (stGamma S.g1 lam X W.1 V.1, stGamma S.g2 lam Y W.2 V.2)

/-- N56: for `t(Y) > 0`, the actual `ProductHessianStrictAt` for the dilated original metrics and the
UNSCALED tube phase is equivalent to nonvanishing Euclidean gradients plus the explicit field clause. -/
theorem tube_scaled_strict_iff (S : KnownSideSourceData) (M e0 a σ lam : ℝ) (X Y : R3)
    (ht : 0 < tubeHeight M e0 Y) :
    ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x)) X Y
        (tubePhase M e0 a σ) ↔
      (X - Y ≠ 0 ∧ stGrad2 M e0 a σ X Y ≠ 0 ∧
        StFieldStrict (MetricOperator.metricOperatorField S.g1 (lam • X))
          (MetricOperator.metricOperatorField S.g2 (lam • Y))
          (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g1) (lam • X)
            (X - Y))
          (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g2) (lam • Y)
            (stGrad2 M e0 a σ X Y))
          (stHess S M e0 a σ lam X Y)) := by
  obtain ⟨-, hJ⟩ := tube_phase_fderiv_apply M e0 a σ (X := X) ht
  obtain ⟨D, hD, hDe⟩ := tube_phase_second_jet M e0 a σ (X := X) ht
  have hR1 : ∀ U : R3, ((fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp
      (ContinuousLinearMap.inl ℝ R3 R3)) U = ⟪X - Y, U⟫_ℝ := by
    intro U
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hJ]
    simp
  have hR2 : ∀ U : R3, ((fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp
      (ContinuousLinearMap.inr ℝ R3 R3)) U = ⟪stGrad2 M e0 a σ X Y, U⟫_ℝ := by
    intro U
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hJ]
    simp only [stGrad2, inner_sub_left, inner_neg_left, real_inner_smul_left,
      InnerProductSpace.toDual_symm_apply, zero_sub, inner_neg_right]
    ring
  have hE1 : (fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ↔
      X - Y ≠ 0 := by
    constructor
    · intro h hz
      apply h
      refine ContinuousLinearMap.ext fun U => ?_
      rw [hR1, hz, inner_zero_left, ContinuousLinearMap.zero_apply]
    · intro hz h
      apply hz
      have h1 := hR1 (X - Y)
      rw [h, ContinuousLinearMap.zero_apply] at h1
      exact inner_self_eq_zero.mp h1.symm
  have hE2 : (fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp (ContinuousLinearMap.inr ℝ R3 R3) ≠ 0 ↔
      stGrad2 M e0 a σ X Y ≠ 0 := by
    constructor
    · intro h hz
      apply h
      refine ContinuousLinearMap.ext fun U => ?_
      rw [hR2, hz, inner_zero_left, ContinuousLinearMap.zero_apply]
    · intro hz h
      apply hz
      have h1 := hR2 (stGrad2 M e0 a σ X Y)
      rw [h, ContinuousLinearMap.zero_apply] at h1
      exact inner_self_eq_zero.mp h1.symm
  have hb1 : MetricOperator.matrixOperatorMap ((S.g1 (lam • X))⁻¹) (WithLp.toLp 2 (fun i : Fin 3 =>
      ((fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp (ContinuousLinearMap.inl ℝ R3 R3))
        (MetricVolume.coordinateVector i))) =
      ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g1) (lam • X)
        (X - Y) := by
    rw [euclidean_coordinate_riesz _ (X - Y) hR1,
      MetricOperator.inverseMetricField_eq_matrix_inverse S.g1 S.g1_admissible]
  have hb2 : MetricOperator.matrixOperatorMap ((S.g2 (lam • Y))⁻¹) (WithLp.toLp 2 (fun i : Fin 3 =>
      ((fderiv ℝ (tubePhase M e0 a σ) (X, Y)).comp (ContinuousLinearMap.inr ℝ R3 R3))
        (MetricVolume.coordinateVector i))) =
      ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g2) (lam • Y)
        (stGrad2 M e0 a σ X Y) := by
    rw [euclidean_coordinate_riesz _ (stGrad2 M e0 a σ X Y) hR2,
      MetricOperator.inverseMetricField_eq_matrix_inverse S.g2 S.g2_admissible]
  have hΓ : ∀ g : MatrixField, IsAdmissibleMetric g → ∀ x : R3,
      ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField fun y => g (lam • y)))
        (MetricOperator.metricOperatorField fun y => g (lam • y)) x = stGamma g lam x := by
    intro g hg x
    refine ContinuousLinearMap.ext fun U => ContinuousLinearMap.ext fun V => ?_
    rw [stGamma, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    exact ConformalDepth.dilatedMetric_connection_eq g hg lam x U V
  have hrs : tubeRadius M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1)) =
      a ^ 2 * (1 + σ) * σ * tubeHeight M e0 Y ^ (2 * σ) := by
    have h2 : tubeHeight M e0 Y ^ (2 * σ) =
        tubeHeight M e0 Y ^ (1 + σ) * tubeHeight M e0 Y ^ (σ - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [h2]
    unfold tubeRadius
    ring
  have hH : (fun W V : R3 × R3 => fderiv ℝ (fderiv ℝ (tubePhase M e0 a σ)) (X, Y) W V -
      fderiv ℝ (tubePhase M e0 a σ) (X, Y) (stGamma S.g1 lam X W.1 V.1, stGamma S.g2 lam Y W.2 V.2)) =
      stHess S M e0 a σ lam X Y := by
    funext W V
    show fderiv ℝ (fderiv ℝ (tubePhase M e0 a σ)) (X, Y) W V -
      fderiv ℝ (tubePhase M e0 a σ) (X, Y) (stGamma S.g1 lam X W.1 V.1, stGamma S.g2 lam Y W.2 V.2) =
      stHess S M e0 a σ lam X Y W V
    rw [hD.fderiv, hDe, hJ]
    simp only [stHess, stHess0, stEll]
    linear_combination (-(tubeHeightDeriv e0 Y W.2 * tubeHeightDeriv e0 Y V.2)) * hrs
  exact (productHessianStrictAt_iff_fields (g1 := fun x => S.g1 (lam • x))
    (g2 := fun x => S.g2 (lam • x)) (x0 := X) (y0 := Y) (rho := tubePhase M e0 a σ)
    (MetricOperator.metricOperatorField S.g1 (lam • X))
    (MetricOperator.metricOperatorField S.g2 (lam • Y))
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g1) (lam • X) (X - Y))
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField S.g2) (lam • Y)
      (stGrad2 M e0 a σ X Y))
    (stGamma S.g1 lam X) (stGamma S.g2 lam Y) (stHess S M e0 a σ lam X Y) rfl rfl hb1 hb2
    (hΓ S.g1 S.g1_admissible X) (hΓ S.g2 S.g2_admissible Y) hH).trans
    (and_congr hE1 (and_congr hE2 Iff.rfl))

/-- N57: the `ContinuousOn` variant of N39 on a closed parameter set `C`. -/
theorem stFieldBad_isClosed {D : Type*} [TopologicalSpace D] {C : Set D} (hC : IsClosed C)
    {M1 M2 : D → R3 →L[ℝ] R3} {b1 b2 : D → R3} {h : D → R3 × R3 → R3 × R3 → ℝ}
    (hM1 : Continuous M1) (hM2 : Continuous M2) (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hh : Continuous fun w : D × (R3 × R3) × (R3 × R3) => h w.1 w.2.1 w.2.2)
    (hc : ∀ p ∈ C, ⟪M1 p (b1 p), b1 p⟫_ℝ ≠ 0 ∧ ⟪M2 p (b2 p), b2 p⟫_ℝ ≠ 0) :
    IsClosed {z : D × (R3 × R3) |
      z.1 ∈ C ∧ StFieldBad (M1 z.1) (M2 z.1) (b1 z.1) (b2 z.1) (h z.1) z.2} := by
  have hs : IsClosed (C ×ˢ (univ : Set (R3 × R3))) := hC.prod isClosed_univ
  have hsC : MapsTo Prod.fst (C ×ˢ (univ : Set (R3 × R3))) C := fun z hz => hz.1
  have ha1 : ContinuousOn (fun p => stNormal (M1 p) (b1 p)) C :=
    (((hM1.clm_apply hb1).inner (𝕜 := ℝ) hb1).continuousOn.inv₀ fun p hp => (hc p hp).1).smul
      hb1.continuousOn
  have ha2 : ContinuousOn (fun p => stNormal (M2 p) (b2 p)) C :=
    (((hM2.clm_apply hb2).inner (𝕜 := ℝ) hb2).continuousOn.inv₀ fun p hp => (hc p hp).2).smul
      hb2.continuousOn
  have cA1 : ContinuousOn (fun z : D × (R3 × R3) => stNormal (M1 z.1) (b1 z.1))
      (C ×ˢ (univ : Set (R3 × R3))) := ha1.comp continuousOn_fst hsC
  have cA2 : ContinuousOn (fun z : D × (R3 × R3) => stNormal (M2 z.1) (b2 z.1))
      (C ×ˢ (univ : Set (R3 × R3))) := ha2.comp continuousOn_fst hsC
  have cM1 : ContinuousOn (fun z : D × (R3 × R3) => M1 z.1) (C ×ˢ (univ : Set (R3 × R3))) :=
    (hM1.comp continuous_fst).continuousOn
  have cM2 : ContinuousOn (fun z : D × (R3 × R3) => M2 z.1) (C ×ˢ (univ : Set (R3 × R3))) :=
    (hM2.comp continuous_fst).continuousOn
  have cv1 : ContinuousOn (fun z : D × (R3 × R3) => z.2.1) (C ×ˢ (univ : Set (R3 × R3))) :=
    continuous_snd.fst.continuousOn
  have cv2 : ContinuousOn (fun z : D × (R3 × R3) => z.2.2) (C ×ˢ (univ : Set (R3 × R3))) :=
    continuous_snd.snd.continuousOn
  have cA : ContinuousOn (fun z : D × (R3 × R3) =>
      (stNormal (M1 z.1) (b1 z.1), -stNormal (M2 z.1) (b2 z.1))) (C ×ˢ (univ : Set (R3 × R3))) :=
    cA1.prodMk cA2.neg
  have cH : ContinuousOn (fun z : D × (R3 × R3) =>
      h z.1 (stNormal (M1 z.1) (b1 z.1), -stNormal (M2 z.1) (b2 z.1))
        (stNormal (M1 z.1) (b1 z.1), -stNormal (M2 z.1) (b2 z.1)) + h z.1 z.2 z.2)
      (C ×ˢ (univ : Set (R3 × R3))) :=
    (hh.comp_continuousOn (continuousOn_fst.prodMk (cA.prodMk cA))).add
      (hh.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))).continuousOn
  have e1 := ((cM1.clm_apply cv1).inner (𝕜 := ℝ) cA1).preimage_isClosed_of_isClosed hs
    (isClosed_singleton : IsClosed ({0} : Set ℝ))
  have e2 := (((cM1.clm_apply cv1).inner (𝕜 := ℝ) cv1).sub
    ((cM1.clm_apply cA1).inner (𝕜 := ℝ) cA1)).preimage_isClosed_of_isClosed hs
    (isClosed_singleton : IsClosed ({0} : Set ℝ))
  have e3 := ((cM2.clm_apply cv2).inner (𝕜 := ℝ) cA2).preimage_isClosed_of_isClosed hs
    (isClosed_singleton : IsClosed ({0} : Set ℝ))
  have e4 := (((cM2.clm_apply cv2).inner (𝕜 := ℝ) cv2).sub
    ((cM2.clm_apply cA2).inner (𝕜 := ℝ) cA2)).preimage_isClosed_of_isClosed hs
    (isClosed_singleton : IsClosed ({0} : Set ℝ))
  have e5 := cH.preimage_isClosed_of_isClosed hs (isClosed_Iic : IsClosed (Iic (0 : ℝ)))
  convert e1.inter (e2.inter (e3.inter (e4.inter e5))) using 1
  ext z
  simp only [StFieldBad, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Iic,
    mem_prod, mem_univ, and_true, Pi.sub_apply, sub_eq_zero]
  tauto

/-- N58: continuous fields with identity metrics and nonzero covectors at `p0` propagate the explicit
strictness clause from `p0` to a neighborhood (closed local bad set N57, compact fiber N38/N37, N41). -/
theorem eventually_stFieldStrict {D : Type*} [TopologicalSpace D] [RegularSpace D] {p0 : D}
    (M1 M2 : D → R3 →L[ℝ] R3) (b1 b2 : D → R3) (h : D → R3 × R3 → R3 × R3 → ℝ)
    (hM1 : Continuous M1) (hM2 : Continuous M2) (hM10 : M1 p0 = ContinuousLinearMap.id ℝ R3)
    (hM20 : M2 p0 = ContinuousLinearMap.id ℝ R3) (hb1 : Continuous b1) (hb2 : Continuous b2)
    (hb10 : b1 p0 ≠ 0) (hb20 : b2 p0 ≠ 0)
    (hh : Continuous fun w : D × (R3 × R3) × (R3 × R3) => h w.1 w.2.1 w.2.2)
    (h0 : StFieldStrict (M1 p0) (M2 p0) (b1 p0) (b2 p0) (h p0)) :
    ∀ᶠ p in 𝓝 p0, StFieldStrict (M1 p) (M2 p) (b1 p) (b2 p) (h p) := by
  have hc1 : Continuous fun p => ⟪M1 p (b1 p), b1 p⟫_ℝ := (hM1.clm_apply hb1).inner (𝕜 := ℝ) hb1
  have hc2 : Continuous fun p => ⟪M2 p (b2 p), b2 p⟫_ℝ := (hM2.clm_apply hb2).inner (𝕜 := ℝ) hb2
  have hc10 : ⟪M1 p0 (b1 p0), b1 p0⟫_ℝ ≠ 0 := by
    rw [hM10, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hb10)
  have hc20 : ⟪M2 p0 (b2 p0), b2 p0⟫_ℝ ≠ 0 := by
    rw [hM20, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hb20)
  have hU : {p | ⟪M1 p (b1 p), b1 p⟫_ℝ ≠ 0 ∧ ⟪M2 p (b2 p), b2 p⟫_ℝ ≠ 0} ∈ 𝓝 p0 :=
    (hc1.continuousAt.eventually_ne hc10).and (hc2.continuousAt.eventually_ne hc20)
  obtain ⟨C, hC, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  have hbad := stFieldBad_isClosed hCc hM1 hM2 hb1 hb2 hh fun p hp => hCU hp
  obtain ⟨β, -, hfib⟩ := eventually_fiber_of_continuousAt M1 M2 b1 b2 hM1.continuousAt
    hM2.continuousAt hM10 hM20 hb1.continuousAt hb2.continuousAt hb10 hb20
    (bad := fun p v => StFieldBad (M1 p) (M2 p) (b1 p) (b2 p) (h p) v)
    fun p v (hv : StFieldBad (M1 p) (M2 p) (b1 p) (b2 p) (h p) v) => ⟨hv.2.1, hv.2.2.2.1⟩
  have h0' : ∀ v ∈ Metric.closedBall (0 : R3) (4 / β) ×ˢ Metric.closedBall (0 : R3) (4 / β),
      ¬ StFieldBad (M1 p0) (M2 p0) (b1 p0) (b2 p0) (h p0) v := by
    rintro ⟨v1, v2⟩ - ⟨h1, h2, h3, h4, h5⟩
    exact absurd (h0 v1 v2 h1 h2 h3 h4) (not_lt.2 h5)
  filter_upwards [eventually_forall_not_bad_of_fiber_local (char_pair_fiber_isCompact (4 / β))
    (bad := fun p v => StFieldBad (M1 p) (M2 p) (b1 p) (b2 p) (h p) v) hC hbad h0' hfib]
    with p hp
  intro v1 v2 h1 h2 h3 h4
  by_contra hn
  exact hp (v1, v2) ⟨h1, h2, h3, h4, not_lt.1 hn⟩

/-- N59a: the actual tube height is continuous. -/
theorem st_height_continuous (M e0 : ℝ) : Continuous (tubeHeight M e0) :=
  continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt M e0 Y).continuousAt

/-- N59a: the actual tube height differential is continuous (J4). -/
theorem st_heightDeriv_continuous (e0 : ℝ) : Continuous (tubeHeightDeriv e0) :=
  continuous_iff_continuousAt.2 fun Y => by
    obtain ⟨D, hD, -⟩ := tube_height_deriv_hasFDerivAt e0 Y
    exact hD.continuousAt

/-- N59b: the Riesz vector `G₂` is jointly continuous in all parameters. -/
theorem stGrad2_continuous {E : Type*} [TopologicalSpace E] (M e0 σ : ℝ) (hσ : 0 ≤ σ)
    {a : E → ℝ} {X Y : E → R3} (ha : Continuous a) (hX : Continuous X) (hY : Continuous Y) :
    Continuous fun e => stGrad2 M e0 (a e) σ (X e) (Y e) := by
  have ht : Continuous fun e => tubeHeight M e0 (Y e) := (st_height_continuous M e0).comp hY
  have hr : Continuous fun e => tubeRadius M e0 (a e) σ (Y e) :=
    (tubeRadius_continuous M e0 σ hσ).comp (ha.prodMk hY)
  have hk : Continuous fun e => a e * (1 + σ) * tubeHeight M e0 (Y e) ^ σ :=
    (ha.mul continuous_const).mul (ht.rpow_const fun _ => Or.inr hσ)
  have hd : Continuous fun e => (InnerProductSpace.toDual ℝ R3).symm (tubeHeightDeriv e0 (Y e)) :=
    (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
      ((st_heightDeriv_continuous e0).comp hY)
  exact (hX.sub hY).neg.sub ((hr.mul hk).smul hd)

/-- N59c: the actual Hessian field `stHess` is jointly continuous in all parameters. -/
theorem stHess_continuous {E : Type*} [TopologicalSpace E] (S : KnownSideSourceData)
    (M e0 σ : ℝ) (hσ : 0 ≤ σ) {lam a : E → ℝ} {X Y : E → R3} {W V : E → R3 × R3}
    (hl : Continuous lam) (ha : Continuous a) (hX : Continuous X) (hY : Continuous Y)
    (hW : Continuous W) (hV : Continuous V) :
    Continuous fun e => stHess S M e0 (a e) σ (lam e) (X e) (Y e) (W e) (V e) := by
  have ht : Continuous fun e => tubeHeight M e0 (Y e) := (st_height_continuous M e0).comp hY
  have hr : Continuous fun e => tubeRadius M e0 (a e) σ (Y e) :=
    (tubeRadius_continuous M e0 σ hσ).comp (ha.prodMk hY)
  have hk : Continuous fun e => a e * (1 + σ) * tubeHeight M e0 (Y e) ^ σ :=
    (ha.mul continuous_const).mul (ht.rpow_const fun _ => Or.inr hσ)
  have hs : Continuous fun e => a e ^ 2 * (1 + σ) * σ * tubeHeight M e0 (Y e) ^ (2 * σ) :=
    (((ha.pow 2).mul continuous_const).mul continuous_const).mul
      (ht.rpow_const fun _ => Or.inr (by linarith))
  have hd : Continuous fun e => tubeHeightDeriv e0 (Y e) := (st_heightDeriv_continuous e0).comp hY
  have hdW : Continuous fun e => tubeHeightDeriv e0 (Y e) (W e).2 := hd.clm_apply hW.snd
  have hdV : Continuous fun e => tubeHeightDeriv e0 (Y e) (V e).2 := hd.clm_apply hV.snd
  have hc : ∀ (i : Fin 3) (Z : E → R3), Continuous Z → Continuous fun e => Z e i :=
    fun i Z hZ => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hZ
  have hΓ : ∀ g : MatrixField, IsAdmissibleMetric g → ∀ Z : E → R3, Continuous Z →
      Continuous fun e => stGamma g (lam e) (Z e) := fun g hg Z hZ =>
    hl.smul ((MetricOperator.contDiff_metricCoordinateConnection g hg).continuous.comp
      (hl.smul hZ))
  have hG1 : Continuous fun e => stGamma S.g1 (lam e) (X e) (W e).1 (V e).1 :=
    ((hΓ S.g1 S.g1_admissible X hX).clm_apply hW.fst).clm_apply hV.fst
  have hG2 : Continuous fun e => stGamma S.g2 (lam e) (Y e) (W e).2 (V e).2 :=
    ((hΓ S.g2 S.g2_admissible Y hY).clm_apply hW.snd).clm_apply hV.snd
  have hH0 : Continuous fun e => stHess0 M e0 (a e) σ (Y e) (W e) (V e) :=
    ((((hW.fst.sub hW.snd).inner (𝕜 := ℝ) (hV.fst.sub hV.snd)).sub
      ((hk.mul hdW).mul (hk.mul hdV))).sub ((hs.mul hdW).mul hdV)).sub
      (hr.mul (hk.mul (continuous_const.mul (((hc 0 _ hW.snd).mul (hc 0 _ hV.snd)).add
        ((hc 1 _ hW.snd).mul (hc 1 _ hV.snd))))))
  have hE : Continuous fun e => stEll M e0 (a e) σ (X e) (Y e)
      (stGamma S.g1 (lam e) (X e) (W e).1 (V e).1, stGamma S.g2 (lam e) (Y e) (W e).2 (V e).2) :=
    ((hX.sub hY).inner (𝕜 := ℝ) (hG1.sub hG2)).sub (hr.mul (hk.mul (hd.clm_apply hG2)))
  exact hH0.sub hE

/-- N60: under N23's exact hypotheses, with N53's `σ, T0, e0` and compact sweep `Q`, ONE `λ0 > 0`
gives the actual `ProductHessianStrictAt` for the dilated original metrics `S.g_i(λ ·)` and the
UNSCALED tube phase at every `λ ∈ (0, λ0]` and every sweep point. -/
theorem tube_scaled_strict_uniform (S : KnownSideSourceData) {c0 η d B M : ℝ} (hc0 : 0 < c0)
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B)
    (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ 0 < e0 ∧
      IsCompact {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} ∧
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
        ∀ p ∈ {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
          min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
          c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
            min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)},
          ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
            (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) p.2.1 (tubePhase M e0 p.1 σ) := by
  obtain ⟨σ, T0, e0, hσ, he0, hQc, hQs⟩ := tube_native_strict_sweep_set hc0 hη hη10 hc0η hd hB hM
  refine ⟨σ, T0, e0, hσ, he0, hQc, ?_⟩
  refine exists_uniform_lambda0 hQc (good := fun lam p =>
    ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
      (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) p.2.1 (tubePhase M e0 p.1 σ)) ?_
  intro q hq
  have hq' := hq
  obtain ⟨-, hY2, hT, -⟩ := hq'
  have hlc : Continuous fun z : ℝ × ℝ × R3 × R3 => z.1 := continuous_fst
  have hac : Continuous fun z : ℝ × ℝ × R3 × R3 => z.2.1 := continuous_snd.fst
  have hYc : Continuous fun z : ℝ × ℝ × R3 × R3 => z.2.2.1 := continuous_snd.snd.fst
  have hXc : Continuous fun z : ℝ × ℝ × R3 × R3 =>
      z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2 :=
    (tubeEndpoint_continuous M e0 σ hσ.le).comp continuous_snd
  have htq : 0 < tubeHeight M e0 q.2.1 := by
    have := (tube_base_height he0.le hM hY2 hT).1
    linarith
  have e1 : (fun x : R3 => S.g1 ((0 : ℝ) • x)) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    funext fun x => by rw [zero_smul]; exact S.g1_origin
  have e2 : (fun x : R3 => S.g2 ((0 : ℝ) • x)) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    funext fun x => by rw [zero_smul]; exact S.g2_origin
  have hbase : ProductHessianStrictAt (fun x => S.g1 ((0 : ℝ) • x)) (fun x => S.g2 ((0 : ℝ) • x))
      (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ) := by
    rw [e1, e2]
    exact hQs q hq
  obtain ⟨hG10, hG20, hS0⟩ := (tube_scaled_strict_iff S M e0 q.1 σ 0 _ _ htq).1 hbase
  obtain ⟨hb1c, hb10⟩ := scaled_inverse_covector_base S.g1 S.g1_admissible S.g1_origin
    (hlc.smul hXc) (hXc.sub hYc) (p0 := ((0 : ℝ), q)) (zero_smul ℝ _)
  obtain ⟨hb2c, hb20⟩ := scaled_inverse_covector_base S.g2 S.g2_admissible S.g2_origin
    (hlc.smul hYc) (stGrad2_continuous M e0 σ hσ.le hac hXc hYc) (p0 := ((0 : ℝ), q))
    (zero_smul ℝ _)
  have hloc := eventually_stFieldStrict (p0 := ((0 : ℝ), q))
    (fun z : ℝ × ℝ × R3 × R3 => MetricOperator.metricOperatorField S.g1
      (z.1 • (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2)))
    (fun z : ℝ × ℝ × R3 × R3 => MetricOperator.metricOperatorField S.g2 (z.1 • z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => ConnectionError.inverseMetricField
      (MetricOperator.metricOperatorField S.g1)
      (z.1 • (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2))
      ((z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) - z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => ConnectionError.inverseMetricField
      (MetricOperator.metricOperatorField S.g2) (z.1 • z.2.2.1)
      (stGrad2 M e0 z.2.1 σ (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => stHess S M e0 z.2.1 σ z.1
      (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1)
    ((MetricOperator.contDiff_metricOperatorField S.g1 S.g1_admissible).continuous.comp
      (hlc.smul hXc))
    ((MetricOperator.contDiff_metricOperatorField S.g2 S.g2_admissible).continuous.comp
      (hlc.smul hYc))
    (scaled_metricOperatorField_zero S.g1 S.g1_origin _)
    (scaled_metricOperatorField_zero S.g2 S.g2_origin _)
    hb1c hb2c (fun h => hG10 (hb10.symm.trans h)) (fun h => hG20 (hb20.symm.trans h))
    (stHess_continuous S M e0 σ hσ.le (hlc.comp continuous_fst) (hac.comp continuous_fst)
      (hXc.comp continuous_fst) (hYc.comp continuous_fst) continuous_snd.fst continuous_snd.snd)
    hS0
  have hpos : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q), 0 < tubeHeight M e0 z.2.2.1 :=
    ((st_height_continuous M e0).comp hYc).continuousAt.eventually (lt_mem_nhds htq)
  have hG1e : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q),
      (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) - z.2.2.1 ≠ 0 :=
    (hXc.sub hYc).continuousAt.eventually_ne hG10
  have hG2e : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q),
      stGrad2 M e0 z.2.1 σ (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1 ≠ 0 :=
    (stGrad2_continuous M e0 σ hσ.le hac hXc hYc).continuousAt.eventually_ne hG20
  filter_upwards [hpos, hG1e, hG2e, hloc] with z hz1 hz2 hz3 hz4
  exact (tube_scaled_strict_iff S M e0 z.2.1 σ z.1 _ _ hz1).2 ⟨hz2, hz3, hz4⟩

/-- N61: the actual tube height is `C^∞`. -/
theorem st_height_contDiff (M e0 : ℝ) : ContDiff ℝ ∞ (tubeHeight M e0) := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff (n := ∞)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff (n := ∞)
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff (n := ∞)
  have hf : tubeHeight M e0 = fun x : R3 => M + EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) x +
      e0 * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) x ^ 2 +
        EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) x ^ 2) := by
    funext x
    simp [tubeHeight]
  rw [hf]
  exact (contDiff_const.add h2).add (contDiff_const.mul ((h0.pow 2).add (h1.pow 2)))

/-- N61: the actual UNSCALED tube phase is `C^∞` on the open positive-height set. -/
theorem tube_phase_contDiffOn (M e0 a σ : ℝ) :
    IsOpen {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∧
      ContDiffOn ℝ ∞ (tubePhase M e0 a σ) {z : R3 × R3 | 0 < tubeHeight M e0 z.2} := by
  have ht : ContDiff ℝ ∞ fun z : R3 × R3 => tubeHeight M e0 z.2 :=
    (st_height_contDiff M e0).comp contDiff_snd
  have hr : ContDiffOn ℝ ∞ (fun z : R3 × R3 => tubeRadius M e0 a σ z.2)
      {z : R3 × R3 | 0 < tubeHeight M e0 z.2} :=
    contDiffOn_const.mul (ht.contDiffOn.rpow_const_of_ne fun z hz => ne_of_gt hz)
  have hn : ContDiff ℝ ∞ fun z : R3 × R3 => ‖z.1 - z.2‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)
  exact ⟨isOpen_lt continuous_const ht.continuous, (hn.contDiffOn.sub (hr.pow 2)).div_const 2⟩

/-- N62: the actual tube phase vanishes at `(Y + r ω, Y)` for `‖ω‖ = 1`. -/
theorem tube_phase_zero (M e0 a σ : ℝ) (Y w : R3) (hw : ‖w‖ = 1) :
    tubePhase M e0 a σ (Y + tubeRadius M e0 a σ Y • w, Y) = 0 := by
  simp [tubePhase, norm_smul, hw]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## Coherent tube witnesses and one lambda0 for the same `σ, T0, e0` (N63-N66) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

/-- N63: N20 together with the positivity `0 < T0` of its OWN witness (stated by N19). -/
theorem tube_native_strict_sweep_targets_pos {c0 η d Ut : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hUt : 1 ≤ Ut) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧ 1 < c0 * min 1 (d / (2 * Ut ^ 2)) * T0 ^ σ ∧
      0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
      (∀ D t : ℝ, d ≤ D → 1 ≤ t → t ≤ Ut → min 1 (d / (2 * Ut ^ 2)) < D / t ^ (1 + σ)) ∧
      ∀ (M a : ℝ) (Y w : R3), 0 < M → ‖w‖ = 1 → 1 ≤ tubeHeight M e0 Y →
        tubeHeight M e0 Y ≤ T0 → e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0 →
        min 1 (d / (2 * Ut ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius M e0 a σ Y • w) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖) →
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • w) Y
          (tubePhase M e0 a σ) := by
  have hU2 : 0 < 2 * Ut ^ 2 := by positivity
  have ham : 0 < min 1 (d / (2 * Ut ^ 2)) := lt_min one_pos (div_pos hd hU2)
  obtain ⟨σ, T0, hσpos, hση, hσ1, hT0pos, hT0, hU⟩ :=
    tube_native_strict_sweep_uniform hc0 hη hη10 hc0η ham
  obtain ⟨e0, he0pos, he0B, hS⟩ := hU (max 1 T0) (le_max_left _ _)
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hT0pos, hT0, he0pos, he0B,
    fun D t hdD ht1 htU => tube_target_level_gt hd hdD ht1 htU hσpos.le hσ1, ?_⟩
  intro M a Y w hM hw ht1 htT hYT ha1 ha2 hout
  exact hS M a Y w hM hw ht1 (htT.trans (le_max_right _ _)) hYT ha1 ha2 hout

/-- N64: N23 together with the positivity `0 < T0` of the SAME witness. -/
theorem tube_native_strict_sweep_base_pos {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      (∀ (D : ℝ) (Y : R3), d ≤ D → -B - 1 ≤ Y 2 → Y 2 ≤ B → Y 0 ^ 2 + Y 1 ^ 2 ≤ B ^ 2 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) < D / tubeHeight M e0 Y ^ (1 + σ)) ∧
      ∀ (a : ℝ) (Y w : R3), ‖w‖ = 1 → -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius M e0 a σ Y • w) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖) →
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • w) Y
          (tubePhase M e0 a σ) := by
  have hUt : 1 ≤ M + B + B ^ 2 := by
    have := sq_nonneg B
    linarith
  obtain ⟨σ, T0, e0, hσpos, hση, hσ1, hT0pos, hT0, he0pos, he0B, htgt, hS⟩ :=
    tube_native_strict_sweep_targets_pos hc0 hη hη10 hc0η hd hUt
  have h1 : 1 / ((4 / c0) ^ 2 + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [sq_nonneg (4 / c0)]
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hT0pos, hT0, he0pos, he0B.trans h1, ?_, ?_⟩
  · intro D Y hdD hy1 hy2 hh
    exact htgt D _ hdD (tube_base_height (T0 := tubeHeight M e0 Y) he0pos.le hM hy1 le_rfl).1
      (tube_target_height_le he0pos.le (he0B.trans h1) hy2 hh)
  · intro a Y w hw hy htT ha1 ha2 hout
    obtain ⟨ht1, hYT⟩ := tube_base_height he0pos.le hM hy htT
    have hM0 : 0 < M := by linarith
    exact hS M a Y w hM0 hw ht1 htT hYT ha1 ha2 hout

/-- N65: for FIXED `M, e0, σ` and ANY compact actual sweep `Q` with positive height and identity-data
strictness, ONE `λ0 > 0` gives the actual dilated `ProductHessianStrictAt` on `Q` (N60's argument). -/
theorem exists_uniform_dilation_of_compact_tube_strictness
    (S : KnownSideSourceData) (M e0 σ : ℝ) (hσ : 0 ≤ σ)
    {Q : Set (ℝ × R3 × R3)} (hQ : IsCompact Q)
    (hHeight : ∀ q ∈ Q, 0 < tubeHeight M e0 q.2.1)
    (hBase : ∀ q ∈ Q,
      ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ)) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ q ∈ Q,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
        (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ) := by
  refine exists_uniform_lambda0 hQ (good := fun lam p =>
    ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
      (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) p.2.1 (tubePhase M e0 p.1 σ)) ?_
  intro q hq
  have hlc : Continuous fun z : ℝ × ℝ × R3 × R3 => z.1 := continuous_fst
  have hac : Continuous fun z : ℝ × ℝ × R3 × R3 => z.2.1 := continuous_snd.fst
  have hYc : Continuous fun z : ℝ × ℝ × R3 × R3 => z.2.2.1 := continuous_snd.snd.fst
  have hXc : Continuous fun z : ℝ × ℝ × R3 × R3 =>
      z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2 :=
    (tubeEndpoint_continuous M e0 σ hσ).comp continuous_snd
  have htq : 0 < tubeHeight M e0 q.2.1 := hHeight q hq
  have e1 : (fun x : R3 => S.g1 ((0 : ℝ) • x)) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    funext fun x => by rw [zero_smul]; exact S.g1_origin
  have e2 : (fun x : R3 => S.g2 ((0 : ℝ) • x)) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    funext fun x => by rw [zero_smul]; exact S.g2_origin
  have hbase : ProductHessianStrictAt (fun x => S.g1 ((0 : ℝ) • x)) (fun x => S.g2 ((0 : ℝ) • x))
      (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ) := by
    rw [e1, e2]
    exact hBase q hq
  obtain ⟨hG10, hG20, hS0⟩ := (tube_scaled_strict_iff S M e0 q.1 σ 0 _ _ htq).1 hbase
  obtain ⟨hb1c, hb10⟩ := scaled_inverse_covector_base S.g1 S.g1_admissible S.g1_origin
    (hlc.smul hXc) (hXc.sub hYc) (p0 := ((0 : ℝ), q)) (zero_smul ℝ _)
  obtain ⟨hb2c, hb20⟩ := scaled_inverse_covector_base S.g2 S.g2_admissible S.g2_origin
    (hlc.smul hYc) (stGrad2_continuous M e0 σ hσ hac hXc hYc) (p0 := ((0 : ℝ), q))
    (zero_smul ℝ _)
  have hloc := eventually_stFieldStrict (p0 := ((0 : ℝ), q))
    (fun z : ℝ × ℝ × R3 × R3 => MetricOperator.metricOperatorField S.g1
      (z.1 • (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2)))
    (fun z : ℝ × ℝ × R3 × R3 => MetricOperator.metricOperatorField S.g2 (z.1 • z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => ConnectionError.inverseMetricField
      (MetricOperator.metricOperatorField S.g1)
      (z.1 • (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2))
      ((z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) - z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => ConnectionError.inverseMetricField
      (MetricOperator.metricOperatorField S.g2) (z.1 • z.2.2.1)
      (stGrad2 M e0 z.2.1 σ (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1))
    (fun z : ℝ × ℝ × R3 × R3 => stHess S M e0 z.2.1 σ z.1
      (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1)
    ((MetricOperator.contDiff_metricOperatorField S.g1 S.g1_admissible).continuous.comp
      (hlc.smul hXc))
    ((MetricOperator.contDiff_metricOperatorField S.g2 S.g2_admissible).continuous.comp
      (hlc.smul hYc))
    (scaled_metricOperatorField_zero S.g1 S.g1_origin _)
    (scaled_metricOperatorField_zero S.g2 S.g2_origin _)
    hb1c hb2c (fun h => hG10 (hb10.symm.trans h)) (fun h => hG20 (hb20.symm.trans h))
    (stHess_continuous S M e0 σ hσ (hlc.comp continuous_fst) (hac.comp continuous_fst)
      (hXc.comp continuous_fst) (hYc.comp continuous_fst) continuous_snd.fst continuous_snd.snd)
    hS0
  have hpos : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q), 0 < tubeHeight M e0 z.2.2.1 :=
    ((st_height_continuous M e0).comp hYc).continuousAt.eventually (lt_mem_nhds htq)
  have hG1e : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q),
      (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) - z.2.2.1 ≠ 0 :=
    (hXc.sub hYc).continuousAt.eventually_ne hG10
  have hG2e : ∀ᶠ z : ℝ × ℝ × R3 × R3 in 𝓝 ((0 : ℝ), q),
      stGrad2 M e0 z.2.1 σ (z.2.2.1 + tubeRadius M e0 z.2.1 σ z.2.2.1 • z.2.2.2) z.2.2.1 ≠ 0 :=
    (stGrad2_continuous M e0 σ hσ hac hXc hYc).continuousAt.eventually_ne hG20
  filter_upwards [hpos, hG1e, hG2e, hloc] with z hz1 hz2 hz3 hz4
  exact (tube_scaled_strict_iff S M e0 z.2.1 σ z.1 _ _ hz1).2 ⟨hz2, hz3, hz4⟩

/-- N66: ONE witness triple `σ, T0, e0` simultaneously gives all N23 seed/target inequalities, `0 < T0`,
compactness of the literal sweep `Q` and ONE `λ0 > 0` with actual dilated strictness on `Q`. -/
theorem tube_scaled_strict_coherent (S : KnownSideSourceData) {c0 η d B M : ℝ} (hc0 : 0 < c0)
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B)
    (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      (∀ (D : ℝ) (Y : R3), d ≤ D → -B - 1 ≤ Y 2 → Y 2 ≤ B → Y 0 ^ 2 + Y 1 ^ 2 ≤ B ^ 2 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) < D / tubeHeight M e0 Y ^ (1 + σ)) ∧
      IsCompact {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} ∧
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
        ∀ p ∈ {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
          min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
          c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
            min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)},
          ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
            (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) p.2.1 (tubePhase M e0 p.1 σ) := by
  obtain ⟨σ, T0, e0, hσ, hση, hσ1, hT0pos, hT0, he0, he01, htgt, hS⟩ :=
    tube_native_strict_sweep_base_pos hc0 hη hη10 hc0η hd hB hM
  have hQc := tubeSweep_isCompact M e0 σ c0 B T0 (min 1 (d / (2 * (M + B + B ^ 2) ^ 2)))
    (2 / c0 + 1) hσ.le he0
  refine ⟨σ, T0, e0, hσ, hση, hσ1, hT0pos, hT0, he0, he01, htgt, hQc, ?_⟩
  refine exists_uniform_dilation_of_compact_tube_strictness S M e0 σ hσ.le hQc ?_ ?_
  · rintro ⟨a, Y, w⟩ ⟨-, hY2, hT, -⟩
    have h1 := (tube_base_height he0.le hM hY2 hT).1
    show 0 < tubeHeight M e0 Y
    linarith
  · rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, hsep⟩
    exact hS a Y w hw hY2 hT ha1 ha2 (not_lt.2 hsep)

/-- N67: exact target coverage: in actual tube coordinates `a = ‖X-Y‖/t^(1+σ)`, `w = (X-Y)/‖X-Y‖`, a target
pair with the strict level gap is either in the literal coarse cone or strictly inside the unseeded region. -/
theorem tube_target_cover {M e0 σ c0 B T0 amin : ℝ} {X Y : R3} (hc0 : 0 < c0) (hσ : 0 < σ)
    (he0 : 0 ≤ e0) (hB : 0 ≤ B) (hM : B + 3 < M) (hT0 : 0 < T0) (ham : 0 < amin)
    (htop : 1 < c0 * amin * T0 ^ σ) (hY : -B ≤ Y 2)
    (hgap : amin < ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ)) :
    ∃ (a : ℝ) (w : R3), a = ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ) ∧ w = ‖X - Y‖⁻¹ • (X - Y) ∧
      ‖w‖ = 1 ∧ X = Y + tubeRadius M e0 a σ Y • w ∧
      (min (X 2) (Y 2) < c0 * ‖X - Y‖ ∨
        (amin < a ∧ a < 2 / c0 + 1 ∧ -B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0)) := by
  have ht1 : 1 ≤ tubeHeight M e0 Y :=
    (tube_base_height (T0 := tubeHeight M e0 Y) he0 hM (by linarith) le_rfl).1
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hDpos : 0 < ‖X - Y‖ := by
    rcases (norm_nonneg (X - Y)).lt_or_eq with h | h
    · exact h
    · have h0 : ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ) = 0 := by rw [← h, zero_div]
      linarith
  have hr : tubeRadius M e0 (‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ)) σ Y = ‖X - Y‖ := by
    rw [tubeRadius, div_mul_cancel₀ _ htp.ne']
  have hw : ‖‖X - Y‖⁻¹ • (X - Y)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hDpos.ne']
  have hX : X = Y + tubeRadius M e0 (‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ)) σ Y •
      (‖X - Y‖⁻¹ • (X - Y)) := by
    rw [hr, smul_smul, mul_inv_cancel₀ hDpos.ne', one_smul, add_sub_cancel]
  refine ⟨_, _, rfl, rfl, hw, hX, ?_⟩
  by_cases hA : 2 / c0 + 1 ≤ ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ)
  · left
    have h := tube_amax_level_in_seed hc0 (by linarith : (0 : ℝ) ≤ M) he0 ht1 hσ.le hA hw
    rwa [← hX] at h
  by_cases hT : T0 ≤ tubeHeight M e0 Y
  · left
    have hts : T0 ^ σ ≤ tubeHeight M e0 Y ^ σ := Real.rpow_le_rpow hT0.le hT hσ.le
    have hca : 0 < c0 * amin := mul_pos hc0 ham
    have h2 := mul_le_mul_of_nonneg_left hts hca.le
    have htop' : 1 < c0 * amin * tubeHeight M e0 Y ^ σ := by linarith
    have h := tube_top_face_in_seed hc0 (by linarith : (0 : ℝ) ≤ M) he0 ht ham.le hgap.le htop' hw
    rwa [← hX] at h
  · right
    exact ⟨hgap, not_le.1 hA, by linarith, not_le.1 hT⟩

/-- N68: for `a ≥ 0` and `t(Y) > 0` the strict positive side of the actual tube phase is the literal
superlevel set `a < ‖X-Y‖/t(Y)^(1+σ)` of the actual polar level. -/
theorem tube_phase_pos_iff {M e0 a σ : ℝ} {X Y : R3} (ha : 0 ≤ a) (ht : 0 < tubeHeight M e0 Y) :
    0 < tubePhase M e0 a σ (X, Y) ↔ a < ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ) := by
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hP : tubePhase M e0 a σ (X, Y) =
      (‖X - Y‖ ^ 2 - (a * tubeHeight M e0 Y ^ (1 + σ)) ^ 2) / 2 := rfl
  have hr : 0 ≤ a * tubeHeight M e0 Y ^ (1 + σ) := mul_nonneg ha htp.le
  have hD := norm_nonneg (X - Y)
  rw [hP, lt_div_iff₀ htp]
  constructor
  · intro h
    by_contra hn
    have hn' := not_lt.1 hn
    nlinarith
  · intro h
    nlinarith

/-- N69: strict outsides are nested: `0 ≤ b ≤ a` and `ρ_a > 0` give `ρ_b > 0`. -/
theorem tube_phase_pos_mono {M e0 a b σ : ℝ} {X Y : R3} (hb : 0 ≤ b) (hba : b ≤ a)
    (ht : 0 < tubeHeight M e0 Y) (h : 0 < tubePhase M e0 a σ (X, Y)) :
    0 < tubePhase M e0 b σ (X, Y) :=
  (tube_phase_pos_iff hb ht).2 (hba.trans_lt ((tube_phase_pos_iff (hb.trans hba) ht).1 h))

/-- N70: at an actual strict tube-front point, the full-cross extension continues an old-side
solution with both full crosses across the front. -/
theorem tube_front_local_extension (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (M e0 a σ : ℝ) (Y w : R3) (hw : ‖w‖ = 1)
    (U : Set (R3 × R3)) (hU : IsOpen U) (hpU : (Y + tubeRadius M e0 a σ Y • w, Y) ∈ U)
    (hroom : U ⊆ dilatedOffDiagonal S lam) (hUt : U ⊆ {z | 0 < tubeHeight M e0 z.2})
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
      (Y + tubeRadius M e0 a σ Y • w) Y (tubePhase M e0 a σ))
    (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F {z | z ∈ U ∧ 0 < tubePhase M e0 a σ z})
    (hF1 : ∀ v, v ∈ U → 0 < tubePhase M e0 a σ v → lam • v.2 ∈ S.W →
      F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v, v ∈ U → 0 < tubePhase M e0 a σ v → lam • v.1 ∈ S.W →
      F v = dilatedKernel2 S lam v) :
    ∃ (V : Set (R3 × R3)) (G : R3 × R3 → ℝ), IsOpen V ∧
      (Y + tubeRadius M e0 a σ Y • w, Y) ∈ V ∧ V ⊆ U ∧
      ProductSolutionOn S L lam G V ∧ EqOn G F (V ∩ {z | z ∈ U ∧ 0 < tubePhase M e0 a σ z}) ∧
      (∀ v ∈ V, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ V, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v) :=
  exists_product_solution_extension_with_full_crosses S L lam hlam _ _ U hU hpU hroom
    (tubePhase M e0 a σ) ((tube_phase_contDiffOn M e0 a σ).2.mono hUt)
    (tube_phase_zero M e0 a σ Y w hw) hTest F hSol hF1 hF2

/-- N71: the canonical actual tube room `dilatedOffDiagonal S λ ∩ {t(z.2) > 0} ∩ W` is open. -/
theorem tube_room_isOpen (S : KnownSideSourceData) (lam M e0 : ℝ) {W : Set (R3 × R3)}
    (hW : IsOpen W) :
    IsOpen (dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W) := by
  have h1 : IsOpen {v : R3 × R3 | lam • v.1 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage (continuous_fst.const_smul lam)
  have h2 : IsOpen {v : R3 × R3 | lam • v.2 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage (continuous_snd.const_smul lam)
  have h3 : IsOpen {v : R3 × R3 | v.1 ≠ v.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hD : IsOpen (dilatedOffDiagonal S lam) := h1.inter (h2.inter h3)
  exact (hD.inter (tube_phase_contDiffOn M e0 0 0).1).inter hW

/-- N72: N70 in the canonical actual tube room. -/
theorem tube_front_room_extension (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (M e0 a σ : ℝ) (Y w : R3) (hw : ‖w‖ = 1) {W : Set (R3 × R3)} (hW : IsOpen W)
    (hpU : (Y + tubeRadius M e0 a σ Y • w, Y) ∈
      dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
      (Y + tubeRadius M e0 a σ Y • w) Y (tubePhase M e0 a σ))
    (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F {z | z ∈ dilatedOffDiagonal S lam ∩
      {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W ∧ 0 < tubePhase M e0 a σ z})
    (hF1 : ∀ v, v ∈ dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W →
      0 < tubePhase M e0 a σ v → lam • v.2 ∈ S.W → F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v, v ∈ dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W →
      0 < tubePhase M e0 a σ v → lam • v.1 ∈ S.W → F v = dilatedKernel2 S lam v) :
    ∃ (V : Set (R3 × R3)) (G : R3 × R3 → ℝ), IsOpen V ∧
      (Y + tubeRadius M e0 a σ Y • w, Y) ∈ V ∧
      V ⊆ dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W ∧
      ProductSolutionOn S L lam G V ∧
      EqOn G F (V ∩ {z | z ∈ dilatedOffDiagonal S lam ∩
        {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ W ∧ 0 < tubePhase M e0 a σ z}) ∧
      (∀ v ∈ V, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ V, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v) :=
  tube_front_local_extension S L lam hlam M e0 a σ Y w hw _ (tube_room_isOpen S lam M e0 hW) hpU
    (fun _ hz => hz.1.1) (fun _ hz => hz.1.2) hTest F hSol hF1 hF2

/-- N73: the literal radius change between levels `c' ≤ c` is uniformly at most `(c - c') T0^(1+σ)`
on the base `t ≤ T0`. -/
theorem tube_radius_collar {M e0 c c' σ T0 : ℝ} {Y : R3} (hσ : 0 ≤ σ) (hcc : c' ≤ c)
    (ht : 0 < tubeHeight M e0 Y) (htT : tubeHeight M e0 Y ≤ T0) :
    tubeRadius M e0 c σ Y - tubeRadius M e0 c' σ Y = (c - c') * tubeHeight M e0 Y ^ (1 + σ) ∧
      tubeRadius M e0 c σ Y - tubeRadius M e0 c' σ Y ≤ (c - c') * T0 ^ (1 + σ) := by
  have he : tubeRadius M e0 c σ Y - tubeRadius M e0 c' σ Y =
      (c - c') * tubeHeight M e0 Y ^ (1 + σ) := by
    unfold tubeRadius
    ring
  refine ⟨he, ?_⟩
  rw [he]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le htT (by linarith)) (by linarith)

/-- N74: on the fixed radial ray `s ↦ Y + s • w` the strict positive side is `r_c(Y) < s`. -/
theorem tube_phase_pos_ray_iff {M e0 c σ s : ℝ} {Y w : R3} (hc : 0 ≤ c)
    (ht : 0 < tubeHeight M e0 Y) (hs : 0 ≤ s) (hw : ‖w‖ = 1) :
    0 < tubePhase M e0 c σ (Y + s • w, Y) ↔ tubeRadius M e0 c σ Y < s := by
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  rw [tube_phase_pos_iff hc ht, add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs,
    abs_of_nonneg hs, lt_div_iff₀ htp, tubeRadius]

/-- N75: far enough along any fixed radial ray, `s ≥ (2/c0+1) t(Y)^(1+σ)`, the point lies in the literal
coarse cone (N24 at the level `s / t^(1+σ)`). -/
theorem tube_ray_far_in_seed {M e0 σ c0 s : ℝ} {Y w : R3} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight M e0 Y) (hσ : 0 ≤ σ) (hw : ‖w‖ = 1)
    (hs : (2 / c0 + 1) * tubeHeight M e0 Y ^ (1 + σ) ≤ s) :
    min ((Y + s • w) 2) (Y 2) < c0 * ‖(Y + s • w) - Y‖ := by
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos (by linarith) _
  have hr : tubeRadius M e0 (s / tubeHeight M e0 Y ^ (1 + σ)) σ Y = s := by
    rw [tubeRadius, div_mul_cancel₀ _ htp.ne']
  have ha : 2 / c0 + 1 ≤ s / tubeHeight M e0 Y ^ (1 + σ) := by
    rw [le_div_iff₀ htp]
    exact hs
  have h := tube_amax_level_in_seed hc0 hM he0 ht1 hσ ha hw
  rwa [hr] at h

/-- N76: ONE `λ1 > 0` (from `S` and `R` only) puts every bounded off-diagonal pair into the literal
`dilatedOffDiagonal S λ` for all `λ ∈ (0, λ1]`. -/
theorem dilated_room_of_bounded (S : KnownSideSourceData) {R : ℝ} (hR : 0 < R) :
    ∃ lam1 : ℝ, 0 < lam1 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam1 → ∀ X Y : R3, ‖X‖ ≤ R → ‖Y‖ ≤ R →
      X ≠ Y → (X, Y) ∈ dilatedOffDiagonal S lam := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S.coordinateRoom_open 0 S.origin_mem
  refine ⟨ε / (2 * R), by positivity, fun lam hlam hle X Y hX hY hXY => ?_⟩
  have hb : ∀ Z : R3, ‖Z‖ ≤ R → lam • Z ∈ S.coordinateRoom := by
    intro Z hZ
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    have h1 : lam * ‖Z‖ ≤ ε / (2 * R) * R := mul_le_mul hle hZ (norm_nonneg _) (by positivity)
    have h2 : ε / (2 * R) * R = ε / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right ε 2 hR.ne']
    linarith
  exact ⟨hb X hX, hb Y hY, hXY⟩

/-- N77: on a compact actual sweep, ONE `λ0 > 0` gives both the actual dilated strictness and literal
`dilatedOffDiagonal S λ` membership of every front point (N65 + N76). -/
theorem exists_uniform_dilation_room_of_compact_tube_strictness
    (S : KnownSideSourceData) (M e0 σ : ℝ) (hσ : 0 ≤ σ)
    {Q : Set (ℝ × R3 × R3)} (hQ : IsCompact Q)
    (hHeight : ∀ q ∈ Q, 0 < tubeHeight M e0 q.2.1)
    (hBase : ∀ q ∈ Q,
      ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ)) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ q ∈ Q,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
        (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2) q.2.1 (tubePhase M e0 q.1 σ) ∧
      (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2, q.2.1) ∈ dilatedOffDiagonal S lam := by
  obtain ⟨l0, hl0, hS⟩ :=
    exists_uniform_dilation_of_compact_tube_strictness S M e0 σ hσ hQ hHeight hBase
  have hc : Continuous fun q : ℝ × R3 × R3 =>
      (q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2, q.2.1) :=
    (tubeEndpoint_continuous M e0 σ hσ).prodMk continuous_snd.fst
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨l1, hl1, hR⟩ := dilated_room_of_bounded S (R := max C 1)
    (lt_of_lt_of_le one_pos (le_max_right C 1))
  refine ⟨min l0 l1, lt_min hl0 hl1, fun lam hlam hle q hq => ?_⟩
  have hs := hS lam hlam (hle.trans (min_le_left _ _)) q hq
  refine ⟨hs, ?_⟩
  have hne := ((tube_scaled_strict_iff S M e0 q.1 σ lam _ _ (hHeight q hq)).1 hs).1
  have hb := hC q hq
  have hX : ‖q.2.1 + tubeRadius M e0 q.1 σ q.2.1 • q.2.2‖ ≤ max C 1 :=
    ((norm_fst_le _).trans hb).trans (le_max_left _ _)
  have hY : ‖q.2.1‖ ≤ max C 1 := ((norm_snd_le _).trans hb).trans (le_max_left _ _)
  exact hR lam hlam (hle.trans (min_le_right _ _)) _ _ hX hY (sub_ne_zero.1 hne)

/-- N78: N66 with the literal dilated room: ONE `σ, T0, e0` and ONE `λ0` give all seed/target data,
compactness, actual strictness and `dilatedOffDiagonal` membership on the sweep. -/
theorem tube_scaled_strict_room_coherent (S : KnownSideSourceData) {c0 η d B M : ℝ} (hc0 : 0 < c0)
    (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B)
    (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      (∀ (D : ℝ) (Y : R3), d ≤ D → -B - 1 ≤ Y 2 → Y 2 ≤ B → Y 0 ^ 2 + Y 1 ^ 2 ≤ B ^ 2 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) < D / tubeHeight M e0 Y ^ (1 + σ)) ∧
      IsCompact {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} ∧
      ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
        ∀ p ∈ {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
          min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
          c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
            min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)},
          ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
            (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) p.2.1 (tubePhase M e0 p.1 σ) ∧
          (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2, p.2.1) ∈ dilatedOffDiagonal S lam := by
  obtain ⟨σ, T0, e0, hσ, hση, hσ1, hT0pos, hT0, he0, he01, htgt, hS⟩ :=
    tube_native_strict_sweep_base_pos hc0 hη hη10 hc0η hd hB hM
  have hQc := tubeSweep_isCompact M e0 σ c0 B T0 (min 1 (d / (2 * (M + B + B ^ 2) ^ 2)))
    (2 / c0 + 1) hσ.le he0
  refine ⟨σ, T0, e0, hσ, hση, hσ1, hT0pos, hT0, he0, he01, htgt, hQc, ?_⟩
  refine exists_uniform_dilation_room_of_compact_tube_strictness S M e0 σ hσ.le hQc ?_ ?_
  · rintro ⟨a, Y, w⟩ ⟨-, hY2, hT, -⟩
    have h1 := (tube_base_height he0.le hM hY2 hT).1
    show 0 < tubeHeight M e0 Y
    linarith
  · rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, hsep⟩
    exact hS a Y w hw hY2 hT ha1 ha2 (not_lt.2 hsep)

/-- N79: the actual front point at level `a ≥ 0` has polar level exactly `a`. -/
theorem tube_front_level {M e0 a σ : ℝ} {Y w : R3} (ha : 0 ≤ a) (ht : 0 < tubeHeight M e0 Y)
    (hw : ‖w‖ = 1) :
    ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖ / tubeHeight M e0 Y ^ (1 + σ) = a := by
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hr : 0 ≤ tubeRadius M e0 a σ Y := mul_nonneg ha htp.le
  rw [add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hr, tubeRadius,
    mul_div_cancel_right₀ _ htp.ne']

/-- N80: from a strict-outside point at radius `s > r_c(Y)`, the SAME ray stays strictly outside for every
larger radius and reaches the literal coarse cone at some radius `s1 ≥ s`. -/
theorem tube_ray_reaches_seed {M e0 c σ c0 s : ℝ} {Y w : R3} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight M e0 Y) (hσ : 0 ≤ σ) (hw : ‖w‖ = 1) (hc : 0 ≤ c)
    (hs : tubeRadius M e0 c σ Y < s) :
    ∃ s1 : ℝ, s ≤ s1 ∧ min ((Y + s1 • w) 2) (Y 2) < c0 * ‖(Y + s1 • w) - Y‖ ∧
      ∀ s' : ℝ, s ≤ s' → 0 < tubePhase M e0 c σ (Y + s' • w, Y) := by
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have hr0 : 0 ≤ tubeRadius M e0 c σ Y := mul_nonneg hc (Real.rpow_pos_of_pos ht _).le
  refine ⟨max s ((2 / c0 + 1) * tubeHeight M e0 Y ^ (1 + σ)), le_max_left _ _,
    tube_ray_far_in_seed hc0 hM he0 ht1 hσ hw (le_max_right _ _), fun s' hss' => ?_⟩
  exact (tube_phase_pos_ray_iff hc ht (by linarith) hw).2 (by linarith)

/-- N81: every strict-outside pair has an actual continuous radial path (center fixed) inside
`strictOutside(c)`, with radius at most its endpoint radius, ending in the literal coarse cone. -/
theorem tube_ray_path_to_seed {M e0 c σ c0 : ℝ} {X Y : R3} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight M e0 Y) (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hz : 0 < tubePhase M e0 c σ (X, Y)) :
    ∃ (a b : ℝ) (f : ℝ → R3 × R3), a ≤ b ∧ ContinuousOn f (uIcc a b) ∧ f a = (X, Y) ∧
      (∀ s ∈ uIcc a b, (f s).2 = Y ∧ 0 < tubePhase M e0 c σ (f s) ∧ ‖(f s).1 - (f s).2‖ ≤ b) ∧
      min ((f b).1 2) ((f b).2 2) < c0 * ‖(f b).1 - (f b).2‖ := by
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hlev := (tube_phase_pos_iff hc ht).1 hz
  have hrD : tubeRadius M e0 c σ Y < ‖X - Y‖ := by
    rw [lt_div_iff₀ htp] at hlev
    exact hlev
  have hr0 : 0 ≤ tubeRadius M e0 c σ Y := mul_nonneg hc htp.le
  have hD : 0 < ‖X - Y‖ := hr0.trans_lt hrD
  obtain ⟨w, hwdef⟩ : ∃ w : R3, w = ‖X - Y‖⁻¹ • (X - Y) := ⟨_, rfl⟩
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']
  have hX : Y + ‖X - Y‖ • w = X := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ hD.ne', one_smul, add_sub_cancel]
  obtain ⟨s1, hs1, hseed, hpos⟩ :=
    tube_ray_reaches_seed (s := ‖X - Y‖) hc0 hM he0 ht1 hσ hw hc hrD
  refine ⟨‖X - Y‖, s1, fun s => (Y + s • w, Y), hs1, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_const.add (continuous_id.smul continuous_const)).prodMk
      continuous_const).continuousOn
  · show (Y + ‖X - Y‖ • w, Y) = (X, Y)
    rw [hX]
  · intro s hs
    rw [uIcc_of_le hs1] at hs
    have hs0 : 0 ≤ s := hD.le.trans hs.1
    refine ⟨rfl, hpos s hs.1, ?_⟩
    show ‖(Y + s • w) - Y‖ ≤ s1
    rw [add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs.2
  · exact hseed

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

open Set Metric Filter

/-- N82: the actual affine difference chart `q ↦ (q.2, q.1 - q.2)` restricted to the literal bounded
room `D` with target `Dv`. -/
def tubeDifferencePartialHomeomorph (P : Set R3) (hP : IsOpen P) (lower upper : ℝ) :
    OpenPartialHomeomorph (R3 × R3) (R3 × R3) where
  toFun q := (q.2, q.1 - q.2)
  invFun a := (a.1 + a.2, a.1)
  source := {q | q.2 ∈ P ∧ lower < ‖q.1 - q.2‖ ∧ ‖q.1 - q.2‖ < upper}
  target := {a | a.1 ∈ P ∧ lower < ‖a.2‖ ∧ ‖a.2‖ < upper}
  map_source' := fun _ hq => hq
  map_target' := by
    intro a ha
    simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using ha
  left_inv' := by
    intro q _
    ext <;> simp
  right_inv' := by
    intro a _
    ext <;> simp
  open_source := (hP.preimage continuous_snd).inter
    ((isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm).inter
      (isOpen_lt (continuous_fst.sub continuous_snd).norm continuous_const))
  open_target := (hP.preimage continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd.norm).inter
      (isOpen_lt continuous_snd.norm continuous_const))
  continuousOn_toFun := (continuous_snd.prodMk (continuous_fst.sub continuous_snd)).continuousOn
  continuousOn_invFun := ((continuous_fst.add continuous_snd).prodMk continuous_fst).continuousOn

/-- N83: the actual tube base `K = {-B-1 ≤ Y₂, t(Y) ≤ T0}` is compact for `e0 > 0`. -/
theorem tubeBase_isCompact {M e0 B T0 : ℝ} (he0 : 0 < e0) :
    IsCompact {Y : R3 | -B - 1 ≤ Y 2 ∧ tubeHeight M e0 Y ≤ T0} := by
  have hY2 : Continuous fun Y : R3 => Y 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_const hY2).inter
      (isClosed_le (st_height_continuous M e0) continuous_const)) ?_
  set C : ℝ := |B| + 1 + |T0| + |M| with hC
  set S : ℝ := Real.sqrt ((T0 - M + B + 1) / e0 + C ^ 2) with hS
  refine (Metric.isBounded_closedBall (x := (0 : R3)) (r := S)).subset ?_
  rintro Y ⟨hY2, hT⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold tubeHeight at hT
  have hs0 : 0 ≤ e0 * (Y 0 ^ 2 + Y 1 ^ 2) := by positivity
  have h1 : Y 0 ^ 2 + Y 1 ^ 2 ≤ (T0 - M + B + 1) / e0 := by
    rw [le_div_iff₀ he0]
    linarith [mul_comm e0 (Y 0 ^ 2 + Y 1 ^ 2)]
  have hT0 := le_abs_self T0
  have hM0 := neg_abs_le M
  have hT1 := abs_nonneg T0
  have hM1 := abs_nonneg M
  have hB0 := le_abs_self B
  have hB1 := abs_nonneg B
  have h2 : Y 2 ^ 2 ≤ C ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hn : ‖Y‖ = Real.sqrt (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hn, hS]
  exact Real.sqrt_le_sqrt (by linarith)

/-- N84: an OPEN bounded center room `P = {‖Y‖ < CY, 0 < t(Y)}` containing the base `K`, with `t ≥ 1` on `K`. -/
theorem tube_center_room {M e0 B T0 : ℝ} (he0 : 0 < e0) (hM : B + 3 < M) :
    ∃ CY : ℝ, 0 < CY ∧ IsOpen {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} ∧
      ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ‖Y‖ < CY ∧ 1 ≤ tubeHeight M e0 Y := by
  obtain ⟨r, hr⟩ :=
    (tubeBase_isCompact (M := M) (B := B) (T0 := T0) he0).isBounded.subset_ball (0 : R3)
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (st_height_continuous M e0)),
    fun Y hY2 hT => ⟨?_, (tube_base_height he0.le hM hY2 hT).1⟩⟩
  have h := hr ⟨hY2, hT⟩
  rw [Metric.mem_ball, dist_zero_right] at h
  exact lt_of_lt_of_le h (le_max_left _ _)

/-- N85: ONE `λ1 > 0` puts every point of the bounded room `‖Y‖ < CY`, `lower < ‖X-Y‖ < upper`
into the literal `dilatedOffDiagonal S λ` for all `λ ∈ (0, λ1]` (N76). -/
theorem tube_room_mem_dilated (S : KnownSideSourceData) {CY lower upper : ℝ} (hl : 0 ≤ lower)
    (hCY : 0 < CY) (hu : 0 < upper) :
    ∃ lam1 : ℝ, 0 < lam1 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam1 → ∀ q : R3 × R3, ‖q.2‖ < CY →
      lower < ‖q.1 - q.2‖ → ‖q.1 - q.2‖ < upper → q ∈ dilatedOffDiagonal S lam := by
  obtain ⟨lam1, hlam1, hR⟩ := dilated_room_of_bounded S (R := CY + upper) (by linarith)
  refine ⟨lam1, hlam1, fun lam hlam hle q hY hlo hup => ?_⟩
  have hX : ‖q.1‖ ≤ CY + upper := by
    have h := norm_add_le (q.1 - q.2) q.2
    rw [sub_add_cancel] at h
    linarith
  have hne : q.1 ≠ q.2 := by
    intro h
    rw [h, sub_self, norm_zero] at hlo
    linarith
  exact hR lam hlam hle q.1 q.2 hX (by linarith) hne

/-- N86: from a strict-outside point of the bounded room (center `Y ∈ P`, `1 ≤ t(Y) ≤ T0`,
`lower < ‖X-Y‖ < upper`), the actual radial path to the coarse cone stays inside the room and outside. -/
theorem tube_ray_path_in_room {M e0 c σ c0 T0 lower upper : ℝ} {P : Set R3} {X Y : R3}
    (hc0 : 0 < c0) (hM : 0 ≤ M) (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight M e0 Y)
    (htT : tubeHeight M e0 Y ≤ T0) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper) (hY : Y ∈ P) (hlo : lower < ‖X - Y‖)
    (hhi : ‖X - Y‖ < upper) (hz : 0 < tubePhase M e0 c σ (X, Y)) :
    ∃ (a b : ℝ) (f : ℝ → R3 × R3), a ≤ b ∧ ContinuousOn f (uIcc a b) ∧ f a = (X, Y) ∧
      (∀ s ∈ uIcc a b, (f s).2 = Y ∧ 0 < tubePhase M e0 c σ (f s) ∧ (f s).2 ∈ P ∧
        lower < ‖(f s).1 - (f s).2‖ ∧ ‖(f s).1 - (f s).2‖ < upper) ∧
      min ((f b).1 2) ((f b).2 2) < c0 * ‖(f b).1 - (f b).2‖ := by
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hlev := (tube_phase_pos_iff hc ht).1 hz
  have hrD : tubeRadius M e0 c σ Y < ‖X - Y‖ := by
    rw [lt_div_iff₀ htp] at hlev
    exact hlev
  have hr0 : 0 ≤ tubeRadius M e0 c σ Y := mul_nonneg hc htp.le
  have hD : 0 < ‖X - Y‖ := hr0.trans_lt hrD
  obtain ⟨w, hwdef⟩ : ∃ w : R3, w = ‖X - Y‖⁻¹ • (X - Y) := ⟨_, rfl⟩
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']
  have hX : Y + ‖X - Y‖ • w = X := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ hD.ne', one_smul, add_sub_cancel]
  have hmax1 : (1 : ℝ) ≤ max 1 T0 := le_max_left _ _
  have hpow : tubeHeight M e0 Y ^ (1 + σ) ≤ max 1 T0 ^ (2 : ℕ) := by
    calc tubeHeight M e0 Y ^ (1 + σ) ≤ max 1 T0 ^ (1 + σ) :=
          Real.rpow_le_rpow ht.le (htT.trans (le_max_right _ _)) (by linarith)
      _ ≤ max 1 T0 ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmax1 (by norm_num; linarith)
      _ = max 1 T0 ^ (2 : ℕ) := Real.rpow_natCast _ _
  have hc1 : 0 < 2 / c0 + 1 := by positivity
  have hfar : (2 / c0 + 1) * tubeHeight M e0 Y ^ (1 + σ) < upper :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow hc1.le) hup
  have hs1 : max ‖X - Y‖ ((2 / c0 + 1) * tubeHeight M e0 Y ^ (1 + σ)) < upper :=
    max_lt hhi hfar
  refine ⟨‖X - Y‖, max ‖X - Y‖ ((2 / c0 + 1) * tubeHeight M e0 Y ^ (1 + σ)),
    fun s => (Y + s • w, Y), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_const.add (continuous_id.smul continuous_const)).prodMk
      continuous_const).continuousOn
  · show (Y + ‖X - Y‖ • w, Y) = (X, Y)
    rw [hX]
  · intro s hs
    rw [uIcc_of_le (le_max_left _ _)] at hs
    have hs0 : 0 ≤ s := hD.le.trans hs.1
    have hn : ‖(Y + s • w) - Y‖ = s := by
      rw [add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hs0]
    refine ⟨rfl, (tube_phase_pos_ray_iff hc ht hs0 hw).2 (by linarith [hs.1]), hY, ?_, ?_⟩
    · show lower < ‖(Y + s • w) - Y‖
      rw [hn]
      linarith [hs.1]
    · show ‖(Y + s • w) - Y‖ < upper
      rw [hn]
      linarith [hs.2]
  · exact tube_ray_far_in_seed hc0 hM he0 ht1 hσ hw (le_max_right _ _)

/-- N87a: the literal bounded room `D`. -/
def tubeChartRoom (P : Set R3) (lower upper : ℝ) : Set (R3 × R3) :=
  {q | q.2 ∈ P ∧ lower < ‖q.1 - q.2‖ ∧ ‖q.1 - q.2‖ < upper}

/-- N87b: the literal coarse cone `A` inside `D`. -/
def tubeSeedRoom (P : Set R3) (lower upper c0 : ℝ) : Set (R3 × R3) :=
  {q | q ∈ tubeChartRoom P lower upper ∧ min (q.1 2) (q.2 2) < c0 * ‖q.1 - q.2‖}

/-- N87c: the strict outside of level `c` over the interior of the base `K`, inside `D`. -/
def tubeOutsideRoom (M e0 c σ B T0 : ℝ) (P : Set R3) (lower upper : ℝ) : Set (R3 × R3) :=
  {q | q ∈ tubeChartRoom P lower upper ∧ (-B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0) ∧
    0 < tubePhase M e0 c σ q}

/-- N87d: the canonical domain `A ∪ outside(c)`. -/
def tubeCanonicalRoom (M e0 c σ B T0 : ℝ) (P : Set R3) (lower upper c0 : ℝ) : Set (R3 × R3) :=
  tubeSeedRoom P lower upper c0 ∪ tubeOutsideRoom M e0 c σ B T0 P lower upper

theorem tubeChartRoom_isOpen {P : Set R3} (hP : IsOpen P) (lower upper : ℝ) :
    IsOpen (tubeChartRoom P lower upper) :=
  (hP.preimage continuous_snd).inter
    ((isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm).inter
      (isOpen_lt (continuous_fst.sub continuous_snd).norm continuous_const))

theorem tubeSeedRoom_isOpen {P : Set R3} (hP : IsOpen P) (lower upper c0 : ℝ) :
    IsOpen (tubeSeedRoom P lower upper c0) := by
  have h2 : Continuous fun Z : R3 => Z 2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  exact (tubeChartRoom_isOpen hP lower upper).inter
    (isOpen_lt ((h2.comp continuous_fst).min (h2.comp continuous_snd))
      (continuous_const.mul (continuous_fst.sub continuous_snd).norm))

theorem tubeOutsideRoom_isOpen {M e0 c σ B T0 : ℝ} {P : Set R3} (hP : IsOpen P) (lower upper : ℝ)
    (he0 : 0 ≤ e0) (hM : B + 3 < M) :
    IsOpen (tubeOutsideRoom M e0 c σ B T0 P lower upper) := by
  have h2 : Continuous fun q : R3 × R3 => q.2 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_snd
  have hK : IsOpen {q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0} :=
    (isOpen_lt continuous_const h2).inter
      (isOpen_lt ((st_height_continuous M e0).comp continuous_snd) continuous_const)
  have hpos := (tube_phase_contDiffOn M e0 c σ).2.continuousOn.isOpen_inter_preimage
    (tube_phase_contDiffOn M e0 c σ).1 (isOpen_Ioi (a := (0 : ℝ)))
  have he : tubeOutsideRoom M e0 c σ B T0 P lower upper = tubeChartRoom P lower upper ∩
      ({q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0} ∩
        ({z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ tubePhase M e0 c σ ⁻¹' Ioi 0)) := by
    ext q
    constructor
    · rintro ⟨h1, hk, h3⟩
      have hb := (tube_base_height he0 hM hk.1.le hk.2.le).1
      exact ⟨h1, hk, ⟨show 0 < tubeHeight M e0 q.2 by linarith, h3⟩⟩
    · rintro ⟨h1, hk, -, h3⟩
      exact ⟨h1, hk, h3⟩
  rw [he]
  exact (tubeChartRoom_isOpen hP lower upper).inter (hK.inter hpos)

/-- N87: PROVED compatibility on the canonical domain: two actual product solutions on
`A ∪ outside(c)` agreeing on the coarse cone `A` agree on the whole canonical domain. -/
theorem tube_canonical_eqOn (S : KnownSideSourceData) (L lam : ℝ)
    {M e0 c σ c0 B T0 lower upper : ℝ} {P : Set R3} (hP : IsOpen P) (hc0 : 0 < c0)
    (hB : 0 ≤ B) (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper) {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0))
    (hG : ProductSolutionOn S L lam G (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0))
    (heq : EqOn F G (tubeSeedRoom P lower upper c0)) :
    EqOn F G (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0) := by
  apply native_product_eq_of_interval_seed S L lam
    ((tubeSeedRoom_isOpen hP lower upper c0).union (tubeOutsideRoom_isOpen hP lower upper he0 hM))
    (tubeSeedRoom_isOpen hP lower upper c0) (fun q hq => Or.inl hq) hF hG heq
  intro z hz
  rcases hz with hzA | hzO
  · exact ⟨0, 0, fun _ => z, continuousOn_const, rfl, fun _ _ => Or.inl hzA, hzA⟩
  · obtain ⟨⟨hY, hlo, hhi⟩, ⟨hY2, hT⟩, hph⟩ := hzO
    have hb := tube_base_height he0 hM hY2.le hT.le
    obtain ⟨a, b, f, hab, hf, hfa, hs, hseed⟩ :=
      tube_ray_path_in_room (P := P) (X := z.1) (Y := z.2) hc0 (by linarith) he0 hb.1 hT.le hσ
        hσ1 hc hup hY hlo hhi hph
    refine ⟨a, b, f, hf, hfa, fun s hs' => ?_, ?_⟩
    · obtain ⟨h2, hpos, hP', hlo', hhi'⟩ := hs s hs'
      refine Or.inr ⟨⟨hP', hlo', hhi'⟩, ⟨?_, ?_⟩, hpos⟩
      · rw [h2]
        exact hY2
      · rw [h2]
        exact hT
    · obtain ⟨-, -, hP', hlo', hhi'⟩ := hs b right_mem_uIcc
      exact ⟨⟨hP', hlo', hhi'⟩, hseed⟩

/-- N88: every actual front point at a level `a ∈ [amin, amax]` over the base lies in the room `D`. -/
theorem tube_front_in_room {M e0 a σ amin amax T0 lower upper : ℝ} {P : Set R3} {Y w : R3}
    (hamin : 0 < amin) (hlo : lower < amin) (hup : amax * max 1 T0 ^ 2 < upper)
    (ha1 : amin ≤ a) (ha2 : a ≤ amax) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht1 : 1 ≤ tubeHeight M e0 Y) (htT : tubeHeight M e0 Y ≤ T0) (hY : Y ∈ P) (hw : ‖w‖ = 1) :
    (Y + tubeRadius M e0 a σ Y • w, Y) ∈ tubeChartRoom P lower upper := by
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have hlev := tube_front_level (a := a) (σ := σ) (w := w) (by linarith) ht hw
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hn : ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖ = a * tubeHeight M e0 Y ^ (1 + σ) := by
    rw [div_eq_iff htp.ne'] at hlev
    exact hlev
  have h1 : 1 ≤ tubeHeight M e0 Y ^ (1 + σ) := Real.one_le_rpow ht1 (by linarith)
  have hmax1 : (1 : ℝ) ≤ max 1 T0 := le_max_left _ _
  have hpow : tubeHeight M e0 Y ^ (1 + σ) ≤ max 1 T0 ^ (2 : ℕ) := by
    calc tubeHeight M e0 Y ^ (1 + σ) ≤ max 1 T0 ^ (1 + σ) :=
          Real.rpow_le_rpow ht.le (htT.trans (le_max_right _ _)) (by linarith)
      _ ≤ max 1 T0 ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmax1 (by norm_num; linarith)
      _ = max 1 T0 ^ (2 : ℕ) := Real.rpow_natCast _ _
  have ha0 : 0 < a := lt_of_lt_of_le hamin ha1
  refine ⟨hY, ?_, ?_⟩
  · show lower < ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖
    rw [hn]
    nlinarith
  · show ‖(Y + tubeRadius M e0 a σ Y • w) - Y‖ < upper
    rw [hn]
    have h2 : a * tubeHeight M e0 Y ^ (1 + σ) ≤ amax * max 1 T0 ^ (2 : ℕ) :=
      mul_le_mul ha2 hpow htp.le (by linarith)
    linarith

/-- N89: the genuine `uniform_common_coarse_seed_RF` kernel restricts to the exact cone `A` of the
bounded room, with its literal PDEs and BOTH entire full crosses. -/
theorem tube_seed_restrict (S : KnownSideSourceData) (L lam : ℝ) {U : Set (R3 × R3)}
    {H : R3 × R3 → ℝ} {M e0 c0 Bs ds CY lower upper : ℝ}
    (hSol : ProductSolutionOn S L lam H U)
    (hH1 : ∀ v ∈ U, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ U, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v)
    (hcov : ∀ x y : R3, ‖x‖ ≤ Bs → ‖y‖ ≤ Bs → ds ≤ ‖x - y‖ →
      min (x 2) (y 2) < c0 * ‖x - y‖ → (x, y) ∈ U)
    (hBs : CY + upper ≤ Bs) (hds : ds ≤ lower) :
    tubeSeedRoom {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper c0 ⊆ U ∧
      ProductSolutionOn S L lam H
        (tubeSeedRoom {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper c0) ∧
      (∀ v ∈ tubeSeedRoom {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper c0,
        lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ tubeSeedRoom {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper c0,
        lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) := by
  have hsub : tubeSeedRoom {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y} lower upper c0 ⊆ U := by
    intro q hq
    obtain ⟨⟨⟨hy, -⟩, hlo, hhi⟩, hcone⟩ := hq
    have hn0 := norm_nonneg (q.1 - q.2)
    have hx : ‖q.1‖ ≤ ‖q.1 - q.2‖ + ‖q.2‖ := by
      have h := norm_add_le (q.1 - q.2) q.2
      rwa [sub_add_cancel] at h
    exact hcov q.1 q.2 (by linarith) (by linarith) (by linarith) hcone
  exact ⟨hsub, ⟨hSol.1.mono hsub, fun v hv => hSol.2.1 v (hsub hv),
    fun v hv => hSol.2.2 v (hsub hv)⟩, fun v hv => hH1 v (hsub hv), fun v hv => hH2 v (hsub hv)⟩

/-- N90a: the outside rooms are nested in the level. -/
theorem tubeOutsideRoom_mono {M e0 a b σ B T0 lower upper : ℝ} {P : Set R3} (hb : 0 ≤ b)
    (hba : b ≤ a) (he0 : 0 ≤ e0) (hM : B + 3 < M) :
    tubeOutsideRoom M e0 a σ B T0 P lower upper ⊆ tubeOutsideRoom M e0 b σ B T0 P lower upper := by
  intro q hq
  obtain ⟨h1, hk, hph⟩ := hq
  have ht := (tube_base_height he0 hM hk.1.le hk.2.le).1
  exact ⟨h1, hk, tube_phase_pos_mono (X := q.1) (Y := q.2) hb hba (by linarith) hph⟩

/-- N90b: the canonical rooms are nested in the level. -/
theorem tubeCanonicalRoom_mono {M e0 a b σ B T0 lower upper c0 : ℝ} {P : Set R3} (hb : 0 ≤ b)
    (hba : b ≤ a) (he0 : 0 ≤ e0) (hM : B + 3 < M) :
    tubeCanonicalRoom M e0 a σ B T0 P lower upper c0 ⊆
      tubeCanonicalRoom M e0 b σ B T0 P lower upper c0 :=
  Set.union_subset_union_right _ (tubeOutsideRoom_mono hb hba he0 hM)

/-- N91: N67 in room form: a gap target is in the literal coarse cone or in `outside(amin)`. -/
theorem tube_target_in_room {M e0 σ c0 B T0 amin lower upper CY : ℝ} {X Y : R3} (hc0 : 0 < c0)
    (hσ : 0 < σ) (he0 : 0 ≤ e0) (hB : 0 ≤ B) (hM : B + 3 < M) (hT0 : 0 < T0) (ham : 0 < amin)
    (htop : 1 < c0 * amin * T0 ^ σ) (hY : -B ≤ Y 2)
    (hgap : amin < ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ))
    (hK : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ‖Y‖ < CY)
    (hlo : lower < ‖X - Y‖) (hhi : ‖X - Y‖ < upper) :
    min (X 2) (Y 2) < c0 * ‖X - Y‖ ∨
      (X, Y) ∈ tubeOutsideRoom M e0 amin σ B T0 {Y : R3 | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y}
        lower upper := by
  obtain ⟨a, w, -, -, -, -, hcase⟩ :=
    tube_target_cover hc0 hσ he0 hB hM hT0 ham htop hY hgap
  rcases hcase with h | ⟨-, -, hY2, hT⟩
  · exact Or.inl h
  · have ht1 := (tube_base_height he0 hM hY2.le hT.le).1
    have ht : 0 < tubeHeight M e0 Y := by linarith
    exact Or.inr ⟨⟨⟨hK Y hY2.le hT.le, ht⟩, hlo, hhi⟩, ⟨hY2, hT⟩,
      (tube_phase_pos_iff ham.le ht).2 hgap⟩

/-- N92: reached kernels on every `canonical(b)`, `b > c`, all equal to the SAME seed kernel on `A`,
glue (by PROVED compatibility N87) to ONE actual product solution on `canonical(c)`. -/
theorem tube_reached_glue (S : KnownSideSourceData) (L lam : ℝ)
    {M e0 c σ c0 B T0 lower upper : ℝ} {P : Set R3} (hP : IsOpen P) (hc0 : 0 < c0)
    (hB : 0 ≤ B) (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper) {H0 : R3 × R3 → ℝ}
    (F : {b : ℝ // c < b} → R3 × R3 → ℝ)
    (hF : ∀ b : {b : ℝ // c < b},
      ProductSolutionOn S L lam (F b) (tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0))
    (hFA : ∀ b : {b : ℝ // c < b}, EqOn (F b) H0 (tubeSeedRoom P lower upper c0)) :
    ∃ G : R3 × R3 → ℝ,
      ProductSolutionOn S L lam G (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0) ∧
      EqOn G H0 (tubeSeedRoom P lower upper c0) ∧
      ∀ b : {b : ℝ // c < b}, EqOn G (F b) (tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0) := by
  have hopen : ∀ b : {b : ℝ // c < b},
      IsOpen (tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0) := fun b =>
    (tubeSeedRoom_isOpen hP _ _ _).union (tubeOutsideRoom_isOpen hP _ _ he0 hM)
  have key : ∀ i j : {b : ℝ // c < b}, i.1 ≤ j.1 →
      EqOn (F i) (F j) (tubeCanonicalRoom M e0 i.1 σ B T0 P lower upper c0 ∩
        tubeCanonicalRoom M e0 j.1 σ B T0 P lower upper c0) := by
    intro i j hij z hz
    have hi0 : 0 ≤ i.1 := by linarith [i.2]
    have hsub : tubeCanonicalRoom M e0 j.1 σ B T0 P lower upper c0 ⊆
        tubeCanonicalRoom M e0 i.1 σ B T0 P lower upper c0 :=
      tubeCanonicalRoom_mono hi0 hij he0 hM
    have hFi : ProductSolutionOn S L lam (F i)
        (tubeCanonicalRoom M e0 j.1 σ B T0 P lower upper c0) :=
      ⟨(hF i).1.mono hsub, fun v hv => (hF i).2.1 v (hsub hv),
        fun v hv => (hF i).2.2 v (hsub hv)⟩
    have hAeq : EqOn (F i) (F j) (tubeSeedRoom P lower upper c0) :=
      fun v hv => (hFA i hv).trans (hFA j hv).symm
    exact tube_canonical_eqOn S L lam hP hc0 hB hM he0 hσ hσ1 (hi0.trans hij) hup hFi (hF j) hAeq
      hz.2
  have hcompat : ∀ i j : {b : ℝ // c < b},
      EqOn (F i) (F j) (tubeCanonicalRoom M e0 i.1 σ B T0 P lower upper c0 ∩
        tubeCanonicalRoom M e0 j.1 σ B T0 P lower upper c0) := by
    intro i j
    rcases le_total i.1 j.1 with h | h
    · exact key i j h
    · intro z hz
      exact (key j i h ⟨hz.2, hz.1⟩).symm
  obtain ⟨G, hG, hGF⟩ := exists_productSolutionOn_iUnion S L lam
    (fun b : {b : ℝ // c < b} => tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0) hopen F hF
    hcompat
  have hsub : tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆
      ⋃ b : {b : ℝ // c < b}, tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0 := by
    intro z hz
    rcases hz with hA | hO
    · exact Set.mem_iUnion.2 ⟨⟨c + 1, by linarith⟩, Or.inl hA⟩
    · obtain ⟨h1, hk, hph⟩ := hO
      have ht := (tube_base_height he0 hM hk.1.le hk.2.le).1
      have htpos : 0 < tubeHeight M e0 z.2 := by linarith
      have hlev := (tube_phase_pos_iff (X := z.1) (Y := z.2) hc htpos).1 hph
      obtain ⟨lv, hlv⟩ : ∃ lv : ℝ, lv = ‖z.1 - z.2‖ / tubeHeight M e0 z.2 ^ (1 + σ) := ⟨_, rfl⟩
      rw [← hlv] at hlev
      refine Set.mem_iUnion.2 ⟨⟨(c + lv) / 2, by linarith⟩, Or.inr ⟨h1, hk, ?_⟩⟩
      refine (tube_phase_pos_iff (X := z.1) (Y := z.2) (by linarith) htpos).2 ?_
      rw [← hlv]
      linarith
  refine ⟨G, ⟨hG.1.mono hsub, fun v hv => hG.2.1 v (hsub hv), fun v hv => hG.2.2 v (hsub hv)⟩,
    fun z hz => ?_, hGF⟩
  have b0 : {b : ℝ // c < b} := ⟨c + 1, by linarith⟩
  exact (hGF b0 (Or.inl hz)).trans (hFA b0 hz)

/-- N93: at every top level `a ≥ 2/c0 + 1` the outside room lies in the coarse cone `A`. -/
theorem tubeOutsideRoom_top_subset {M e0 a σ c0 B T0 lower upper : ℝ} {P : Set R3}
    (hc0 : 0 < c0) (hB : 0 ≤ B) (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ)
    (ha : 2 / c0 + 1 ≤ a) :
    tubeOutsideRoom M e0 a σ B T0 P lower upper ⊆ tubeSeedRoom P lower upper c0 := by
  intro q hq
  obtain ⟨h1, hk, hph⟩ := hq
  have ht1 := (tube_base_height he0 hM hk.1.le hk.2.le).1
  have ht : 0 < tubeHeight M e0 q.2 := by linarith
  have htp : 0 < tubeHeight M e0 q.2 ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have hc1 : 0 < 2 / c0 + 1 := by positivity
  have hlev := (tube_phase_pos_iff (X := q.1) (Y := q.2) (hc1.le.trans ha) ht).1 hph
  rw [lt_div_iff₀ htp] at hlev
  have hfar : (2 / c0 + 1) * tubeHeight M e0 q.2 ^ (1 + σ) ≤ ‖q.1 - q.2‖ := by
    have := mul_le_mul_of_nonneg_right ha htp.le
    linarith
  have hD : 0 < ‖q.1 - q.2‖ := lt_of_lt_of_le (mul_pos hc1 htp) hfar
  obtain ⟨w, hwdef⟩ : ∃ w : R3, w = ‖q.1 - q.2‖⁻¹ • (q.1 - q.2) := ⟨_, rfl⟩
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']
  have hX : q.2 + ‖q.1 - q.2‖ • w = q.1 := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ hD.ne', one_smul, add_sub_cancel]
  have h := tube_ray_far_in_seed hc0 (by linarith) he0 ht1 hσ hw hfar
  rw [hX] at h
  exact ⟨h1, h⟩

/-- N94: the reached property at level `c`: an actual product solution on `canonical(c)` equal to the
seed kernel `H0` on `A`, with BOTH entire full crosses. -/
def TubeReached (S : KnownSideSourceData) (L lam M e0 c σ B T0 : ℝ) (P : Set R3)
    (lower upper c0 : ℝ) (H0 : R3 × R3 → ℝ) : Prop :=
  ∃ G : R3 × R3 → ℝ,
    ProductSolutionOn S L lam G (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0) ∧
    EqOn G H0 (tubeSeedRoom P lower upper c0) ∧
    (∀ v ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0, lam • v.2 ∈ S.W →
      G v = dilatedKernel1 S lam v) ∧
    (∀ v ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0, lam • v.1 ∈ S.W →
      G v = dilatedKernel2 S lam v)

/-- N94a: `canonical(c)` is covered by the canonical rooms of strictly larger levels. -/
theorem tubeCanonicalRoom_subset_iUnion {M e0 c σ B T0 lower upper c0 : ℝ} {P : Set R3}
    (hM : B + 3 < M) (he0 : 0 ≤ e0) (hc : 0 ≤ c) :
    tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆
      ⋃ b : {b : ℝ // c < b}, tubeCanonicalRoom M e0 b.1 σ B T0 P lower upper c0 := by
  intro z hz
  rcases hz with hA | hO
  · exact Set.mem_iUnion.2 ⟨⟨c + 1, by linarith⟩, Or.inl hA⟩
  · obtain ⟨h1, hk, hph⟩ := hO
    have ht := (tube_base_height he0 hM hk.1.le hk.2.le).1
    have htpos : 0 < tubeHeight M e0 z.2 := by linarith
    have hlev := (tube_phase_pos_iff (X := z.1) (Y := z.2) hc htpos).1 hph
    obtain ⟨lv, hlv⟩ : ∃ lv : ℝ, lv = ‖z.1 - z.2‖ / tubeHeight M e0 z.2 ^ (1 + σ) := ⟨_, rfl⟩
    rw [← hlv] at hlev
    refine Set.mem_iUnion.2 ⟨⟨(c + lv) / 2, by linarith⟩, Or.inr ⟨h1, hk, ?_⟩⟩
    refine (tube_phase_pos_iff (X := z.1) (Y := z.2) (by linarith) htpos).2 ?_
    rw [← hlv]
    linarith

/-- N94b: every top level `a ≥ 2/c0 + 1` is reached by the restricted seed kernel itself. -/
theorem tube_reached_top (S : KnownSideSourceData) (L lam : ℝ)
    {M e0 a σ c0 B T0 lower upper : ℝ} {P : Set R3} (hc0 : 0 < c0) (hB : 0 ≤ B)
    (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ) (ha : 2 / c0 + 1 ≤ a) {H0 : R3 × R3 → ℝ}
    (hH0 : ProductSolutionOn S L lam H0 (tubeSeedRoom P lower upper c0))
    (hH1 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.2 ∈ S.W → H0 v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.1 ∈ S.W → H0 v = dilatedKernel2 S lam v) :
    TubeReached S L lam M e0 a σ B T0 P lower upper c0 H0 := by
  have hsub : tubeCanonicalRoom M e0 a σ B T0 P lower upper c0 ⊆ tubeSeedRoom P lower upper c0 :=
    Set.union_subset subset_rfl (tubeOutsideRoom_top_subset hc0 hB hM he0 hσ ha)
  unfold TubeReached
  exact ⟨H0, ⟨hH0.1.mono hsub, fun v hv => hH0.2.1 v (hsub hv), fun v hv => hH0.2.2 v (hsub hv)⟩,
    fun _ _ => rfl, fun v hv => hH1 v (hsub hv), fun v hv => hH2 v (hsub hv)⟩

/-- N94c: the limit step: reached at every level `b > c` gives reached at `c` (N92 + N94a). -/
theorem tube_reached_limit (S : KnownSideSourceData) (L lam : ℝ)
    {M e0 c σ c0 B T0 lower upper : ℝ} {P : Set R3} (hP : IsOpen P) (hc0 : 0 < c0)
    (hB : 0 ≤ B) (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper) {H0 : R3 × R3 → ℝ}
    (h : ∀ b : ℝ, c < b → TubeReached S L lam M e0 b σ B T0 P lower upper c0 H0) :
    TubeReached S L lam M e0 c σ B T0 P lower upper c0 H0 := by
  unfold TubeReached at h
  choose F hF hFA hF1 hF2 using fun b : {b : ℝ // c < b} => h b.1 b.2
  obtain ⟨G, hG, hGA, hGF⟩ := tube_reached_glue S L lam hP hc0 hB hM he0 hσ hσ1 hc hup F hF hFA
  have hcov := tubeCanonicalRoom_subset_iUnion (σ := σ) (T0 := T0) (P := P) (lower := lower)
    (upper := upper) (c0 := c0) hM he0 hc
  unfold TubeReached
  refine ⟨G, hG, hGA, fun v hv hW => ?_, fun v hv hW => ?_⟩
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov hv)
    rw [hGF b hb]
    exact hF1 b v hb hW
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov hv)
    rw [hGF b hb]
    exact hF2 b v hb hW

/-- N95a: generic downward real induction: top levels, the limit step and a front step give every
level `≥ amin`. -/
theorem real_downward_induction {R : ℝ → Prop} {amin amax : ℝ} (htop : ∀ b, amax ≤ b → R b)
    (hlim : ∀ c, amin ≤ c → (∀ b, c < b → R b) → R c)
    (hstep : ∀ c, amin < c → c ≤ amax → R c → ∃ ε > 0, ∀ c', c - ε < c' → c' ≤ c → R c') :
    ∀ c, amin ≤ c → R c := by
  intro c hc
  by_contra hRc
  have hne : ({x : ℝ | amin ≤ x ∧ ¬ R x}).Nonempty := ⟨c, hc, hRc⟩
  have hub : ∀ x ∈ {x : ℝ | amin ≤ x ∧ ¬ R x}, x ≤ amax := by
    intro x hx
    by_contra h
    exact hx.2 (htop x (le_of_lt (not_le.1 h)))
  have hbdd : BddAbove {x : ℝ | amin ≤ x ∧ ¬ R x} := ⟨amax, hub⟩
  have hcs : c ≤ sSup {x : ℝ | amin ≤ x ∧ ¬ R x} := le_csSup hbdd ⟨hc, hRc⟩
  have hsup : ∀ b, sSup {x : ℝ | amin ≤ x ∧ ¬ R x} < b → R b := by
    intro b hb
    by_contra hR
    exact absurd (le_csSup hbdd ⟨by linarith, hR⟩) (not_le.2 hb)
  have hRs := hlim _ (hc.trans hcs) hsup
  have hsa : sSup {x : ℝ | amin ≤ x ∧ ¬ R x} ≤ amax := csSup_le hne hub
  rcases eq_or_lt_of_le (hc.trans hcs) with heq | hlt
  · have hcs' : c = sSup {x : ℝ | amin ≤ x ∧ ¬ R x} := le_antisymm hcs (heq ▸ hc)
    exact hRc (hcs' ▸ hRs)
  · obtain ⟨ε, hε, hloc⟩ := hstep _ hlt hsa hRs
    have hle : sSup {x : ℝ | amin ≤ x ∧ ¬ R x} ≤ sSup {x : ℝ | amin ≤ x ∧ ¬ R x} - ε / 2 := by
      refine csSup_le hne fun x hx => ?_
      by_contra hx'
      exact hx.2 (hloc x (by linarith [not_le.1 hx']) (le_csSup hbdd hx))
    linarith

/-- N95b: with the top (N94b) and limit (N94c) steps, `TubeReached amin` follows from the FRONT STEP
alone, taken here as an explicit hypothesis (N108 proves it). -/
theorem tube_reached_all (S : KnownSideSourceData) (L lam : ℝ)
    {M e0 σ c0 B T0 lower upper amin : ℝ} {P : Set R3} (hP : IsOpen P) (hc0 : 0 < c0)
    (hB : 0 ≤ B) (hM : B + 3 < M) (he0 : 0 ≤ e0) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hamin : 0 ≤ amin)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper) {H0 : R3 × R3 → ℝ}
    (hH0 : ProductSolutionOn S L lam H0 (tubeSeedRoom P lower upper c0))
    (hH1 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.2 ∈ S.W → H0 v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.1 ∈ S.W → H0 v = dilatedKernel2 S lam v)
    (hstep : ∀ c, amin < c → c ≤ 2 / c0 + 1 →
      TubeReached S L lam M e0 c σ B T0 P lower upper c0 H0 → ∃ ε > 0, ∀ c', c - ε < c' →
        c' ≤ c → TubeReached S L lam M e0 c' σ B T0 P lower upper c0 H0) :
    TubeReached S L lam M e0 amin σ B T0 P lower upper c0 H0 :=
  real_downward_induction (R := fun c => TubeReached S L lam M e0 c σ B T0 P lower upper c0 H0)
    (amax := 2 / c0 + 1)
    (fun b hb => tube_reached_top S L lam hc0 hB hM he0 hσ hb hH0 hH1 hH2)
    (fun c hc h => tube_reached_limit S L lam hP hc0 hB hM he0 hσ hσ1 (hamin.trans hc) hup h)
    hstep amin le_rfl

/-- N96: the explicit room constants `amin`, `lower = amin/4`, `upper = (2/c0+1)(max 1 T0)^2 + 2B + 3`
satisfy every numerical hypothesis of N86-N95 and the target margins `lower < d`, `2B < upper`. -/
theorem tube_room_constants {c0 d B M T0 : ℝ} (hc0 : 0 < c0) (hd : 0 < d) (hB : 0 ≤ B)
    (hM : B + 3 < M) :
    0 < min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ∧
      min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) / 4 < min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ∧
      0 < min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) / 4 ∧
      min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) / 4 < d ∧
      (2 / c0 + 1) * max 1 T0 ^ 2 < (2 / c0 + 1) * max 1 T0 ^ 2 + 2 * B + 3 ∧
      2 * B < (2 / c0 + 1) * max 1 T0 ^ 2 + 2 * B + 3 := by
  have hU : 1 ≤ M + B + B ^ 2 := by nlinarith [sq_nonneg B]
  have hU2 : 2 ≤ 2 * (M + B + B ^ 2) ^ 2 := by nlinarith
  have hpos : 0 < d / (2 * (M + B + B ^ 2) ^ 2) := by positivity
  have ham : 0 < min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) := lt_min one_pos hpos
  have hle : min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ d / 2 :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_left hd.le (by norm_num) hU2)
  have hsq : 0 ≤ (2 / c0 + 1) * max 1 T0 ^ 2 := by positivity
  refine ⟨ham, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- N97: the actual polar chart of the bounded room (difference chart, then the unit-sphere
radial chart, then reassociation). -/
def tubePolarChart (P : Set R3) (hP : IsOpen P) (lower upper : ℝ) :
    OpenPartialHomeomorph (R3 × R3) ((R3 × sphere (0 : R3) 1) × ℝ) :=
  ((tubeDifferencePartialHomeomorph P hP lower upper).trans
    ((OpenPartialHomeomorph.refl R3).prod unitSphereRadialPartialHomeomorph)).transHomeomorph
      (Homeomorph.prodAssoc R3 (sphere (0 : R3) 1) ℝ).symm

/-- N97a: for `0 ≤ lower` the polar chart source is EXACTLY the room `D`. -/
theorem tubePolarChart_source {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower) :
    (tubePolarChart P hP lower upper).source = tubeChartRoom P lower upper := by
  ext q
  constructor
  · intro hq
    have h' : q ∈ (tubeDifferencePartialHomeomorph P hP lower upper).source ∩
        (tubeDifferencePartialHomeomorph P hP lower upper) ⁻¹'
          ((OpenPartialHomeomorph.refl R3).prod unitSphereRadialPartialHomeomorph).source := hq
    exact h'.1
  · intro hq
    have h2 : (q.2, q.1 - q.2) ∈
        ((OpenPartialHomeomorph.refl R3).prod unitSphereRadialPartialHomeomorph).source := by
      rw [OpenPartialHomeomorph.prod_source, unitSphereRadialPartialHomeomorph_source]
      refine ⟨Set.mem_univ _, ?_⟩
      intro h
      have h0 : q.1 - q.2 = 0 := h
      have hlo := hq.2.1
      rw [h0, norm_zero] at hlo
      linarith
    show q ∈ (tubeDifferencePartialHomeomorph P hP lower upper).source ∩
        (tubeDifferencePartialHomeomorph P hP lower upper) ⁻¹'
          ((OpenPartialHomeomorph.refl R3).prod unitSphereRadialPartialHomeomorph).source
    exact ⟨hq, h2⟩

/-- N98: the continuous height shift `(base, s) ↦ (base, s - r_c(Y))` by the SAME actual tube radius. -/
def tubeHeightShift (M e0 c σ : ℝ) (hσ : 0 ≤ σ) :
    ((R3 × sphere (0 : R3) 1) × ℝ) ≃ₜ ((R3 × sphere (0 : R3) 1) × ℝ) where
  toFun a := (a.1, a.2 - tubeRadius M e0 c σ a.1.1)
  invFun a := (a.1, a.2 + tubeRadius M e0 c σ a.1.1)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub
    ((tubeRadius_continuous M e0 σ hσ).comp (continuous_const.prodMk continuous_fst.fst)))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add
    ((tubeRadius_continuous M e0 σ hσ).comp (continuous_const.prodMk continuous_fst.fst)))

/-- N98a: the level-`c` tube chart: center, unit direction, height `‖X-Y‖ - r_c(Y)`. -/
def tubeLevelChart (P : Set R3) (hP : IsOpen P) (lower upper M e0 c σ : ℝ) (hσ : 0 ≤ σ) :
    OpenPartialHomeomorph (R3 × R3) ((R3 × sphere (0 : R3) 1) × ℝ) :=
  (tubePolarChart P hP lower upper).transHomeomorph (tubeHeightShift M e0 c σ hσ)

/-- N98b: the level chart source is EXACTLY `D`, independent of the level. -/
theorem tubeLevelChart_source {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    (M e0 c σ : ℝ) (hσ : 0 ≤ σ) :
    (tubeLevelChart P hP lower upper M e0 c σ hσ).source = tubeChartRoom P lower upper :=
  tubePolarChart_source hP hl

/-- N99: the level chart's forward formulas: center `q.2` and height `‖q.1 - q.2‖ - r_c(q.2)`. -/
theorem tubeLevelChart_apply (P : Set R3) (hP : IsOpen P) (lower upper M e0 c σ : ℝ) (hσ : 0 ≤ σ)
    (q : R3 × R3) (hq : q.1 ≠ q.2) :
    (tubeLevelChart P hP lower upper M e0 c σ hσ q).1.1 = q.2 ∧
      (tubeLevelChart P hP lower upper M e0 c σ hσ q).2 = ‖q.1 - q.2‖ - tubeRadius M e0 c σ q.2 := by
  refine ⟨rfl, ?_⟩
  show (unitSphereRadialPartialHomeomorph (q.1 - q.2)).2 - tubeRadius M e0 c σ q.2 = _
  rw [unitSphereRadialPartialHomeomorph_radius _ (sub_ne_zero.2 hq)]

/-- N100: the level chart's inverse formula `((Y, w), h) ↦ (Y + (h + r_c(Y)) • w, Y)` on positive radius. -/
theorem tubeLevelChart_symm_apply (P : Set R3) (hP : IsOpen P) (lower upper M e0 c σ : ℝ)
    (hσ : 0 ≤ σ) (a : (R3 × sphere (0 : R3) 1) × ℝ) (ha : 0 < a.2 + tubeRadius M e0 c σ a.1.1) :
    (tubeLevelChart P hP lower upper M e0 c σ hσ).symm a =
      (a.1.1 + (a.2 + tubeRadius M e0 c σ a.1.1) • (a.1.2 : R3), a.1.1) := by
  show (a.1.1 + unitSphereRadialPartialHomeomorph.symm (a.1.2, a.2 + tubeRadius M e0 c σ a.1.1),
    a.1.1) = _
  rw [unitSphereRadialPartialHomeomorph_inverse (a.1.2, a.2 + tubeRadius M e0 c σ a.1.1) ha]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

open Set Metric Filter

/-- N101: the level chart's literal target: center in `P` and BOTH radial bounds on `r = h + r_c(Y)`. -/
theorem tubeLevelChart_target {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    (M e0 c σ : ℝ) (hσ : 0 ≤ σ) :
    (tubeLevelChart P hP lower upper M e0 c σ hσ).target =
      {a | a.1.1 ∈ P ∧ lower < a.2 + tubeRadius M e0 c σ a.1.1 ∧
        a.2 + tubeRadius M e0 c σ a.1.1 < upper} := by
  ext a
  let t := a.2 + tubeRadius M e0 c σ a.1.1
  have hOmega : ‖(a.1.2 : R3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using a.1.2.property
  change ((a.1.1 ∈ (univ : Set R3) ∧ (a.1.2, t) ∈ unitSphereRadialPartialHomeomorph.target) ∧
    (a.1.1, unitSphereRadialPartialHomeomorph.symm (a.1.2, t)) ∈
      (tubeDifferencePartialHomeomorph P hP lower upper).target) ↔ _
  constructor
  · intro ha
    have ht : 0 < t := by
      have hh := ha.1.2
      rw [unitSphereRadialPartialHomeomorph_target] at hh
      exact hh.2
    have hh := ha.2
    rw [unitSphereRadialPartialHomeomorph_inverse _ ht] at hh
    have hNorm : ‖t • (a.1.2 : R3)‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hOmega, mul_one]
    have hh' : a.1.1 ∈ P ∧ lower < ‖t • (a.1.2 : R3)‖ ∧ ‖t • (a.1.2 : R3)‖ < upper := hh
    rw [hNorm] at hh'
    exact hh'
  · intro ha
    have ha' : a.1.1 ∈ P ∧ lower < t ∧ t < upper := ha
    have ht : 0 < t := lt_of_le_of_lt hl ha'.2.1
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · rw [unitSphereRadialPartialHomeomorph_target]
      exact ⟨mem_univ _, ht⟩
    · rw [unitSphereRadialPartialHomeomorph_inverse _ ht]
      have hNorm : ‖t • (a.1.2 : R3)‖ = t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hOmega, mul_one]
      show a.1.1 ∈ P ∧ lower < ‖t • (a.1.2 : R3)‖ ∧ ‖t • (a.1.2 : R3)‖ < upper
      rw [hNorm]
      exact ha'

/-- N101a: on the actual target, the N100 inverse formula holds (positivity from `0 ≤ lower`). -/
theorem tubeLevelChart_symm_apply_of_target {P : Set R3} (hP : IsOpen P) {lower upper : ℝ}
    (hl : 0 ≤ lower) (M e0 c σ : ℝ) (hσ : 0 ≤ σ) (a : (R3 × sphere (0 : R3) 1) × ℝ)
    (ha : a ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).target) :
    (tubeLevelChart P hP lower upper M e0 c σ hσ).symm a =
      (a.1.1 + (a.2 + tubeRadius M e0 c σ a.1.1) • (a.1.2 : R3), a.1.1) := by
  rw [tubeLevelChart_target hP hl M e0 c σ hσ] at ha
  exact tubeLevelChart_symm_apply P hP lower upper M e0 c σ hσ a (lt_of_le_of_lt hl ha.2.1)

/-- N101b: an actual zero-height chart point is in the target exactly when its center is in `P` and the
level-`c` radius lies strictly between BOTH caps; its physical image is the literal `c`-front point. -/
theorem tubeLevelChart_zero_mem_target {P : Set R3} (hP : IsOpen P) {lower upper : ℝ}
    (hl : 0 ≤ lower) (M e0 c σ : ℝ) (hσ : 0 ≤ σ) (Y : R3) (w : sphere (0 : R3) 1)
    (hY : Y ∈ P) (hlo : lower < tubeRadius M e0 c σ Y) (hhi : tubeRadius M e0 c σ Y < upper) :
    ((Y, w), (0 : ℝ)) ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).target ∧
      (tubeLevelChart P hP lower upper M e0 c σ hσ).symm ((Y, w), (0 : ℝ)) =
        (Y + tubeRadius M e0 c σ Y • (w : R3), Y) := by
  have hmem : ((Y, w), (0 : ℝ)) ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).target := by
    rw [tubeLevelChart_target hP hl M e0 c σ hσ]
    exact ⟨hY, by simpa using hlo, by simpa using hhi⟩
  refine ⟨hmem, ?_⟩
  rw [tubeLevelChart_symm_apply_of_target hP hl M e0 c σ hσ _ hmem]
  simp

/-- N102: the canonical room `A = canonical(c)` is upward in the SAME level-`c` chart: moving the height up
inside the actual target keeps the center and direction, so the seed cone (`tube_seed_upward`) and the
strict outside (N74 on the fixed ray) are both preserved; D-membership comes from the actual chart. -/
theorem tubeCanonicalRoom_upward {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hc0 : 0 < c0)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y) :
    ∀ z ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ∩
        (tubeLevelChart P hP lower upper M e0 c σ hσ).source, ∀ t : ℝ,
      ((tubeLevelChart P hP lower upper M e0 c σ hσ) z).2 ≤ t →
      (((tubeLevelChart P hP lower upper M e0 c σ hσ) z).1, t) ∈
          (tubeLevelChart P hP lower upper M e0 c σ hσ).target →
      (tubeLevelChart P hP lower upper M e0 c σ hσ).symm
          (((tubeLevelChart P hP lower upper M e0 c σ hσ) z).1, t) ∈
        tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 := by
  rintro ⟨X, Y⟩ ⟨hzA, hzs⟩ t ht hT
  have hsrc : (X, Y) ∈ tubeChartRoom P lower upper := by
    rw [← tubeLevelChart_source hP hl M e0 c σ hσ]
    exact hzs
  have h1 : lower < ‖X - Y‖ := hsrc.2.1
  have hne : X ≠ Y := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    linarith
  obtain ⟨hc1, hh⟩ := tubeLevelChart_apply P hP lower upper M e0 c σ hσ (X, Y) hne
  have hmapz := (tubeLevelChart P hP lower upper M e0 c σ hσ).map_source hzs
  have hinv := tubeLevelChart_symm_apply_of_target hP hl M e0 c σ hσ _ hmapz
  rw [(tubeLevelChart P hP lower upper M e0 c σ hσ).left_inv hzs] at hinv
  have hroom : (tubeLevelChart P hP lower upper M e0 c σ hσ).symm
      (((tubeLevelChart P hP lower upper M e0 c σ hσ) (X, Y)).1, t) ∈ tubeChartRoom P lower upper := by
    rw [← tubeLevelChart_source hP hl M e0 c σ hσ]
    exact (tubeLevelChart P hP lower upper M e0 c σ hσ).map_target hT
  have hnew := tubeLevelChart_symm_apply_of_target hP hl M e0 c σ hσ _ hT
  rw [hnew] at hroom
  rw [hnew]
  generalize (tubeLevelChart P hP lower upper M e0 c σ hσ) (X, Y) = Z at hc1 hh hinv ht hroom ⊢
  obtain ⟨⟨Yc, w⟩, h⟩ := Z
  have hc1' : Yc = Y := hc1
  have hh' : h = ‖X - Y‖ - tubeRadius M e0 c σ Y := hh
  have ht' : h ≤ t := ht
  have hX : X = Yc + (h + tubeRadius M e0 c σ Yc) • (w : R3) := congrArg Prod.fst hinv
  have hroom' : (Yc + (t + tubeRadius M e0 c σ Yc) • (w : R3), Yc) ∈ tubeChartRoom P lower upper :=
    hroom
  show (Yc + (t + tubeRadius M e0 c σ Yc) • (w : R3), Yc) ∈
    tubeCanonicalRoom M e0 c σ B T0 P lower upper c0
  rw [hc1'] at hX hroom' ⊢
  have hw : ‖(w : R3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using w.property
  have hs0 : 0 < h + tubeRadius M e0 c σ Y := by
    rw [hh']
    linarith
  have hss : h + tubeRadius M e0 c σ Y ≤ t + tubeRadius M e0 c σ Y := by linarith
  subst hX
  rcases hzA with hA | hA
  · left
    exact ⟨hroom', tube_seed_upward hw hc0 hs0.le hss hA.2⟩
  · right
    refine ⟨hroom', hA.2.1, ?_⟩
    have hYt : 0 < tubeHeight M e0 Y := hPt Y hroom'.1
    have hpos : 0 < tubePhase M e0 c σ (Y + (h + tubeRadius M e0 c σ Y) • (w : R3), Y) := hA.2.2
    rw [tube_phase_pos_ray_iff hc hYt hs0.le hw] at hpos
    show 0 < tubePhase M e0 c σ (Y + (t + tubeRadius M e0 c σ Y) • (w : R3), Y)
    rw [tube_phase_pos_ray_iff hc hYt (by linarith) hw]
    linarith

/-- N103: lower-level coverage. If `canonical(c) ⊆ N` and the actual level-`c` slab over `K × sphere` of
width `eps` maps into `N`, then for `0 ≤ c' ≤ c` with `(c - c') T0^(1+σ) < eps` also `canonical(c') ⊆ N`:
a new outside point has OLD chart height `‖X-Y‖ - r_c(Y) ∈ (r_{c'} - r_c, 0]` and center in `K`. -/
theorem tubeCanonicalRoom_lower_subset {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c c' σ B T0 c0 eps : ℝ} (hσ : 0 ≤ σ) (hc' : 0 ≤ c') (hcc : c' ≤ c)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    {N : Set (R3 × R3)} {V : Set (R3 × sphere (0 : R3) 1)}
    (hKV : ∀ x : R3 × sphere (0 : R3) 1, -B - 1 ≤ x.1 2 → tubeHeight M e0 x.1 ≤ T0 → x ∈ V)
    (hslab : MapsTo (tubeLevelChart P hP lower upper M e0 c σ hσ).symm
      (V ×ˢ Ioo (0 - eps) (0 + eps)) N)
    (hA : tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆ N)
    (heps : (c - c') * T0 ^ (1 + σ) < eps) :
    tubeCanonicalRoom M e0 c' σ B T0 P lower upper c0 ⊆ N := by
  rintro ⟨X, Y⟩ hq
  rcases hq with hq | hq
  · exact hA (Set.mem_union_left _ hq)
  · have hq' : (X, Y) ∈ tubeChartRoom P lower upper ∧ (-B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0) ∧
        0 < tubePhase M e0 c' σ (X, Y) := hq
    obtain ⟨hD, ⟨hB, hT⟩, hpos⟩ := hq'
    by_cases hc : 0 < tubePhase M e0 c σ (X, Y)
    · exact hA (Set.mem_union_right _ ⟨hD, ⟨hB, hT⟩, hc⟩)
    · have hD' : lower < ‖X - Y‖ := hD.2.1
      have hne : X ≠ Y := by
        intro h
        rw [h, sub_self, norm_zero] at hD'
        linarith
      have hYt : 0 < tubeHeight M e0 Y := hPt Y hD.1
      have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos hYt _
      have hlo : c' * tubeHeight M e0 Y ^ (1 + σ) < ‖X - Y‖ := by
        have h := (tube_phase_pos_iff hc' hYt).1 hpos
        rwa [lt_div_iff₀ htp] at h
      have hhi : ‖X - Y‖ ≤ c * tubeHeight M e0 Y ^ (1 + σ) := by
        have h : ¬ c < ‖X - Y‖ / tubeHeight M e0 Y ^ (1 + σ) :=
          fun h => hc ((tube_phase_pos_iff (hc'.trans hcc) hYt).2 h)
        rw [not_lt, div_le_iff₀ htp] at h
        exact h
      have hcol := (tube_radius_collar (M := M) (e0 := e0) hσ hcc hYt hT.le).2
      unfold tubeRadius at hcol
      have hT0p : 0 ≤ T0 ^ (1 + σ) := Real.rpow_nonneg (by linarith) _
      have hnn : 0 ≤ (c - c') * T0 ^ (1 + σ) := mul_nonneg (by linarith) hT0p
      obtain ⟨hc1, hh⟩ := tubeLevelChart_apply P hP lower upper M e0 c σ hσ (X, Y) hne
      have hh' : ((tubeLevelChart P hP lower upper M e0 c σ hσ) (X, Y)).2 =
          ‖X - Y‖ - c * tubeHeight M e0 Y ^ (1 + σ) := hh
      have hc1' : ((tubeLevelChart P hP lower upper M e0 c σ hσ) (X, Y)).1.1 = Y := hc1
      have hzs : (X, Y) ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).source := by
        rw [tubeLevelChart_source hP hl M e0 c σ hσ]
        exact hD
      have hmem : (tubeLevelChart P hP lower upper M e0 c σ hσ) (X, Y) ∈
          V ×ˢ Ioo (0 - eps) (0 + eps) := by
        refine ⟨hKV _ ?_ ?_, ?_⟩
        · rw [hc1']
          exact hB.le
        · rw [hc1']
          exact hT.le
        · rw [mem_Ioo, hh']
          constructor <;> linarith
      have h := hslab hmem
      rwa [(tubeLevelChart P hP lower upper M e0 c σ hσ).left_inv hzs] at h

/-- N104: the WHOLE compact front slab. If every literal `c`-front point over `K` (all unit directions) lies
in an open `N`, and over `K` the center is in `P` with BOTH radial caps, then ONE actual level-`c` chart slab
over a neighbourhood of `K × sphere` maps into `N` (compact-level slab lemma, zero level by N101b). -/
theorem tube_front_slab {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 : ℝ} (hσ : 0 ≤ σ) (he0 : 0 < e0)
    (hKP : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    {N : Set (R3 × R3)} (hN : IsOpen N)
    (hfront : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ∀ w : sphere (0 : R3) 1, (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ N) :
    ∃ V : Set (R3 × sphere (0 : R3) 1), IsOpen V ∧
      (∀ x : R3 × sphere (0 : R3) 1, -B - 1 ≤ x.1 2 → tubeHeight M e0 x.1 ≤ T0 → x ∈ V) ∧
      ∃ eps : ℝ, 0 < eps ∧
        V ×ˢ Ioo (0 - eps) (0 + eps) ⊆ (tubeLevelChart P hP lower upper M e0 c σ hσ).target ∧
        MapsTo (tubeLevelChart P hP lower upper M e0 c σ hσ).symm
          (V ×ˢ Ioo (0 - eps) (0 + eps)) N := by
  have hK : IsCompact ({Y : R3 | -B - 1 ≤ Y 2 ∧ tubeHeight M e0 Y ≤ T0} ×ˢ
      (univ : Set (sphere (0 : R3) 1))) := (tubeBase_isCompact he0).prod isCompact_univ
  have hT : ({Y : R3 | -B - 1 ≤ Y 2 ∧ tubeHeight M e0 Y ≤ T0} ×ˢ (univ : Set (sphere (0 : R3) 1))) ×ˢ
      {(0 : ℝ)} ⊆ (tubeLevelChart P hP lower upper M e0 c σ hσ).target := by
    rintro ⟨⟨Y, w⟩, h⟩ ⟨⟨⟨hY1, hY2⟩, -⟩, hh⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨hYP, hlo, hhi⟩ := hKP Y hY1 hY2
    exact (tubeLevelChart_zero_mem_target hP hl M e0 c σ hσ Y w hYP hlo hhi).1
  have hlevel : ∀ z ∈ ({Y : R3 | -B - 1 ≤ Y 2 ∧ tubeHeight M e0 Y ≤ T0} ×ˢ
      (univ : Set (sphere (0 : R3) 1))) ×ˢ {(0 : ℝ)},
      (tubeLevelChart P hP lower upper M e0 c σ hσ).symm z ∈ N := by
    rintro ⟨⟨Y, w⟩, h⟩ ⟨⟨⟨hY1, hY2⟩, -⟩, hh⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨hYP, hlo, hhi⟩ := hKP Y hY1 hY2
    rw [(tubeLevelChart_zero_mem_target hP hl M e0 c σ hσ Y w hYP hlo hhi).2]
    exact hfront Y hY1 hY2 w
  obtain ⟨V, hV, hKV, eps, heps, hsub, hmaps⟩ :=
    exists_actual_chart_compact_level_slab (tubeLevelChart P hP lower upper M e0 c σ hσ) hK 0 hN hT hlevel
  exact ⟨V, hV, fun x h1 h2 => hKV ⟨⟨h1, h2⟩, mem_univ _⟩, eps, heps, hsub, hmaps⟩

/-- N105: the geometric front passage. An open `N ⊇ canonical(c)` containing the WHOLE literal `c`-front over
`K` contains every `canonical(c')` for `0 ≤ c' ≤ c` with `c - c' < eta`, ONE `eta > 0` (N104 slab + N103). -/
theorem tube_front_passage_geometry {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 : ℝ} (hσ : 0 ≤ σ) (he0 : 0 < e0)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    {N : Set (R3 × R3)} (hN : IsOpen N)
    (hA : tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆ N)
    (hfront : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ∀ w : sphere (0 : R3) 1, (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ N) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ c' : ℝ, 0 ≤ c' → c' ≤ c → c - eta < c' →
      tubeCanonicalRoom M e0 c' σ B T0 P lower upper c0 ⊆ N := by
  obtain ⟨V, -, hKV, eps, heps, -, hmaps⟩ := tube_front_slab hP hl hσ he0 hKP hN hfront
  have ha : 0 ≤ |T0 ^ (1 + σ)| := abs_nonneg _
  refine ⟨eps / (|T0 ^ (1 + σ)| + 1), div_pos heps (by linarith), ?_⟩
  intro c' hc' hcc hlt
  apply tubeCanonicalRoom_lower_subset hP hl hσ hc' hcc hPt hKV hmaps hA
  have h1 : c - c' < eps / (|T0 ^ (1 + σ)| + 1) := by linarith
  have h2 : (c - c') * (|T0 ^ (1 + σ)| + 1) < eps := by
    rwa [lt_div_iff₀ (by linarith)] at h1
  have h3 : (c - c') * T0 ^ (1 + σ) ≤ (c - c') * |T0 ^ (1 + σ)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  have h4 : (c - c') * |T0 ^ (1 + σ)| ≤ (c - c') * (|T0 ^ (1 + σ)| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- N106: the N95b step from ONE actual open solution `H` on an open `N ⊇ canonical(c) ∪ (whole c-front over K)`
with BOTH full crosses and seed equality: restrict the SAME `H` to every `canonical(c')`, `c - eps < c' ≤ c`
(N105, `eps ≤ c - amin`). Such `N, H` are constructed in N108. -/
theorem tube_reached_step_of_front_solution (S : KnownSideSourceData) (L lam : ℝ)
    {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 amin : ℝ} (hσ : 0 ≤ σ) (he0 : 0 < e0) (hamin : 0 ≤ amin) (hc : amin < c)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    {H0 : R3 × R3 → ℝ} {N : Set (R3 × R3)} (hN : IsOpen N)
    (hA : tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆ N)
    (hfront : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ∀ w : sphere (0 : R3) 1, (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ N)
    (H : R3 × R3 → ℝ) (hH : ProductSolutionOn S L lam H N)
    (hHA : EqOn H H0 (tubeSeedRoom P lower upper c0))
    (hH1 : ∀ v ∈ N, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ N, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) :
    ∃ ε > 0, ∀ c', c - ε < c' → c' ≤ c →
      TubeReached S L lam M e0 c' σ B T0 P lower upper c0 H0 := by
  obtain ⟨eta, heta, hsub⟩ :=
    tube_front_passage_geometry (c0 := c0) hP hl hσ he0 hPt hKP hN hA hfront
  refine ⟨min eta (c - amin), lt_min heta (by linarith), ?_⟩
  intro c' h1 h2
  have hm1 := min_le_left eta (c - amin)
  have hm2 := min_le_right eta (c - amin)
  have hs := hsub c' (by linarith) h2 (by linarith)
  unfold TubeReached
  exact ⟨H, ⟨hH.1.mono hs, fun v hv => hH.2.1 v (hs hv), fun v hv => hH.2.2 v (hs hv)⟩, hHA,
    fun v hv => hH1 v (hs hv), fun v hv => hH2 v (hs hv)⟩

/-- N107: ONE actual same-chart local box at an UNSEEDED `c`-front point: N72 in the room
`D ∩ {t>0} ∩ (D ∩ strict base)` from the reached old-side solution `F` and actual strictness at the point,
then the zero box in the SAME level-`c` chart; `G = F` on the box's positive height. -/
theorem tube_front_box (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hroom : tubeChartRoom P lower upper ⊆ dilatedOffDiagonal S lam)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (Y : R3) (w : sphere (0 : R3) 1) (hY : Y ∈ P) (hB : -B - 1 < Y 2) (hT : tubeHeight M e0 Y < T0)
    (hlo : lower < tubeRadius M e0 c σ Y) (hhi : tubeRadius M e0 c σ Y < upper)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
      (Y + tubeRadius M e0 c σ Y • (w : R3)) Y (tubePhase M e0 c σ))
    (F : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0))
    (hF1 : ∀ v ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0, lam • v.2 ∈ S.W →
      F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0, lam • v.1 ∈ S.W →
      F v = dilatedKernel2 S lam v) :
    ∃ Bx : Set (R3 × sphere (0 : R3) 1), IsOpen Bx ∧ ∃ d : ℝ, 0 < d ∧
      Bx ×ˢ Ioo (0 - d) (0 + d) ⊆ (tubeLevelChart P hP lower upper M e0 c σ hσ).target ∧
      (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
        (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d)) ∧
      ∃ G : R3 × R3 → ℝ,
        ProductSolutionOn S L lam G ((tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
          (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d))) ∧
        (tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
          (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d)) ⊆
            dilatedOffDiagonal S lam ∧
        (∀ z ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
          (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d)),
            lam • z.2 ∈ S.W → G z = dilatedKernel1 S lam z) ∧
        (∀ z ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
          (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d)),
            lam • z.1 ∈ S.W → G z = dilatedKernel2 S lam z) ∧
        (∀ z ∈ (tubeLevelChart P hP lower upper M e0 c σ hσ).source ∩
          (tubeLevelChart P hP lower upper M e0 c σ hσ) ⁻¹' (Bx ×ˢ Ioo (0 - d) (0 + d)),
            0 < ((tubeLevelChart P hP lower upper M e0 c σ hσ) z).2 → G z = F z) := by
  have h2 : Continuous fun q : R3 × R3 => q.2 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_snd
  have hK : IsOpen {q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0} :=
    (isOpen_lt continuous_const h2).inter
      (isOpen_lt ((st_height_continuous M e0).comp continuous_snd) continuous_const)
  have hWo : IsOpen (tubeChartRoom P lower upper ∩
      {q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0}) :=
    (tubeChartRoom_isOpen hP lower upper).inter hK
  have hw : ‖(w : R3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using w.property
  have hr : 0 < tubeRadius M e0 c σ Y := lt_of_le_of_lt hl hlo
  have hn : ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ = tubeRadius M e0 c σ Y := by
    rw [add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hqD : (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ tubeChartRoom P lower upper := by
    refine ⟨hY, ?_, ?_⟩
    · show lower < ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖
      rw [hn]
      exact hlo
    · show ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ < upper
      rw [hn]
      exact hhi
  have hqR : (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ dilatedOffDiagonal S lam ∩
      {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩ (tubeChartRoom P lower upper ∩
        {q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0}) :=
    ⟨⟨hroom hqD, hPt Y hY⟩, hqD, hB, hT⟩
  have hsub : {z | z ∈ dilatedOffDiagonal S lam ∩ {z : R3 × R3 | 0 < tubeHeight M e0 z.2} ∩
      (tubeChartRoom P lower upper ∩ {q : R3 × R3 | -B - 1 < q.2 2 ∧ tubeHeight M e0 q.2 < T0}) ∧
        0 < tubePhase M e0 c σ z} ⊆ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 :=
    fun z hz => Set.mem_union_right _ ⟨hz.1.2.1, hz.1.2.2, hz.2⟩
  obtain ⟨V, G, hV, hqV, hVR, hG, hGF, hG1, hG2⟩ :=
    tube_front_room_extension S L lam hlam M e0 c σ Y (w : R3) hw hWo hqR hTest F
      ⟨hF.1.mono hsub, fun v hv => hF.2.1 v (hsub hv), fun v hv => hF.2.2 v (hsub hv)⟩
      (fun v hv hp hW => hF1 v (hsub ⟨hv, hp⟩) hW) (fun v hv hp hW => hF2 v (hsub ⟨hv, hp⟩) hW)
  have hqs : (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈
      (tubeLevelChart P hP lower upper M e0 c σ hσ).source := by
    rw [tubeLevelChart_source hP hl M e0 c σ hσ]
    exact hqD
  have hne : Y + tubeRadius M e0 c σ Y • (w : R3) ≠ Y := by
    intro h
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hzero : ((tubeLevelChart P hP lower upper M e0 c σ hσ)
      (Y + tubeRadius M e0 c σ Y • (w : R3), Y)).2 = 0 := by
    rw [(tubeLevelChart_apply P hP lower upper M e0 c σ hσ _ hne).2]
    show ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ - tubeRadius M e0 c σ Y = 0
    rw [hn, sub_self]
  obtain ⟨Bx, hBx, hqB, d, hd, hBT, hBV⟩ :=
    exists_actual_chart_zero_box (tubeLevelChart P hP lower upper M e0 c σ hσ) _ hqs hzero V hV hqV
  have hIoo : Ioo (0 - d) (0 + d) = Ioo (-d) d := by rw [zero_sub, zero_add]
  refine ⟨Bx, hBx, d, hd, ?_⟩
  rw [hIoo]
  refine ⟨hBT, ⟨hqs, hqB, ?_⟩, G,
    ⟨hG.1.mono hBV, fun v hv => hG.2.1 v (hBV hv), fun v hv => hG.2.2 v (hBV hv)⟩,
    fun z hz => (hVR (hBV hz)).1.1, fun z hz hW => hG1 z (hBV hz) hW,
    fun z hz hW => hG2 z (hBV hz) hW, ?_⟩
  · rw [mem_Ioo, hzero]
    constructor <;> linarith
  · rintro ⟨X1, Y1⟩ hz hpos
    have hzV := hBV hz
    have hzR := hVR hzV
    have hzD : lower < ‖X1 - Y1‖ := hzR.2.1.2.1
    have ht : 0 < tubeHeight M e0 Y1 := hzR.1.2
    have hne1 : X1 ≠ Y1 := by
      intro h
      rw [h, sub_self, norm_zero] at hzD
      linarith
    have hh := (tubeLevelChart_apply P hP lower upper M e0 c σ hσ (X1, Y1) hne1).2
    have hh' : ((tubeLevelChart P hP lower upper M e0 c σ hσ) (X1, Y1)).2 =
        ‖X1 - Y1‖ - c * tubeHeight M e0 Y1 ^ (1 + σ) := hh
    rw [hh'] at hpos
    have htp : 0 < tubeHeight M e0 Y1 ^ (1 + σ) := Real.rpow_pos_of_pos ht _
    have hph : 0 < tubePhase M e0 c σ (X1, Y1) := by
      refine (tube_phase_pos_iff hc ht).2 ?_
      rw [lt_div_iff₀ htp]
      linarith
    exact hGF ⟨hzV, hzR, hph⟩

/-- N108: the ACTUAL front step (N95b `hstep` shape) from `TubeReached(c)`: N107 boxes at EVERY unseeded front
point (actual strictness there), the full-cross common-level gluing with `A = canonical(c)` (upward by
N102) in the SAME level-`c` chart, boundary front points in `A`, then N106. -/
theorem tube_reached_front_step (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 amin : ℝ} (hσ : 0 ≤ σ) (he0 : 0 < e0) (hM : B + 3 < M) (hc0 : 0 < c0)
    (hamin : 0 ≤ amin) (hc : amin < c)
    (hroom : tubeChartRoom P lower upper ⊆ dilatedOffDiagonal S lam)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    (hstrict : ∀ Y : R3, -B - 1 < Y 2 → tubeHeight M e0 Y < T0 → ∀ w : sphere (0 : R3) 1,
      ¬min ((Y + tubeRadius M e0 c σ Y • (w : R3)) 2) (Y 2) <
        c0 * ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ →
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
        (Y + tubeRadius M e0 c σ Y • (w : R3)) Y (tubePhase M e0 c σ))
    (hseed : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ¬ (-B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0) → ∀ w : sphere (0 : R3) 1,
        (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0)
    {H0 : R3 × R3 → ℝ} (hR : TubeReached S L lam M e0 c σ B T0 P lower upper c0 H0) :
    ∃ ε > 0, ∀ c', c - ε < c' → c' ≤ c →
      TubeReached S L lam M e0 c' σ B T0 P lower upper c0 H0 := by
  obtain ⟨F, hF, hFA, hF1, hF2⟩ := hR
  have hcn : 0 ≤ c := by linarith
  let ι := {p : R3 × sphere (0 : R3) 1 // -B - 1 < p.1 2 ∧ tubeHeight M e0 p.1 < T0 ∧
    ¬min ((p.1 + tubeRadius M e0 c σ p.1 • (p.2 : R3)) 2) (p.1 2) <
      c0 * ‖(p.1 + tubeRadius M e0 c σ p.1 • (p.2 : R3)) - p.1‖}
  choose Bx hBx d hd hBT hq G hG hGroom hG1 hG2 hGF using fun i : ι =>
    tube_front_box S L lam hlam hP hl (c0 := c0) hσ hcn hroom hPt i.1.1 i.1.2
      (hKP i.1.1 i.2.1.le i.2.2.1.le).1 i.2.1 i.2.2.1 (hKP i.1.1 i.2.1.le i.2.2.1.le).2.1
      (hKP i.1.1 i.2.1.le i.2.2.1.le).2.2 (hstrict i.1.1 i.2.1 i.2.2.1 i.1.2 i.2.2.2) F hF hF1 hF2
  have hAo : IsOpen (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0) :=
    (tubeSeedRoom_isOpen hP lower upper c0).union (tubeOutsideRoom_isOpen hP lower upper he0.le hM)
  have hAroom : tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 ⊆ dilatedOffDiagonal S lam := by
    intro z hz
    rcases hz with hz | hz
    · exact hroom hz.1
    · exact hroom hz.1
  obtain ⟨hNo, -, H, hH, hHF, -, hH1, hH2⟩ :=
    exists_native_full_cross_solution_from_common_level_boxes S L lam
      (tubeLevelChart P hP lower upper M e0 c σ hσ) Bx hBx 0 d hd hBT
      (tubeCanonicalRoom M e0 c σ B T0 P lower upper c0) hAo hAroom
      (tubeCanonicalRoom_upward hP hl hσ hcn hc0 hPt) F hF hF1 hF2 G hG hGroom hG1 hG2 hGF
  refine tube_reached_step_of_front_solution S L lam hP hl hσ he0 hamin hc hPt hKP hNo
    Set.subset_union_left ?_ H hH (fun z hz => (hHF (Set.mem_union_left _ hz)).trans (hFA hz))
    hH1 hH2
  intro Y hY1 hY2 w
  by_cases hCone : min ((Y + tubeRadius M e0 c σ Y • (w : R3)) 2) (Y 2) <
      c0 * ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖
  · obtain ⟨hYP,hlo,hhi⟩ := hKP Y hY1 hY2
    have hw : ‖(w : R3)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using w.property
    have hr : 0 < tubeRadius M e0 c σ Y := hl.trans_lt hlo
    have hn : ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ = tubeRadius M e0 c σ Y := by
      rw [add_sub_cancel_left,norm_smul,hw,mul_one,Real.norm_eq_abs,abs_of_pos hr]
    exact Set.mem_union_left _ (Set.mem_union_left _
      ⟨⟨hYP,by simpa only [hn] using hlo,by simpa only [hn] using hhi⟩,hCone⟩)
  · by_cases hs : -B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0
    · let i : ι := ⟨(Y,w),hs.1,hs.2,hCone⟩
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i,hq i⟩)
    · exact Set.mem_union_left _ (hseed Y hY1 hY2 hs w)

/-- N109: `TubeReached amin` from the actual RF seed solution on `A` (SAME `H0`, BOTH crosses), N95b and the
ACTUAL front step N108 at every level in `(amin, 2/c0+1]`; inputs are the level-uniform room caps on `K`,
actual strictness at unseeded front points and boundary seed coverage (no hstep/solver input). -/
theorem tube_reached_amin (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 σ B T0 c0 amin : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (he0 : 0 < e0) (hM : B + 3 < M)
    (hc0 : 0 < c0) (hB : 0 ≤ B) (hamin : 0 ≤ amin)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper)
    (hroom : tubeChartRoom P lower upper ⊆ dilatedOffDiagonal S lam)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ c, amin < c → c ≤ 2 / c0 + 1 → ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    (hstrict : ∀ c, amin < c → c ≤ 2 / c0 + 1 → ∀ Y : R3, -B - 1 < Y 2 → tubeHeight M e0 Y < T0 →
      ∀ w : sphere (0 : R3) 1,
        ¬min ((Y + tubeRadius M e0 c σ Y • (w : R3)) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ →
        ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
          (Y + tubeRadius M e0 c σ Y • (w : R3)) Y (tubePhase M e0 c σ))
    (hseed : ∀ c, amin < c → c ≤ 2 / c0 + 1 → ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ¬ (-B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0) → ∀ w : sphere (0 : R3) 1,
        (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0)
    {H0 : R3 × R3 → ℝ}
    (hH0 : ProductSolutionOn S L lam H0 (tubeSeedRoom P lower upper c0))
    (hH1 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.2 ∈ S.W → H0 v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.1 ∈ S.W → H0 v = dilatedKernel2 S lam v) :
    TubeReached S L lam M e0 amin σ B T0 P lower upper c0 H0 :=
  tube_reached_all S L lam hP hc0 hB hM he0.le hσ hσ1 hamin hup hH0 hH1 hH2
    (fun c hc hcmax hR => tube_reached_front_step S L lam hlam hP hl hσ he0 hM hc0 hamin hc hroom hPt
      (hKP c hc hcmax) (hstrict c hc hcmax) (hseed c hc hcmax) hR)

/-- N110: boundary seed coverage: a front point over `K` OUTSIDE the strict base is genuinely seeded,
by N25 (bottom face `Y₂ = -B-1 < 0`) or N26 (top face `t = T0`, `1 < c0 amin T0^σ`), with the SAME caps. -/
theorem tube_boundary_front_seeded {P : Set R3} {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 c σ B T0 c0 amin : ℝ} (hc0 : 0 < c0) (hM0 : 0 ≤ M) (he0 : 0 ≤ e0) (hB : 0 ≤ B)
    (hamin : 0 ≤ amin) (ham : amin ≤ c) (htopT : 1 < c0 * amin * T0 ^ σ)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper) :
    ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      ¬ (-B - 1 < Y 2 ∧ tubeHeight M e0 Y < T0) → ∀ w : sphere (0 : R3) 1,
        (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ tubeCanonicalRoom M e0 c σ B T0 P lower upper c0 := by
  intro Y hY1 hY2 hns w
  obtain ⟨hYP, hlo, hhi⟩ := hKP Y hY1 hY2
  have hw : ‖(w : R3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using w.property
  have hr : 0 < tubeRadius M e0 c σ Y := lt_of_le_of_lt hl hlo
  have hn : ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ = tubeRadius M e0 c σ Y := by
    rw [add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hqD : (Y + tubeRadius M e0 c σ Y • (w : R3), Y) ∈ tubeChartRoom P lower upper := by
    refine ⟨hYP, ?_, ?_⟩
    · show lower < ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖
      rw [hn]
      exact hlo
    · show ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ < upper
      rw [hn]
      exact hhi
  refine Set.mem_union_left _ ⟨hqD, ?_⟩
  show min ((Y + tubeRadius M e0 c σ Y • (w : R3)) 2) (Y 2) <
    c0 * ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖
  by_cases hb : -B - 1 < Y 2
  · have hteq : tubeHeight M e0 Y = T0 :=
      le_antisymm hY2 (not_lt.1 (fun h => hns ⟨hb, h⟩))
    exact tube_top_face_in_seed hc0 hM0 he0 (hPt Y hYP) hamin ham (by rw [hteq]; exact htopT) hw
  · exact tube_bottom_face_in_seed hc0 hr (by linarith [not_lt.1 hb]) hw

/-- N111: `TubeReached amin` with the boundary seed coverage DISCHARGED by N110 (no `hseed` input). -/
theorem tube_reached_amin_seeded (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {P : Set R3} (hP : IsOpen P) {lower upper : ℝ} (hl : 0 ≤ lower)
    {M e0 σ B T0 c0 amin : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (he0 : 0 < e0) (hM : B + 3 < M)
    (hc0 : 0 < c0) (hB : 0 ≤ B) (hamin : 0 ≤ amin) (htopT : 1 < c0 * amin * T0 ^ σ)
    (hup : (2 / c0 + 1) * max 1 T0 ^ 2 < upper)
    (hroom : tubeChartRoom P lower upper ⊆ dilatedOffDiagonal S lam)
    (hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y)
    (hKP : ∀ c, amin < c → c ≤ 2 / c0 + 1 → ∀ Y : R3, -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 c σ Y ∧ tubeRadius M e0 c σ Y < upper)
    (hstrict : ∀ c, amin < c → c ≤ 2 / c0 + 1 → ∀ Y : R3, -B - 1 < Y 2 → tubeHeight M e0 Y < T0 →
      ∀ w : sphere (0 : R3) 1,
        ¬min ((Y + tubeRadius M e0 c σ Y • (w : R3)) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 c σ Y • (w : R3)) - Y‖ →
        ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun x => S.g2 (lam • x))
          (Y + tubeRadius M e0 c σ Y • (w : R3)) Y (tubePhase M e0 c σ))
    {H0 : R3 × R3 → ℝ}
    (hH0 : ProductSolutionOn S L lam H0 (tubeSeedRoom P lower upper c0))
    (hH1 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.2 ∈ S.W → H0 v = dilatedKernel1 S lam v)
    (hH2 : ∀ v ∈ tubeSeedRoom P lower upper c0, lam • v.1 ∈ S.W → H0 v = dilatedKernel2 S lam v) :
    TubeReached S L lam M e0 amin σ B T0 P lower upper c0 H0 :=
  tube_reached_amin S L lam hlam hP hl hσ hσ1 he0 hM hc0 hB hamin hup hroom hPt hKP hstrict
    (fun c hc hcmax => tube_boundary_front_seeded hl hc0 (by linarith) he0.le hB hamin hc.le htopT hPt
      (hKP c hc hcmax)) hH0 hH1 hH2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

/-- Actual cone agreement and BOTH full crosses justify the ENTIRE final overlap. -/
theorem exists_fixed_separation_kernel_from_coarse_cone
    (S : KnownSideSourceData) (L lam B d Bs ds c0 : ℝ) (hlam : 0 < lam)
    (hB : B < Bs) (hd : ds < d)
    (N U : Set (R3 × R3)) (F H0 : R3 × R3 → ℝ)
    (hN : IsOpen N) (hNRoom : N ⊆ dilatedOffDiagonal S lam)
    (hF : ProductSolutionOn S L lam F N)
    (hF1 : ∀ q ∈ N, lam • q.2 ∈ S.W → F q = dilatedKernel1 S lam q)
    (hF2 : ∀ q ∈ N, lam • q.1 ∈ S.W → F q = dilatedKernel2 S lam q)
    (hURoom : U ⊆ dilatedOffDiagonal S lam) (hInitial : initialCross S lam ⊆ U)
    (hH : ProductSolutionOn S L lam H0 U)
    (hH1 : ∀ q ∈ U, lam • q.2 ∈ S.W → H0 q = dilatedKernel1 S lam q)
    (hH2 : ∀ q ∈ U, lam • q.1 ∈ S.W → H0 q = dilatedKernel2 S lam q)
    (hCover : ∀ X Y : R3, ‖X‖ ≤ Bs → ‖Y‖ ≤ Bs → ds ≤ ‖X-Y‖ →
      min (X 2) (Y 2) < c0 * ‖X-Y‖ → (X,Y) ∈ U)
    (hEqCone : ∀ q ∈ N, min (q.1 2) (q.2 2) < c0 * ‖q.1-q.2‖ → F q = H0 q)
    (hTarget : ∀ q ∈ fixedSeparationSet B d,
      min (q.1 2) (q.2 2) < c0 * ‖q.1-q.2‖ ∨ q ∈ N) :
    ∃ (V : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen V ∧
      V ⊆ dilatedOffDiagonal S lam ∧ initialCross S lam ⊆ V ∧
      fixedSeparationSet B d ⊆ V ∧ ProductSolutionOn S L lam H V ∧
      (∀ q ∈ V, lam • q.2 ∈ S.W → H q = dilatedKernel1 S lam q) ∧
      (∀ q ∈ V, lam • q.1 ∈ S.W → H q = dilatedKernel2 S lam q) := by
  let C : Set (R3 × R3) := {q | ‖q.1‖ < Bs ∧ ‖q.2‖ < Bs ∧ ds < ‖q.1-q.2‖ ∧
    min (q.1 2) (q.2 2) < c0 * ‖q.1-q.2‖}
  let V : Set (R3 × R3) := initialCross S lam ∪ C
  have hCoord : Continuous (fun q : R3 × R3 => min (q.1 2) (q.2 2)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_fst).min
      ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_snd)
  have hC : IsOpen C :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      ((isOpen_lt continuous_snd.norm continuous_const).inter
        ((isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm).inter
          (isOpen_lt hCoord (continuous_const.mul (continuous_fst.sub continuous_snd).norm))))
  have hV : IsOpen V := (initial_cross_product S L lam hlam).1.union hC
  have hVU : V ⊆ U := by
    intro q hq
    rcases hq with hi | hc
    · exact hInitial hi
    · exact hCover q.1 q.2 hc.1.le hc.2.1.le hc.2.2.1.le hc.2.2.2
  have hEq : EqOn F H0 (N ∩ V) := by
    intro q hq
    rcases hq.2 with hi | hc
    · rcases hi.2 with hx | hy
      · exact (hF2 q hq.1 hx).trans (hH2 q (hInitial hi) hx).symm
      · exact (hF1 q hq.1 hy).trans (hH1 q (hInitial hi) hy).symm
    · exact hEqCone q hq.1 hc.2.2.2
  obtain ⟨H,hHSol,hHF,hHH⟩ := exists_product_solution_on_union_of_eqOn S L lam N V hN hV
    F H0 hF (productSolutionOn_mono hH hVU) hEq
  refine ⟨N ∪ V,H,hN.union hV,?_,?_,?_,hHSol,?_,?_⟩
  · intro q hq
    rcases hq with hn | hv
    · exact hNRoom hn
    · exact hURoom (hVU hv)
  · intro q hq
    exact Or.inr (Or.inl hq)
  · intro q hq
    rcases hTarget q hq with hc | hn
    · exact Or.inr (Or.inr ⟨hq.1.trans_lt hB,hq.2.1.trans_lt hB,hd.trans_le hq.2.2,hc⟩)
    · exact Or.inl hn
  · intro q hq hW
    rcases hq with hn | hv
    · exact (hHF hn).trans (hF1 q hn hW)
    · exact (hHH hv).trans (hH1 q (hVU hv) hW)
  · intro q hq hW
    rcases hq with hn | hv
    · exact (hHF hn).trans (hF2 q hn hW)
    · exact (hHH hv).trans (hH2 q (hVU hv) hW)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

theorem fixed_separation_product_producer : FixedSeparationProductProducer := by
  classical
  intro S B d hB hd
  obtain ⟨c0,hc0,HRF⟩ := uniform_common_coarse_seed_RF S
  let η := min (1/10 : ℝ) (c0/13)
  have hη : 0 < η := lt_min (by norm_num) (div_pos hc0 (by norm_num))
  have hη10 : η ≤ 1/10 := min_le_left _ _
  have hc0η : 13*η ≤ c0 := by
    have hh : η ≤ c0/13 := min_le_right _ _
    linarith
  let M := B+4
  have hM : B+3 < M := by dsimp only [M];linarith
  obtain ⟨σ,T0,e0,hσ,hση,hσ1,hT0,hTop,he0,he01,hGap,hQ,lS,hlS,HS⟩ :=
    tube_scaled_strict_room_coherent S hc0 hη hη10 hc0η hd hB.le hM
  obtain ⟨CY,hCY,hP,hCenter⟩ := tube_center_room (M := M) (B := B) (T0 := T0) he0 hM
  let P : Set R3 := {Y | ‖Y‖ < CY ∧ 0 < tubeHeight M e0 Y}
  let amin := min 1 (d/(2*(M+B+B^2)^2))
  let lower := amin/4
  let upper := (2/c0+1)*max 1 T0^2+2*B+3
  obtain ⟨hamin,hLowerA,hLower,hLowerD,hUpper,hUpperB⟩ :=
    tube_room_constants (T0 := T0) hc0 hd hB.le hM
  have hUpperPos : 0 < upper := by change 0 < (2/c0+1)*max 1 T0^2+2*B+3;positivity
  obtain ⟨lD,hlD,HD⟩ := tube_room_mem_dilated S (CY := CY) (lower := lower) (upper := upper)
    hLower.le hCY hUpperPos
  let Bs := CY+upper+B+1
  let ds := min (lower/2) (d/2)
  have hBs : 0 < Bs := by dsimp only [Bs];positivity
  have hds : 0 < ds := lt_min (by positivity) (by positivity)
  have hBsD : CY+upper ≤ Bs := by dsimp only [Bs];linarith
  have hBsB : B < Bs := by dsimp only [Bs];linarith
  have hdsD : ds ≤ lower := by
    have hh : ds ≤ lower/2 := min_le_left _ _
    linarith
  have hdsd : ds < d := by
    have hh : ds ≤ d/2 := min_le_right _ _
    linarith
  obtain ⟨lRF,hlRF,HF⟩ := HRF Bs ds hBs hds
  let lam0 := min lRF (min lS lD)
  refine ⟨lam0,lt_min hlRF (lt_min hlS hlD),?_⟩
  intro L lam hlam hlam0
  have hlamRF : lam ≤ lRF := hlam0.trans (min_le_left _ _)
  have hlamS : lam ≤ lS := hlam0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamD : lam ≤ lD := hlam0.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨U,H0,hU,hInitial,hURoom,hH0,hHInitial,hH1,hH2,hCover⟩ := HF L lam hlam hlamRF
  obtain ⟨hAU,hASol,hA1,hA2⟩ := tube_seed_restrict S L lam
    (M := M) (e0 := e0) (c0 := c0) (Bs := Bs) (ds := ds) (CY := CY)
    (lower := lower) (upper := upper) hH0 hH1 hH2 hCover hBsD hdsD
  have hDSource : tubeChartRoom P lower upper ⊆ dilatedOffDiagonal S lam := by
    intro q hq
    exact HD lam hlam hlamD q hq.1.1 hq.2.1 hq.2.2
  have hTests : ∀ a ∈ Icc amin (2/c0+1), ∀ Y : R3,
      -B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ∀ w : R3, ‖w‖ = 1 →
      ¬min ((Y+tubeRadius M e0 a σ Y • w) 2) (Y 2) <
        c0*‖(Y+tubeRadius M e0 a σ Y • w)-Y‖ →
      ProductHessianStrictAt (fun X => S.g1 (lam • X)) (fun Z => S.g2 (lam • Z))
        (Y+tubeRadius M e0 a σ Y • w) Y (tubePhase M e0 a σ) := by
    intro a ha Y hY hT w hw hNoCone
    exact (HS lam hlam hlamS (a,Y,w) ⟨hw,hY,hT,ha.1,ha.2,not_lt.mp hNoCone⟩).1

  have hMpos : 0 < M := by dsimp only [M];linarith
  have hPt : ∀ Y ∈ P, 0 < tubeHeight M e0 Y := fun Y hY => hY.2
  have hFrontCaps : ∀ a ∈ Icc amin (2/c0+1), ∀ Y : R3,
      -B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      Y ∈ P ∧ lower < tubeRadius M e0 a σ Y ∧ tubeRadius M e0 a σ Y < upper := by
    intro a ha Y hY hT
    obtain ⟨hCYat,ht1⟩ := hCenter Y hY hT
    have ht : 0 < tubeHeight M e0 Y := by linarith
    have hYP : Y ∈ P := ⟨hCYat,ht⟩
    let w0 : R3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
    have hw0 : ‖w0‖ = 1 := by simp [w0]
    have hD := tube_front_in_room hamin hLowerA hUpper ha.1 ha.2 hσ.le hσ1 ht1 hT hYP hw0
    have hr : 0 < tubeRadius M e0 a σ Y :=
      mul_pos (hamin.trans_le ha.1) (Real.rpow_pos_of_pos ht _)
    have hn : ‖(Y+tubeRadius M e0 a σ Y • w0)-Y‖ = tubeRadius M e0 a σ Y := by
      rw [add_sub_cancel_left,norm_smul,hw0,mul_one,Real.norm_eq_abs,abs_of_pos hr]
    exact ⟨hYP,by simpa only [hn] using hD.2.1,by simpa only [hn] using hD.2.2⟩
  have hUnseededInterior : ∀ a ∈ Icc amin (2/c0+1), ∀ Y : R3,
      -B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ∀ w : R3, ‖w‖ = 1 →
      ¬min ((Y+tubeRadius M e0 a σ Y • w) 2) (Y 2) < c0*‖(Y+tubeRadius M e0 a σ Y • w)-Y‖ →
      -B-1 < Y 2 ∧ tubeHeight M e0 Y < T0 := by
    intro a ha Y hY hT w hw hNoCone
    have ht : 0 < tubeHeight M e0 Y := (hFrontCaps a ha Y hY hT).1.2
    have hr : 0 < tubeRadius M e0 a σ Y :=
      mul_pos (hamin.trans_le ha.1) (Real.rpow_pos_of_pos ht _)
    constructor
    · by_contra hn
      have hyNeg : Y 2 < 0 := by have hh := le_of_not_gt hn;linarith
      exact hNoCone (tube_bottom_face_in_seed hc0 hr hyNeg hw)
    · by_contra hn
      have htEq : tubeHeight M e0 Y = T0 := le_antisymm hT (le_of_not_gt hn)
      have hTopAt : 1 < c0*amin*tubeHeight M e0 Y^σ := by rw [htEq];exact hTop
      exact hNoCone (tube_top_face_in_seed hc0 hMpos.le he0.le ht hamin.le ha.1 hTopAt hw)

  -- The front-passage theorem, instantiated with hTests, hDSource, the same hTop/hCenter
  -- and the same H0 seed data.
  have hReached : TubeReached S L lam M e0 amin σ B T0 P lower upper c0 H0 :=
    tube_reached_amin_seeded S L lam hlam hP hLower.le hσ.le hσ1 he0 hM hc0 hB.le hamin.le
      hTop hUpper hDSource hPt
      (fun c hc hcmax => hFrontCaps c ⟨hc.le,hcmax⟩)
      (fun c hc hcmax Y hY hT w hNoCone => hTests c ⟨hc.le,hcmax⟩ Y hY.le hT.le (w : R3)
        (by simpa only [mem_sphere,dist_zero_right] using w.property) hNoCone)
      hASol hA1 hA2

  obtain ⟨F,hF,hFEq,hF1,hF2⟩ := hReached
  let N := tubeCanonicalRoom M e0 amin σ B T0 P lower upper c0
  have hN : IsOpen N := (tubeSeedRoom_isOpen hP lower upper c0).union
    (tubeOutsideRoom_isOpen (M := M) (e0 := e0) (c := amin) (σ := σ) (B := B) (T0 := T0)
      hP lower upper he0.le hM)
  have hND : N ⊆ tubeChartRoom P lower upper := by
    intro q hq
    rcases hq with hA | hO
    · exact hA.1
    · exact hO.1
  have hEqCone : ∀ q ∈ N, min (q.1 2) (q.2 2) < c0*‖q.1-q.2‖ → F q = H0 q := by
    intro q hq hCone
    exact hFEq ⟨hND hq,hCone⟩
  have hTarget : ∀ q ∈ fixedSeparationSet B d,
      min (q.1 2) (q.2 2) < c0*‖q.1-q.2‖ ∨ q ∈ N := by
    intro q hq
    have hYCoord : |q.2 2| ≤ B := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le q.2 (2 : Fin 3)).trans hq.2.1
    have hNormSq : ‖q.2‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hq.2.1 2
    have hSq : ‖q.2‖^2 = q.2 0^2+q.2 1^2+q.2 2^2 := by
      simpa only [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq q.2
    have hHoriz : q.2 0^2+q.2 1^2 ≤ B^2 := by nlinarith only [hNormSq,hSq,sq_nonneg (q.2 2)]
    have hGapAt : amin < ‖q.1-q.2‖/tubeHeight M e0 q.2^(1+σ) :=
      hGap ‖q.1-q.2‖ q.2 hq.2.2 (by linarith [(abs_le.mp hYCoord).1])
        (abs_le.mp hYCoord).2 hHoriz
    have hSepUpper : ‖q.1-q.2‖ < upper := by
      have hh := norm_sub_le q.1 q.2
      have hx := hq.1
      have hy := hq.2.1
      linarith
    have hc := tube_target_in_room (M := M) (e0 := e0) (σ := σ) (c0 := c0) (B := B)
      (T0 := T0) (amin := amin) (lower := lower) (upper := upper) (CY := CY)
      hc0 hσ he0.le hB.le hM hT0 hamin hTop (abs_le.mp hYCoord).1 hGapAt
      (fun Y hY hT => (hCenter Y hY hT).1) (hLowerD.trans_le hq.2.2) hSepUpper
    rcases hc with hc | ho
    · exact Or.inl hc
    · exact Or.inr (Or.inr ho)
  exact exists_fixed_separation_kernel_from_coarse_cone S L lam B d Bs ds c0 hlam hBsB hdsd
    N U F H0 hN (hND.trans hDSource) hF hF1 hF2 hURoom hInitial hH0 hH1 hH2 hCover hEqCone hTarget

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
theorem actual_mixed_kernel_exists : ActualMixedKernelConstructionGoal := by
  exact actualMixedKernelConstructionGoal_of_fixed_separation_product_producer fixed_separation_product_producer

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
