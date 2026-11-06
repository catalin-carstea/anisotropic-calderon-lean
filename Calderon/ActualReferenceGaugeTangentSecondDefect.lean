import Calderon.ActualReferenceGaugeTangentOperator
import Calderon.ActualReferenceGaugeNormalMultiplierInverse
import Calderon.ActualAdjointMovingBoundaryFamilyFoundation

/-! First component: SAME lower tangent term. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceGaugeTangentSecondEndpointFamily
  referenceGaugeNormalHalfMultiplierFamily sphereLowerDistributionalTranspose
  sphereLowerDistributionalTransposeL ContinuousLinearMap.inverse

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeTangentSecondDefectFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p -
    sphereLowerDistributionalTranspose (referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse

theorem contDiff_referenceGaugeTangentSecondDefectFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondDefectFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  let T := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  have hT : ContDiff ℝ ∞ T := contDiff_referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  letI : NormedAddCommGroup
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let t : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := sphereLowerDistributionalTranspose
      map_add' := fun U V => by
        have h := sphereLowerDistributionalTransposeL.map_add U V
        simpa only [sphereLowerDistributionalTransposeL_apply] using h
      map_smul' := fun c U => by
        have h := sphereLowerDistributionalTransposeL.map_smul c U
        simpa only [sphereLowerDistributionalTransposeL_apply,RingHom.id_apply] using h }
  have hBound : ∀ U : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)),
      ‖t U‖ ≤ (1 : ℝ) * ‖U‖ := by
    intro U
    have hAdj : t U = ContinuousLinearMap.adjoint U := by
      change sphereLowerDistributionalTranspose U = ContinuousLinearMap.adjoint U
      unfold sphereLowerDistributionalTranspose sphereHalfDualCarrierEquiv
      apply ContinuousLinearMap.ext
      intro u
      rfl
    have hNorm : ‖t U‖ ≤ ‖U‖ :=
      (congrArg (fun V : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => ‖V‖) hAdj).le.trans
          (ContinuousLinearMap.adjoint.norm_map U).le
    simpa only [one_mul] using hNorm
  let Lt : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      t (1 : ℝ) hBound
  have hTranspose := Lt.contDiff.comp hT
  have hCurve : (fun p : ℝ × (R3 × ℝ) => Lt (T p)) =
      (fun p => sphereLowerDistributionalTranspose (T p)) := by
    funext p
    rfl
  have hNamed : ContDiff ℝ ∞ (fun p => sphereLowerDistributionalTranspose (T p)) :=
    hCurve ▸ hTranspose
  have hW := contDiff_referenceGaugeNormalHalfMultiplierFamily_inverse
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0
  unfold referenceGaugeTangentSecondDefectFamily
  exact (hT.sub hNamed).clm_comp hW

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondDefectFamily
