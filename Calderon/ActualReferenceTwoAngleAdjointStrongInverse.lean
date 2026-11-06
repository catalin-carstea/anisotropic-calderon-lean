import Calderon.ActualReferenceTwoAngleAdjointStrongEnergy
import Calderon.ActualReferenceTwoAngleNativeAdjointInverse
import Calderon.CompactInverseDerivativeBounds
/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-strong-inverse-v040.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTwoAngleAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp nativeStrongH2InclusionL

lemma referenceTwoAngleAdjointStrongDirichletFamily_eq_native (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t =
      nativeSupportedAdjointStrongDirichletL hcalc
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) 0
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t) :=
  congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 0 => T.comp nativeStrongH2InclusionL)
    (referenceTwoAngleAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
      g L y0 Φ B ε C ρ H a w hData i j k l hcalc t)

lemma contDiff_referenceTwoAngleAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l) :=
  (contDiff_referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).clm_comp contDiff_const

lemma referenceTwoAngleAdjointStrongDirichletFamily_isInvertible_of_original
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))).IsInvertible :=
  Eq.mp (congrArg (fun T : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => T.IsInvertible)
    (referenceTwoAngleAdjointStrongDirichletFamily_eq_native g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))).symm)
    (nativeReferenceTwoAngleSupportedAdjointStrongDirichletL_isInvertible g L y0 Φ B ε C ρ H a w hData
      τ0 hreg hcalc i j k l (θ,(φ,p)) hOriginal)

lemma contDiffOn_referenceTwoAngleAdjointStrongInverse_originalLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (ℝ × (R3 × ℝ))) =>
      (referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).inverse)
      (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  apply contDiffOn_banachInverseFamily _ _
    (contDiff_referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).contDiffOn
  intro t ht
  exact referenceTwoAngleAdjointStrongDirichletFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg i j k l t.1 t.2.1 t.2.2 ht.2.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointStrongDirichletFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointStrongDirichletFamily_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleAdjointStrongInverse_originalLocus
