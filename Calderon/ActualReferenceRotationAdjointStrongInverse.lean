import Calderon.ActualReferenceRotationAdjointStrongEnergy
import Calderon.ActualReferenceRotationNativeAdjointStrongInverse
import Calderon.CompactInverseDerivativeBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
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

def referenceRotationAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp nativeStrongH2InclusionL

lemma referenceRotationAdjointStrongDirichletFamily_eq_native (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      nativeSupportedAdjointStrongDirichletL hcalc
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) 0
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 t) :=
  congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 0 => T.comp nativeStrongH2InclusionL)
    (referenceRotationAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
      g L y0 Φ B ε C ρ H a w hData i j hcalc t)

lemma contDiff_referenceRotationAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) :=
  (contDiff_referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).clm_comp contDiff_const

lemma referenceRotationAdjointStrongDirichletFamily_isInvertible_of_original
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible :=
  Eq.mp (congrArg (fun T : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => T.IsInvertible)
    (referenceRotationAdjointStrongDirichletFamily_eq_native g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).symm)
    (nativeReferenceRotationAdjointStrongDirichletL_isInvertible g L y0 Φ B ε C ρ H a w hData
      τ0 hcalc hreg i j θ p hOriginal)

lemma contDiffOn_referenceRotationAdjointStrongInverse_originalLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      (referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).inverse)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  apply contDiffOn_banachInverseFamily _ _
    (contDiff_referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffOn
  intro t ht
  exact referenceRotationAdjointStrongDirichletFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg i j t.1 t.2 ht.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointStrongDirichletFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointStrongDirichletFamily_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointStrongInverse_originalLocus
