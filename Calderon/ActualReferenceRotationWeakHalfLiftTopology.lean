import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeParameterWeakLiftTopology
import Calderon.ActualReferenceNativeWeakHalfLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

/-! Expanded before source in EXPANSION-actual-rotation-native-weak-lift-topology-v001.json.
SAME literal native total affine lift; smoothness only on its actual inverse locus. -/

def referenceRotationNativeWeakHalfLiftFamily (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  nativeWeakHalfLift
    (fun x => coordinateRotationPrincipalFamily i j a (t,x))
    (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift
  referenceRotationWeakEnergyFamily referenceRotationWeakDirichletEnergyFamily

lemma referenceRotationWeakFunctionalInverse_apply_eq_native
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (ell : StrongDual ℝ BallH1Zero) :
    let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
    functionalInverse A0 ell = K0 ell := by
  let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let N0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
  have hA : A0 = N0 := referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hRaw := nativeZeroFunctionalInverse_apply A0 ell
  have hZero := congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => nativeZeroFunctionalInverse T ell) hA
  unfold nativeCoefficientWeakFunctionalInverse
  exact hRaw.symm.trans hZero

lemma referenceRotationWeakFunctionalInverse_eq_native
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
    functionalInverse A0 = K0 := by
  apply ContinuousLinearMap.ext
  intro ell
  exact referenceRotationWeakFunctionalInverse_apply_eq_native g L y0 Φ B ε C ρ H a w hData hcalc i j t ell

lemma referenceRotationNativeWeakHalfLiftFamily_eq_affineFormula
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t =
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((functionalInverse (referenceRotationWeakDirichletEnergyFamily
            g L y0 Φ B ε C ρ H a w hData hcalc i j t)).comp
            (referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t))).comp
        (harmonicFirstOrderLiftCompletion hF) := by
  have hI := referenceRotationWeakFunctionalInverse_eq_native g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hR := referenceRotationWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hFormula := nativeAffineWeakLiftFormula_congr
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion hF) _ _ _ _ hI hR
  have hNative := nativeWeakHalfLift_eq_nativeAffineFormula
    (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF
  change nativeWeakHalfLift (fun x => coordinateRotationPrincipalFamily i j a (t,x)) (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF = _
  exact hNative.trans hFormula.symm

lemma contDiffAt_referenceRotationNativeWeakHalfLiftFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (p : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j) p := by
  have hFormula : ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((functionalInverse (referenceRotationWeakDirichletEnergyFamily
            g L y0 Φ B ε C ρ H a w hData hcalc i j t)).comp
            (referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t))).comp
        (harmonicFirstOrderLiftCompletion hF)) p := by
    apply contDiffAt_nativeParameterWeakHalfAffineLiftFormula (hF := hF)
    · exact (contDiff_referenceRotationWeakDirichletEnergyFamily_as_family g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt
    · exact (contDiff_referenceRotationWeakEnergyFamily_as_family g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt
    · exact hi
  exact contDiffAt_nativeParameterHalfLiftFamily_congr _ _ p hFormula
    (fun t => referenceRotationNativeWeakHalfLiftFamily_eq_affineFormula
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)

lemma contDiffOn_referenceRotationNativeWeakHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j)
      (referenceRotationWeakInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  intro t ht
  exact (contDiffAt_referenceRotationNativeWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t ht).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNativeWeakHalfLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNativeWeakHalfLiftFamily_eq_affineFormula
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationNativeWeakHalfLiftFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationNativeWeakHalfLiftFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakFunctionalInverse_apply_eq_native

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakFunctionalInverse_eq_native
