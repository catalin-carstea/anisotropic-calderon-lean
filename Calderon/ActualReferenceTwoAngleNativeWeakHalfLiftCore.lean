import Calderon.ActualReferenceTwoAngleNativeEnergyIdentification
import Calderon.ActualReferenceTwoAngleWeakCovariance
import Calderon.ActualReferenceNativeWeakHalfLift
import Calderon.NativeParameterWeakLiftTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def referenceTwoAngleNativeWeakHalfLiftFamily (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
  nativeWeakHalfLift (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily

lemma referenceTwoAngleWeakFunctionalInverse_eq_native
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    functionalInverse (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t) =
    nativeCoefficientWeakFunctionalInverse
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) := by
  apply ContinuousLinearMap.ext
  intro ell
  have hA := referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeZeroEnergy
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hRaw := nativeZeroFunctionalInverse_apply
    (referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t) ell
  have hZero := congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => nativeZeroFunctionalInverse T ell) hA
  unfold nativeCoefficientWeakFunctionalInverse
  exact hRaw.symm.trans hZero

lemma referenceTwoAngleNativeWeakHalfLiftFamily_eq_affineFormula
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t =
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((functionalInverse (referenceTwoAngleWeakDirichletEnergyFamily
            g L y0 Φ B ε C ρ H a w hData hcalc i j k l t)).comp
            (referenceTwoAngleWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t))).comp
        (harmonicFirstOrderLiftCompletion hF) := by
  have hI := referenceTwoAngleWeakFunctionalInverse_eq_native
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hR := referenceTwoAngleWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hFormula := nativeAffineWeakLiftFormula_congr
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion hF) _ _ _ _ hI hR
  have hNative := nativeWeakHalfLift_eq_nativeAffineFormula
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF
  exact hNative.trans hFormula.symm

lemma referenceTwoAngleNativeWeakHalfLiftFamily_affine_difference
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (f : SphereSobolev (1/2 : ℝ)) :
    harmonicFirstOrderLiftCompletion hF f -
      referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t f ∈
        TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
  nativeWeakHalfLift_affine_difference
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF f

lemma referenceTwoAngleNativeWeakHalfLiftFamily_weak_solution
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t f)
      (v : BallH1) = 0 := by
  have hActual := referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t.1 t.2.1 t.2.2 hOriginal
  have hEq := referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeZeroEnergy
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hZero : (nativeZeroCoefficientEnergyL
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)).IsInvertible :=
    Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) hEq) hActual
  have hNative := (nativeZeroCoefficientEnergyL_isInvertible_iff
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)).mp hZero
  exact nativeWeakHalfLift_weak_solution
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF hNative f v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeWeakHalfLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakFunctionalInverse_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeWeakHalfLiftFamily_eq_affineFormula
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeWeakHalfLiftFamily_affine_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeWeakHalfLiftFamily_weak_solution
