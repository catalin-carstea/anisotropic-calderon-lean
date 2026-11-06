import Calderon.NativeCoefficientWeakHalfLift
import Calderon.ActualReferenceWeakHalfLift
import Calderon.ActualReferenceFullWeakEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
lemma affineWeakLiftFormula_congr
    {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : V →L[ℝ] U) (P0 : X →L[ℝ] U)
    (I1 I2 : StrongDual ℝ V →L[ℝ] V)
    (R1 R2 : U →L[ℝ] StrongDual ℝ V) (hI : I1 = I2) (hR : R1 = R2) :
    ((ContinuousLinearMap.id ℝ U) - J.comp (I1.comp R1)).comp P0 =
      ((ContinuousLinearMap.id ℝ U) - J.comp (I2.comp R2)).comp P0 :=
  congrArg₂ (fun I R => ((ContinuousLinearMap.id ℝ U) - J.comp (I.comp R)).comp P0) hI hR

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! All identities hold for the SAME total definitions, including outside the invertible locus. -/

include hData

lemma referenceNativeEnergy_memLp (p : ℝ × (R3 × ℝ)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ha : Continuous (fun x : R3 => a (p,x)) :=
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hb : Continuous (fun x : R3 => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact memLp_nativeEnergyIntegrand_of_continuous (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 ha hb continuous_const

lemma referenceWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeCoefficientWeakEnergyL (fun x => a (p,x))
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v).trans
    (nativeCoefficientWeakEnergyL_apply (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff u v).symm

lemma referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    let R : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
    let N : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      nativeZeroCoefficientEnergyL (fun x => a (p,x))
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
    R = N := by
  let R : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let N : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
  change R = N
  have hR := referenceWeakDirichletEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc p
  have hN (u v : BallH1Zero) :=
    (nativeZeroCoefficientEnergyL_apply (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff u v).trans
        (TauCeti.PDE.energyFormH1L0_apply hcoeff u v)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (hR u v).trans (hN u v).symm

lemma referenceFullWeakEnergyFamily_eq_nativeEnergyFormH1L
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := fun x => a (p,x))
        (b := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) (c := 0) hcoeff := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (referenceFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v).trans
    (TauCeti.PDE.energyFormH1L_apply hcoeff u v).symm

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeZeroCoefficientEnergyL nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift

omit hData in
lemma nativeActualZeroFunctionalInverse_eq_functionalInverse
    (A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) :
    nativeZeroFunctionalInverse A0 = functionalInverse A0 := by
  apply ContinuousLinearMap.ext
  intro ell
  exact nativeZeroFunctionalInverse_apply A0 ell

omit hData in
lemma nativeCoefficientWeakFunctionalInverse_eq_nativeZeroInverse
    (a0 : MatrixField) (b0 : R3 → R3) (c0 : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) (b0 x) (c0 x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    nativeCoefficientWeakFunctionalInverse a0 b0 c0 hcoeff =
      nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a0 b0 c0 hcoeff) := by
  unfold nativeCoefficientWeakFunctionalInverse
  rfl

lemma referenceWeakHalfLiftFamily_eq_actualAffineFormula
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
    let R0 : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
    let J : BallH1Zero →L[ℝ] BallH1 :=
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    let P0 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
      ((ContinuousLinearMap.id ℝ BallH1) - J.comp ((functionalInverse A0).comp R0)).comp P0 := rfl

omit hData in
lemma nativeAffineWeakLiftFormula_congr
    (J : BallH1Zero →L[ℝ] BallH1) (P0 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1)
    (I1 I2 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero)
    (R1 R2 : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) (hI : I1 = I2) (hR : R1 = R2) :
    ((ContinuousLinearMap.id ℝ BallH1) - J.comp (I1.comp R1)).comp P0 =
      ((ContinuousLinearMap.id ℝ BallH1) - J.comp (I2.comp R2)).comp P0 := by
  cases hI
  cases hR
  rfl

lemma referenceWeakFunctionalInverse_apply_eq_nativeCoefficientWeakFunctionalInverse
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) (ell : StrongDual ℝ BallH1Zero) :
    let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
    functionalInverse A0 ell = K0 ell := by
  let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let N0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
  have hA : A0 = N0 := referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc p hcoeff
  have hRaw := nativeZeroFunctionalInverse_apply A0 ell
  have hZero := congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => nativeZeroFunctionalInverse T ell) hA
  unfold nativeCoefficientWeakFunctionalInverse
  exact hRaw.symm.trans hZero

lemma referenceWeakFunctionalInverse_eq_nativeCoefficientWeakFunctionalInverse
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    let A0 : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
    functionalInverse A0 = K0 := by
  apply ContinuousLinearMap.ext
  intro ell
  exact referenceWeakFunctionalInverse_apply_eq_nativeCoefficientWeakFunctionalInverse
    g L y0 Φ B ε C ρ H a w hData hcalc p hcoeff ell

lemma referenceWeakHalfLiftFamily_eq_nativeAffineFormula
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    let J : BallH1Zero →L[ℝ] BallH1 :=
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    let P0 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
    let RN : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
      nativeCoefficientWeakEnergyL (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
      ((ContinuousLinearMap.id ℝ BallH1) - J.comp (K0.comp RN)).comp P0 := by
  have hI := referenceWeakFunctionalInverse_eq_nativeCoefficientWeakFunctionalInverse
    g L y0 Φ B ε C ρ H a w hData hcalc p hcoeff
  have hR := referenceWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    g L y0 Φ B ε C ρ H a w hData hcalc p hcoeff
  have hActual := referenceWeakHalfLiftFamily_eq_actualAffineFormula
    g L y0 Φ B ε C ρ H a w hData hcalc hF p
  have hFormula := nativeAffineWeakLiftFormula_congr
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion hF) _ _ _ _ hI hR
  exact hActual.trans hFormula

omit hData in
lemma nativeWeakHalfLift_eq_nativeAffineFormula
    (a0 : MatrixField) (b0 : R3 → R3) (c0 : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) (b0 x) (c0 x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (hF : SphereFischerInner) :
    let J : BallH1Zero →L[ℝ] BallH1 :=
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    let P0 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
    let K0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
      nativeCoefficientWeakFunctionalInverse a0 b0 c0 hcoeff
    let RN : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
      nativeCoefficientWeakEnergyL a0 b0 c0 hcoeff
    nativeWeakHalfLift a0 b0 c0 hcoeff hF =
      ((ContinuousLinearMap.id ℝ BallH1) - J.comp (K0.comp RN)).comp P0 := by
  exact nativeWeakHalfLift_eq_affineAssembly a0 b0 c0 hcoeff hF

lemma referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x))
      (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
      nativeWeakHalfLift (fun x => a (p,x))
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff hF := by
  have hActual := referenceWeakHalfLiftFamily_eq_nativeAffineFormula
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hcoeff
  have hNative := nativeWeakHalfLift_eq_nativeAffineFormula (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff hF
  exact hActual.trans hNative.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeEnergy_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFullWeakEnergyFamily_eq_nativeEnergyFormH1L
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.affineWeakLiftFormula_congr

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAffineWeakLiftFormula_congr

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakFunctionalInverse_eq_nativeCoefficientWeakFunctionalInverse

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_eq_nativeAffineFormula

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_eq_nativeAffineFormula

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeActualZeroFunctionalInverse_eq_functionalInverse

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientWeakFunctionalInverse_eq_nativeZeroInverse

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_eq_actualAffineFormula

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakFunctionalInverse_apply_eq_nativeCoefficientWeakFunctionalInverse
