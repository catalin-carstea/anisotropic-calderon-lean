import Calderon.NativeFullSharpHalfTrace
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeH2CoefficientFluxGreen

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace
open NativeFullSharpHalfTrace SphereHarmonic SpectralCoreRegularity DirichletFamily EnergyBridge
  DirichletFamily.DriftBootstrap

def nativeHalfCoefficientConormalTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2) :
    BallSobolev 2 →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
      (EuclideanSpace.single i 1)).comp
      ((nativeHalfTraceL hF hO hD τ0).comp
        ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) 0).comp
          ((coefficientMultiplier hcalc 1 (F i j)).comp
            (unitBallCoordinateDerivativeL hcalc 1 j))))

lemma nativeHalfCoefficientConormalTraceL_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U =
      ∑ i : Fin 3, ∑ j : Fin 3,
        sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0
            (TauCeti.Wkp.firstOrder 0
              (coefficientMultiplier hcalc 1 (F i j)
                (unitBallCoordinateDerivativeL hcalc 1 j U)))) := by
  simp only [nativeHalfCoefficientConormalTraceL, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun v : BallH1 =>
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
      (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0 v))
    (TauCeti.Wkp.firstOrderL_apply (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0
      (coefficientMultiplier hcalc 1 (F i j)
        (unitBallCoordinateDerivativeL hcalc 1 j U)))

lemma sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U) =
        sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let q (i j : Fin 3) : BallH1 := TauCeti.Wkp.firstOrder 0
    (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U))
  let H (i j : Fin 3) : SphereSobolev (1/2 : ℝ) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
      (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0 (q i j))
  let B (i j : Fin 3) : SphereL2 := sphereCoordinateMulL i (τ0.valueTraceL (q i j))
  have hL := congrArg I (nativeHalfCoefficientConormalTraceL_apply hF hO hD hcalc τ0 F U)
  have hR := congrArg Z (ordinaryConormalTraceL_apply hcalc τ0 F U)
  have hTerm (i j : Fin 3) : I (H i j) = Z (B i j) := by
    have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (1/2 : ℝ)
      (by norm_num) (EuclideanSpace.single i 1) (nativeHalfTraceL hF hO hD τ0 (q i j))
      (τ0.valueTraceL (q i j)) (sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 (q i j))
    simpa only [I,Z,H,B,sphereLinearCoordinateMulL_single] using h
  have hSum : I (∑ i : Fin 3, ∑ j : Fin 3, H i j) =
      Z (∑ i : Fin 3, ∑ j : Fin 3, B i j) := by
    calc
      _ = ∑ i : Fin 3, I (∑ j : Fin 3, H i j) := map_sum I _ _
      _ = ∑ i : Fin 3, ∑ j : Fin 3, I (H i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact map_sum I _ _
      _ = ∑ i : Fin 3, ∑ j : Fin 3, Z (B i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hTerm i j
      _ = ∑ i : Fin 3, Z (∑ j : Fin 3, B i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (map_sum Z _ _).symm
      _ = _ := (map_sum Z _ _).symm
  exact hL.trans (hSum.trans hR.symm)

lemma sphereSobolevCoefficientL_nativeHalfCoefficientConormalTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (U : BallSobolev 2) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k
      (nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U) =
        sphereHarmonicCoordinate hO hD k (ordinaryConormalTraceL hcalc τ0 F U) := by
  have h := congrArg (sphereSobolevCoefficientL 0 k)
    (sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U)
  simpa only [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_zeroEquiv] using h

def nativeH2LiftHalfConormalL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (W : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F).comp W

lemma nativeH2LiftHalfConormalL_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (W : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2)
    (f : SphereSobolev (3/2 : ℝ)) :
    nativeH2LiftHalfConormalL hF hO hD hcalc τ0 F W f =
      nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F (W f) := rfl

lemma norm_nativeH2LiftHalfConormalL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (hcalc : FixedSobolevCalculus)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (W : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2) :
    ‖nativeH2LiftHalfConormalL hF hO hD hcalc τ0 F W‖ ≤
      ‖nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F‖ * ‖W‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

end OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace

#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.nativeHalfCoefficientConormalTraceL
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.nativeHalfCoefficientConormalTraceL_apply
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.sphereSobolevCoefficientL_nativeHalfCoefficientConormalTraceL
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.nativeH2LiftHalfConormalL
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.nativeH2LiftHalfConormalL_apply
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientConormalTrace.norm_nativeH2LiftHalfConormalL_le
