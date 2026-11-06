import Calderon.SphereSobolevAngularRaisingThreeHalfGraph
import Calderon.ActualReferenceHighAdjointRadialNativeJets
import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.AngularShiftGraph
import Calderon.SharpRadialHarmonicCoefficientCore

/-! Actual zero coordinate action, TRUE model raising graph. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic AngularShiftGraph HarmonicDerivativeOperator

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceHighAdjointCoordinateBoundaryFamily sphereSobolevAngularCoordinateTransposeL

lemma referenceHighAdjointCoordinateBoundaryFamily_zero_raisingGraph
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) u),
     (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (q,(y,0)) i u))) ∈ sphereRaisingGraph hF hO hD i := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let C0 := referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 (q,(y,0)) i
  let A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    J.comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i)
  have hZero : C0 = sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i := by
    dsimp [C0]
    unfold referenceHighAdjointCoordinateBoundaryFamily sphereSobolevAngularCoordinateTransposeL
    rw [referenceAdjointThreeHalfRadialFamily_zero_eq_shiftedDegree
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy]
  have hGeneric : (Z.symm (I u),Z.symm (A u)) ∈ sphereRaisingGraph hF hO hD i :=
    sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph hF hO hD i u
  have hActualValue : J (C0 u) = A u :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      J (T u)) hZero
  have hPair := congrArg (fun v : SphereSobolev 0 => (Z.symm (I u),Z.symm v)) hActualValue
  exact (congrArg (fun pair : SphereL2 × SphereL2 =>
    pair ∈ sphereRaisingGraph hF hO hD i) hPair).mpr hGeneric

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily_zero_raisingGraph
