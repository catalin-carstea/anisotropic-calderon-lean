import Calderon.ActualFiveHalfAdjointCoordinateFamily
import Calderon.ActualJacobiFiveHalfCompactRoom
import Calderon.ActualHighAdjointJacobiBoundaryFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  referenceFiveHalfAdjointCoordinateBoundaryFamily referenceHighAdjointCoordinateBoundaryFamily
  ReferenceJacobiCompactExtensionRoom.fiveHalfMultiplierFamily
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hg : IsAdmissibleMetric g) {K : Set (ℝ × (R3 × ℝ))}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)

def referenceFiveHalfAdjointJacobiBoundaryInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ j : Fin 3, (referenceFiveHalfAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j).comp
      (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j p)

lemma contDiffAt_referenceFiveHalfAdjointJacobiBoundaryInRoom
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun t => referenceFiveHalfAdjointJacobiBoundaryInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i) p := by
  apply ContDiffAt.sum
  intro j hj
  exact (contDiffAt_referenceFiveHalfAdjointCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p j hp).clm_comp
      (E.contDiff_fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j).contDiffAt

lemma referenceAdjointJacobiBoundaryInRoom_fivehalf_threehalf_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3) (hp : p ∈ K)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceFiveHalfAdjointJacobiBoundaryInRoom g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 p i) =
    (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  apply ContinuousLinearMap.ext
  intro u
  have hTerm (j : Fin 3) :
      Iout (referenceFiveHalfAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j
          (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j p u)) =
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData i j p) (Iin u)) := by
    have hQ := DFunLike.congr_fun
      (referenceAdjointCoordinateBoundaryFamily_fivehalf_threehalf_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p j hWeak)
      (E.fiveHalfMultiplierFamily hcalc hF hO hD τ0 i j p u)
    have hM := DFunLike.congr_fun
      (E.eventually_fiveHalfMultiplierFamily_threeHalf_actual_eq
        hcalc hF hO hD τ0 p hp i j).self_of_nhds u
    exact hQ.trans (congrArg (referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j) hM)
  simp only [ContinuousLinearMap.comp_apply,referenceFiveHalfAdjointJacobiBoundaryInRoom,
    referenceHighAdjointJacobiBoundaryCorrectionFamily,ContinuousLinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun j hj => hTerm j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
