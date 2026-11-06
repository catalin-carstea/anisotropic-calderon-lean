import Calderon.ActualReferenceAdjointFiveHalfRadialCompatibility
import Calderon.ActualFiveHalfHorizontalConnection
import Calderon.ActualAdjointMovingBoundaryFamilyFoundation

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local irreducible] referenceAdjointFiveHalfRadialFamily referenceAdjointThreeHalfRadialFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceFiveHalfAdjointCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  -(∑ j : Fin 3, (sphereSobolevRotationL (5/2:ℝ) j i).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1))) +
  (referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1))

lemma contDiffAt_referenceFiveHalfAdjointCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun t => referenceFiveHalfAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i) p := by
  have hRad :=
    (contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  unfold referenceFiveHalfAdjointCoordinateBoundaryFamily
  exact contDiffAt_const.add (hRad.clm_comp contDiffAt_const)

lemma referenceAdjointCoordinateBoundaryFamily_fivehalf_threehalf_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceFiveHalfAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i) =
    (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  apply ContinuousLinearMap.ext
  intro u
  have hM (j : Fin 3) :
      Iin (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1) u) =
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single j 1) (Iin u) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD
      (5/2:ℝ) (3/2:ℝ) (by norm_num) (EuclideanSpace.single j 1) u
  have hT (j : Fin 3) :
      Iout (sphereSobolevRotationL (5/2:ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1) u)) =
      sphereSobolevRotationL (3/2:ℝ) j i
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2:ℝ) (EuclideanSpace.single j 1) (Iin u)) := by
    have hR := DFunLike.congr_fun (sphereSobolevRotationL_fivehalf_threehalf_compatibility j i)
      (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single j 1) u)
    exact hR.trans (congrArg (sphereSobolevRotationL (3/2:ℝ) j i) (hM j))
  have hR := DFunLike.congr_fun
    (referenceAdjointRadialEndpointFamily_fivehalf_threehalf_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hWeak)
    (sphereSobolevLinearCoordinateMulL hF hO hD (5/2:ℝ) (EuclideanSpace.single i 1) u)
  have hRad := hR.trans (congrArg
    (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (hM i))
  simp only [ContinuousLinearMap.comp_apply,referenceFiveHalfAdjointCoordinateBoundaryFamily,
    referenceHighAdjointCoordinateBoundaryFamily,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,map_add,map_neg,map_sum]
  exact congrArg₂ (fun a b : SphereSobolev (1/2:ℝ) => -a+b)
    (Finset.sum_congr rfl (fun j hj => hT j)) hRad
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
