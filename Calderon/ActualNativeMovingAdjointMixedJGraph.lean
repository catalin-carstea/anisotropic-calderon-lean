import Calderon.ActualNativeMovingAdjointMixedJRealization

/-! The actual ordered mixed zero/first expression, with the same finite-J graph and bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic AngularShiftGraph
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  sphereSobolevAngularCoordinateTransposeL referenceNativeMovingAdjointParametricCorrection
  referenceNativeMovingAdjointParametricJ referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL

attribute [local irreducible] referenceNativeMovingAdjointHighMixedCorrection

lemma referenceNativeMovingAdjointHighMixedCorrection_inclusion
    (g2 : MatrixField) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (ell : R3 →L[ℝ] ℝ) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (referenceNativeMovingAdjointHighMixedCorrection g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y ell u) =
      referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)
        (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u) := by
  let I := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let U := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u
  have hA (i : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      I (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i v) = (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) v)) :=
    referenceHighAdjointCoordinateBoundaryFamily_zero_inclusion_one
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i v
  have hAF (i j : Fin 3) :
      I (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),ell) j u)) = (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 1 ((q,y),ell) j U)) := by
    have hFgraph := referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD
      g L (3/2 : ℝ) 1 (by norm_num) ((q,y),ell) j u
    exact (hA i _).trans
      (congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i) hFgraph)
  have hFA (i j : Fin 3) :
      I (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),ell) i (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j u)) = (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 ((q,y),ell) i (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 j U)) := by
    have hFgraph := referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD
      g L (1/2 : ℝ) 0 (by norm_num) ((q,y),ell) i (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j u)
    exact hFgraph.trans (congrArg
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L 0 ((q,y),ell) i)
      (hA j u))
  simp (config := { instances := true }) only
    [referenceNativeMovingAdjointHighMixedCorrection,referenceNativeMovingAdjointParametricJ,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_add,map_smul,map_sum]
  apply congrArg₂ (fun v z : SphereSobolev 0 => v+z)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun v : SphereSobolev 0 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j • v)
      (congrArg₂ (fun v z : SphereSobolev 0 => v+z) (hAF i j) (hFA i j))
  · apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun v : SphereSobolev 0 => normalizedSecondDriftFrameJoint g g2 L i (q,y) • v) (hA i u)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointHighMixedCorrection_inclusion
