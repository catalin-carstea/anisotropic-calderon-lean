import Calderon.ActualHighAdjointUnweightedPointValue
import Calderon.RadiusSquaredFiveTermVectorCancellation
import Calderon.ActualFinitePairedRadialQuarticDomain
import Mathlib.Algebra.GroupWithZero.Action.Units

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

local instance referenceHighRadiusPowerPointwiseHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighRadiusPowerPointwiseOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighRadiusPowerPointwiseIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighRadiusPowerPointwiseEndIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceAdjointThreeHalfRadialFamily referenceHighAdjointCoordinateBoundaryFamily
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
  sphereSobolevLinearCoordinateMulL referenceRadiusHorizontalLogDerivative

lemma referenceHighAdjointMovingDifferenceQuotient_radiusPower_eqOn_ordered_extension
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    let Ω := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
    let T : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
    let N : Fin 3 → Fin 3 → R3 →
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i j y =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (χ y))
    let C0 : Fin 3 → R3 →
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j y =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun y =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    let E : ℕ → Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun power i y =>
      ((R y)^power • T y).comp (M i) +
      (∑ j : Fin 3, (C0 j y).comp ((R y)^power • N i j y)) +
      (∑ j : Fin 3, (D y).comp ((M j).comp ((R y)^(power+1) • N i j y))) +
      (∑ j : Fin 3, ((R y)^power • T y).comp ((M j).comp ((R y)^2 • N i j y))) +
      f i y • ((R y)^(power+1) • T y)
    ∀ power : ℕ, ∀ i : Fin 3, EqOn
      (fun y => (R y)^power • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i)
      (E power i) (closedBall y0 ρ ∩ U) := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E
  intro power i y hy
  apply ContinuousLinearMap.ext
  intro u
  have hPoint := referenceHighAdjointMovingDifferenceQuotient_apply_eq_ordered_sum
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
      y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2 i u
  have hScaled := congrArg
    (fun z : SphereSobolev (1/2 : ℝ) => (R y)^power • z) hPoint
  have hExpanded := pow_smul_ordered_five_term_vector_sum power (R y) (f i y)
    (T y (M i u)) (T y u) (fun j => C0 j y (N i j y u))
    (fun j => D y (M j (N i j y u))) (fun j => T y (M j (N i j y u)))
  have hValue := hScaled.trans hExpanded
  have hPowerComm : (R y)^power*(R y)^2 = (R y)^2*(R y)^power := mul_comm _ _
  exact (by simpa only [E,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_smul,smul_smul,hPowerComm]
    using hValue)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointMovingDifferenceQuotient_radiusPower_eqOn_ordered_extension
