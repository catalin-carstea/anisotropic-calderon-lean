import Calderon.ActualLowerAdjointRadiusPowerExtensionOpenRoom
import Calderon.ActualLowerAdjointRadiusPowerPointwiseIdentity
import Calderon.ActualLowerAdjointWeightedCorrectionOpenRoom
import Calderon.ActualFinitePairedRadialQuarticDomain
import Calderon.LocalCoordinateWordEqOnTransport
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ReferenceDensityBounds

local instance referenceLowerRadiusPowerWeightedWordDictionaryNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceLowerRadiusPowerWeightedWordDictionaryOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

local instance referenceLowerRadiusPowerWeightedWordDictionaryIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceLowerRadiusPowerWeightedWordDictionaryEndIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointHalfRadialFamily referenceLowerAdjointCoordinateBoundaryFamily
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  nativeHalfCoefficientMulL referenceJacobiBoundaryCoefficientFamily
  sphereSobolevLinearCoordinateMulL referenceRadiusHorizontalLogDerivative

lemma referenceLowerAdjointMovingDifferenceQuotient_radiusPower_word_eq_ordered_extension
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
    let T : R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun y =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y)
    let N : Fin 3 → Fin 3 → R3 →
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i j y =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j (χ y))
    let C0 : Fin 3 → R3 →
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun j y =>
      referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D : R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun y =>
      deriv (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    let E : ℕ → Fin 3 → R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun power i y =>
      ((R y)^power • T y).comp (M i) +
      (∑ j : Fin 3, (C0 j y).comp ((R y)^power • N i j y)) +
      (∑ j : Fin 3, (D y).comp ((M j).comp ((R y)^(power+1) • N i j y))) +
      (∑ j : Fin 3, ((R y)^power • T y).comp ((M j).comp ((R y)^2 • N i j y))) +
      f i y • ((R y)^(power+1) • T y)
    IsOpen U ∧ ∀ power : ℕ, ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (E power i) U ∧
      ContDiffOn ℝ ∞ (fun y => (R y)^power •
        referenceLowerAdjointMovingDifferenceQuotient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U ∧
      ∀ word : List (Fin 3), EqOn
        (coordinateFieldWordPartial word (fun y => (R y)^power •
          referenceLowerAdjointMovingDifferenceQuotient
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i))
        (coordinateFieldWordPartial word (E power i)) (closedBall y0 ρ ∩ U) := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E
  have hOpen := contDiffOn_referenceLowerAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hExtension := contDiffOn_referenceLowerAdjoint_radiusPower_ordered_extension
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hPointwise := referenceLowerAdjointMovingDifferenceQuotient_radiusPower_eqOn_ordered_extension
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hUnique : UniqueDiffOn ℝ (closedBall y0 ρ ∩ U) :=
    (uniqueDiffOn_convex (convex_closedBall y0 ρ)
      ⟨y0,ball_subset_interior_closedBall (mem_ball_self hData.1.2.1)⟩).inter hU
  refine ⟨hU,?_⟩
  intro power i
  have hEOn : ContDiffOn ℝ ∞ (E power i) U := hExtension power i
  have hQuotientOn : ContDiffOn ℝ ∞ (fun y => (R y)^power •
      referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U :=
    hOpen.2.2.2.2.2.2 power i
  refine ⟨hEOn,hQuotientOn,?_⟩
  intro word
  exact coordinateFieldWordPartial_eqOn_of_uniqueDiffOn word _ _ U (closedBall y0 ρ ∩ U)
    hU (fun _ hy => hy.2) hUnique hQuotientOn hEOn (hPointwise power i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingDifferenceQuotient_radiusPower_word_eq_ordered_extension
