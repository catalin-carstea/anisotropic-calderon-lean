import Calderon.ActualLowerAdjointMovingQuotientOrderedWords
import Calderon.OrderedCompositionRadiusPowerWordBounds
import Calderon.ActualJacobiBoundaryMultiplierFamily
import Calderon.ActualFinitePairedRadialQuarticDomain
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

local instance referenceLowerRadiusPowerPointwiseNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceLowerRadiusPowerPointwiseOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

local instance referenceLowerRadiusPowerPointwiseIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceLowerRadiusPowerPointwiseEndIsBoundedSMul :
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

lemma referenceLowerAdjointMovingDifferenceQuotient_radiusPower_eqOn_ordered_extension
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
    ∀ power : ℕ, ∀ i : Fin 3, EqOn
      (fun y => (R y)^power • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i)
      (E power i) (closedBall y0 ρ ∩ U) := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E
  intro power i
  intro y hy
  have hSegment : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈ Ω := by
    intro t ht
    have htSeg : t ∈ segment ℝ (0 : ℝ) (R y) := by
      simpa only [segment_eq_uIcc] using ht
    rcases htSeg with ⟨a,b,ha,hb,hab,heq⟩
    have hb1 : b ≤ 1 := by linarith only [ha,hab]
    have ht' : b*(R y) = t := by simpa only [smul_zero,zero_add,smul_eq_mul,mul_zero] using heq
    exact ht' ▸ hy.2.2.1 b ⟨hb,hb1⟩
  have hInv := hy.2.2.2
  have hQ := referenceLowerAdjointMovingDifferenceQuotient_eq_ordered_words
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y
    (mem_closedBall_iff_norm.mp hy.1) R hR i hy.2.1 hInv hSegment
  dsimp only at hQ
  have hWeighted := congrArg
    (fun F : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => (R y)^power • F) hQ
  have hNsame (j : Fin 3) : N i j y = nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientJets
        g hg L y0 Φ B ε C ρ H a w hData q y (R y) i j hInv) :=
    congrArg (nativeHalfCoefficientMulL hcalc hF hO hD τ0)
      (referenceJacobiBoundaryCoefficientFamily_eq
        g hg L y0 Φ B ε C ρ H a w hData i j (χ y) hInv)
  simp only [← hNsame] at hWeighted
  have hAlgebra := radiusPower_smul_ordered_composition_sum power (R y) (f i y)
    (T y) (D y) (fun j => C0 j y) (M i) M (fun j => N i j y)
  exact hWeighted.trans (by simpa only [E,T,C0,D,M,f] using hAlgebra)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerAdjointMovingDifferenceQuotient_radiusPower_eqOn_ordered_extension
