import Calderon.ActualHighAdjointRadiusPowerWordDictionary
import Calderon.ActualHighAdjointOrderedRadiusPowerExtensionWordBounds
import Calderon.OrderedCompositionRadiusPowerWordBounds
import Calderon.ActualFinitePairedRadialQuarticDomain

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ReferenceDensityBounds

local instance referenceHighPointRadiusPowerWordsHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighPointRadiusPowerWordsOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighPointRadiusPowerWordsIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighPointRadiusPowerWordsEndIsBoundedSMul :
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

lemma norm_referenceHighAdjointMovingDifferenceQuotient_radiusPower_coordinate_word_le_of_primitive_jets
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
    ∀ x ∈ closedBall y0 ρ, x ∈ U →
      ∀ Cscaled B0 F0 m0 beta eta : ℝ,
      0 ≤ Cscaled → 0 ≤ B0 → 0 ≤ F0 →
      (∀ j : Fin 3, ‖M j‖ ≤ m0) → 1 ≤ beta → 0 ≤ eta → eta ≤ 1 →
      ∀ i : Fin 3,
      (∀ a : ℕ, 1 ≤ a → a ≤ 3 → ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y => (R y)^a • T y) x‖ ≤
          Cscaled*eta^a*beta^order/beta^(2*a) ∧
        ∀ k j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y => (R y)^a • N k j y) x‖ ≤
          Cscaled*eta^a*beta^order/beta^(2*a)) →
      (∀ j : Fin 3, HasCoordinateWordJetBound 3 (C0 j) x B0 beta 0) →
      HasCoordinateWordJetBound 3 D x B0 beta 0 →
      HasCoordinateWordJetBound 3 (f i) x F0 beta 1 →
      ∀ power : ℕ, 1 ≤ power → power ≤ 2 →
      ∀ word : List (Fin 3), word.length ≤ 3 →
        ‖coordinateFieldWordPartial word (fun y => (R y)^power •
          referenceHighAdjointMovingDifferenceQuotient
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
          (Cscaled*m0+24*B0*Cscaled+24*B0*m0*Cscaled+
            24*Cscaled^2*m0+8*F0*Cscaled)*eta^power*beta^word.length/beta^(2*power) := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E x hxBall hxU
  intro Cscaled B0 F0 m0 beta eta hC0 hB0 hF0 hM0 hbeta heta heta1 i
  intro hRaw hC0Bound hDBound hfBound power hpower1 hpower2 word hw
  have hEstimate := norm_referenceHighAdjoint_ordered_radiusPower_extension_coordinate_word_le_of_primitive_jets
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
    x hxBall hxU Cscaled B0 F0 m0 beta eta hC0 hB0 hF0 hM0 hbeta heta heta1 i
    hRaw hC0Bound hDBound hfBound power hpower1 hpower2 word hw
  have hEstimate' : ‖coordinateFieldWordPartial word (E power i) x‖ ≤
      (Cscaled*m0+24*B0*Cscaled+24*B0*m0*Cscaled+
        24*Cscaled^2*m0+8*F0*Cscaled)*eta^power*beta^word.length/beta^(2*power) := hEstimate
  have hDictionary := referenceHighAdjointMovingDifferenceQuotient_radiusPower_word_eq_ordered_extension
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hOriginalWord := (hDictionary.2 power i).2.2 word ⟨hxBall,hxU⟩
  change coordinateFieldWordPartial word (fun y => (R y)^power •
    referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x =
    coordinateFieldWordPartial word (E power i) x at hOriginalWord
  change ‖coordinateFieldWordPartial word (fun y => (R y)^power •
    referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
    (Cscaled*m0+24*B0*Cscaled+24*B0*m0*Cscaled+
      24*Cscaled^2*m0+8*F0*Cscaled)*eta^power*beta^word.length/beta^(2*power)
  rw [hOriginalWord]
  exact hEstimate'


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceHighAdjointMovingDifferenceQuotient_radiusPower_coordinate_word_le_of_primitive_jets
