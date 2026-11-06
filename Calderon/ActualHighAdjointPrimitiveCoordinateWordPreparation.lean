import Calderon.ActualHighAdjointWeightedCorrectionOpenRoom
import Calderon.ActualReferenceLocalCoordinateWordJets
import Calderon.ActualFinitePairedRadialQuarticDomain
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ReferenceDensityBounds

local instance referenceHighPrimitiveCoordinateWordsHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighPrimitiveCoordinateWordsOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighPrimitiveCoordinateWordsIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighPrimitiveCoordinateWordsEndIsBoundedSMul :
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

lemma referenceHighAdjoint_weighted_primitive_coordinate_word_preparation
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
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    ∀ x ∈ U, ∀ Cscaled beta eta : ℝ,
      (∀ a : ℕ, 1 ≤ a → a ≤ 3 → ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y => (R y)^a • T y) x‖ ≤
          Cscaled*eta^a*beta^order/beta^(2*a) ∧
        ∀ k j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y => (R y)^a • N k j y) x‖ ≤
          Cscaled*eta^a*beta^order/beta^(2*a)) →
      IsOpen U ∧
      (∀ a : ℕ, ContDiffOn ℝ ∞ (fun y => (R y)^a • T y) U) ∧
      (∀ (a : ℕ) (k j : Fin 3), ContDiffOn ℝ ∞ (fun y => (R y)^a • N k j y) U) ∧
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (C0 j) U) ∧
      ContDiffOn ℝ ∞ D U ∧
      (∀ i : Fin 3, ContDiffOn ℝ ∞ (f i) U) ∧
      (∀ a : ℕ, 1 ≤ a → a ≤ 3 →
        HasCoordinateWordJetBound 3 (fun y => (R y)^a • T y) x
          (Cscaled*eta^a/beta^(2*a)) beta 0) ∧
      (∀ a : ℕ, 1 ≤ a → a ≤ 3 → ∀ k j : Fin 3,
        HasCoordinateWordJetBound 3 (fun y => (R y)^a • N k j y) x
          (Cscaled*eta^a/beta^(2*a)) beta 0) := by
  intro Ω SegΩ V χ U T N C0 D f x hxU Cscaled beta eta hRaw
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hTOn (a : ℕ) : ContDiffOn ℝ ∞ (fun y => (R y)^a • T y) U :=
    hOpen.2.1 a
  have hNOn (a : ℕ) (k j : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => (R y)^a • N k j y) U := hOpen.2.2.1 a k j
  have hC0On (j : Fin 3) : ContDiffOn ℝ ∞ (C0 j) U := hOpen.2.2.2.1 j
  have hDOn : ContDiffOn ℝ ∞ D U := hOpen.2.2.2.2.1
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := hOpen.2.2.2.2.2.1 i
  have hTBound (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) :
      HasCoordinateWordJetBound 3 (fun y => (R y)^a • T y) x
        (Cscaled*eta^a/beta^(2*a)) beta 0 := by
    intro v hv
    have hPrimitive := hRaw a ha1 ha3 v.length hv
    have hJet : ‖iteratedFDeriv ℝ v.length (fun y => (R y)^a • T y) x‖ ≤
        Cscaled*eta^a*beta^v.length/beta^(2*a) := hPrimitive.1
    calc
      _ ≤ ‖iteratedFDeriv ℝ v.length (fun y => (R y)^a • T y) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen
          v _ U hU (hTOn a) x hxU
      _ ≤ Cscaled*eta^a*beta^v.length/beta^(2*a) := hJet
      _ = (Cscaled*eta^a/beta^(2*a))*beta^(0+v.length) := by
        simp only [Nat.zero_add]; ring
  have hNBound (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (k j : Fin 3) :
      HasCoordinateWordJetBound 3 (fun y => (R y)^a • N k j y) x
        (Cscaled*eta^a/beta^(2*a)) beta 0 := by
    intro v hv
    have hPrimitive := hRaw a ha1 ha3 v.length hv
    have hJet : ‖iteratedFDeriv ℝ v.length (fun y => (R y)^a • N k j y) x‖ ≤
        Cscaled*eta^a*beta^v.length/beta^(2*a) := hPrimitive.2 k j
    calc
      _ ≤ ‖iteratedFDeriv ℝ v.length (fun y => (R y)^a • N k j y) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen
          v _ U hU (hNOn a k j) x hxU
      _ ≤ Cscaled*eta^a*beta^v.length/beta^(2*a) := hJet
      _ = (Cscaled*eta^a/beta^(2*a))*beta^(0+v.length) := by
        simp only [Nat.zero_add]; ring
  exact ⟨hU,hTOn,hNOn,hC0On,hDOn,hfOn,hTBound,hNBound⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjoint_weighted_primitive_coordinate_word_preparation
