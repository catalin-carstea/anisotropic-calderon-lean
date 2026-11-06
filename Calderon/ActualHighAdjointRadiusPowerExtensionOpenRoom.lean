import Calderon.ActualHighAdjointWeightedCorrectionOpenRoom
import Calderon.ActualFinitePairedRadialQuarticDomain

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

local instance referenceHighRadiusPowerExtensionOpenHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighRadiusPowerExtensionOpenOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighRadiusPowerExtensionOpenIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighRadiusPowerExtensionOpenEndIsBoundedSMul :
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

lemma contDiffOn_referenceHighAdjoint_radiusPower_ordered_extension
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
    ∀ power : ℕ, ∀ i : Fin 3, ContDiffOn ℝ ∞ (E power i) U := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hTWeighted := hOpen.2.1
  have hNWeighted := hOpen.2.2.1
  have hC0On := hOpen.2.2.2.1
  have hDOn := hOpen.2.2.2.2.1
  have hfOn := hOpen.2.2.2.2.2.1
  intro power i
  have h1 := (hTWeighted power).clm_comp (contDiffOn_const (c := M i))
  have h2 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
    (hC0On j).clm_comp (hNWeighted power i j))
  have h3 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
    hDOn.clm_comp ((contDiffOn_const (c := M j)).clm_comp (hNWeighted (power+1) i j)))
  have h4 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
    (hTWeighted power).clm_comp ((contDiffOn_const (c := M j)).clm_comp (hNWeighted 2 i j)))
  exact (((h1.add h2).add h3).add h4).add ((hfOn i).smul (hTWeighted (power+1)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceHighAdjoint_radiusPower_ordered_extension
