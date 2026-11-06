import Calderon.ActualNativeMovingLowerLocalRemainderSmoothness
import Calderon.ActualPairedRadialRemainderProfileLocalSmoothness
import Calderon.ActualReferencePairedLowRadialRemainderLocalSmoothness
import Calderon.ActualJacobiNativeMultiplierProfileLocalSmoothness
import Calderon.JointRadialDerivativeLocalSmoothness
import Calderon.ActualFinitePairedRadialQuarticDomain

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

local instance referenceLowerWeightedCorrectionOpenNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceLowerWeightedCorrectionOpenOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

local instance referenceLowerWeightedCorrectionOpenIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceLowerWeightedCorrectionOpenEndIsBoundedSMul :
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

lemma contDiffOn_referenceLowerAdjoint_weighted_correction_open_room
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
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    IsOpen U ∧
    (∀ power : ℕ, ContDiffOn ℝ ∞ (fun y => (R y)^power • T y) U) ∧
    (∀ power : ℕ, ∀ i j : Fin 3,
      ContDiffOn ℝ ∞ (fun y => (R y)^power • N i j y) U) ∧
    (∀ j : Fin 3, ContDiffOn ℝ ∞ (C0 j) U) ∧ ContDiffOn ℝ ∞ D U ∧
    (∀ i : Fin 3, ContDiffOn ℝ ∞ (f i) U) ∧
    (∀ power : ℕ, ∀ i : Fin 3, ContDiffOn ℝ ∞ (fun y => (R y)^power •
      referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U) := by
  classical
  intro Ω SegΩ V χ U T N C0 D f
  have hPaired := exists_referencePairedRadialRemainder_profile_open_room
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hJacobi := exists_referenceJacobiNativeMultiplier_profile_open_room
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hU : IsOpen U := (isOpen_ne_fun hR.continuous continuous_const).inter
    ((hPaired.1.preimage hχ.continuous).inter (hJacobi.1.preimage hχ.continuous))
  have hTOn : ContDiffOn ℝ ∞ T U := by
    intro y hy
    have hActual := contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1
    exact (hActual.2.comp y hχ.contDiffAt).contDiffWithinAt
  have hNOn (i j : Fin 3) : ContDiffOn ℝ ∞ (N i j) U := by
    intro y hy
    have hActual := contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (χ y) hy.2.2
    exact (hActual.comp y hχ.contDiffAt).contDiffWithinAt
  have hTWeighted (power : ℕ) : ContDiffOn ℝ ∞ (fun y => (R y)^power • T y) U :=
    (hR.pow power).contDiffOn.smul hTOn
  have hNWeighted (power : ℕ) (i j : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => (R y)^power • N i j y) U :=
    (hR.pow power).contDiffOn.smul (hNOn i j)
  have hZero (y : R3) (hy : y ∈ U) : (q,(y,(0 : ℝ))) ∈ Ω := by
    simpa only [zero_mul] using hy.2.1 0 ⟨le_refl 0,zero_le_one⟩
  let A : (ℝ × (R3 × ℝ)) →
      SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let DJoint : (ℝ × (R3 × ℝ)) →
      SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun z =>
    deriv (fun t : ℝ => A (z.1,(z.2.1,t))) z.2.2
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hA : ContDiffOn ℝ ∞ A Ω := contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hC0On (j : Fin 3) : ContDiffOn ℝ ∞ (C0 j) U := by
    intro y hy
    have hRad := (hA.contDiffAt (hΩ.mem_nhds (hZero y hy))).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))
    have hActual : ContDiffAt ℝ ∞ (fun z : R3 => referenceLowerAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(z,0)) j) y := by
      unfold referenceLowerAdjointCoordinateBoundaryFamily
      exact contDiffAt_const.add (hRad.clm_comp contDiffAt_const)
    exact hActual.contDiffWithinAt
  have hDJoint : ContDiffOn ℝ ∞ DJoint Ω := contDiffOn_deriv_joint_radialSlice A Ω hΩ hA
  have hDOn : ContDiffOn ℝ ∞ D U := by
    intro y hy
    exact ((hDJoint.contDiffAt (hΩ.mem_nhds (hZero y hy))).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).contDiffWithinAt
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := by
    intro y hy
    exact ((contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i
      hR.contDiffAt hy.1).comp y (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hQuotientOn (power : ℕ) (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => (R y)^power •
      referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U := by
    intro y hy
    have hCurrent : (q,(y,R y)) ∈ Ω := by
      simpa only [one_mul] using hy.2.1 1 ⟨zero_le_one,le_refl 1⟩
    have hActual := contDiffAt_referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i
        hR.contDiffAt hy.1 hy.2.2 hCurrent
    exact ((hR.pow power).contDiffAt.smul hActual).contDiffWithinAt
  exact ⟨hU,hTWeighted,hNWeighted,hC0On,hDOn,hfOn,hQuotientOn⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceLowerAdjoint_weighted_correction_open_room
