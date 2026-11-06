import Calderon.ActualHighAdjointWeightedQuotientOpenRoom
import Calderon.ActualPairedRadialRemainderProfileLocalSmoothness
import Calderon.JointRadialDerivativeLocalSmoothness

/-! Full BEFORE-SOURCE dictionary declaration split v081. Actual open smoothness only; no word or gain premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

local instance referenceHighWeightedCorrectionOpenHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighWeightedCorrectionOpenOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighWeightedCorrectionOpenIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighWeightedCorrectionOpenEndIsBoundedSMul :
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

lemma contDiffOn_referenceHighAdjoint_weighted_correction_open_room
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
    let E : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i y =>
      ((R y)^2 • T y).comp (M i) +
      (∑ j : Fin 3, (C0 j y).comp ((R y)^2 • N i j y)) +
      (∑ j : Fin 3, (D y).comp ((M j).comp ((R y)^3 • N i j y))) +
      (∑ j : Fin 3, ((R y)^2 • T y).comp ((M j).comp ((R y)^2 • N i j y))) +
      f i y • ((R y)^3 • T y)
    IsOpen U ∧
    (∀ power : ℕ, ContDiffOn ℝ ∞ (fun y => (R y)^power • T y) U) ∧
    (∀ power : ℕ, ∀ i j : Fin 3,
      ContDiffOn ℝ ∞ (fun y => (R y)^power • N i j y) U) ∧
    (∀ j : Fin 3, ContDiffOn ℝ ∞ (C0 j) U) ∧ ContDiffOn ℝ ∞ D U ∧
    (∀ i : Fin 3, ContDiffOn ℝ ∞ (f i) U) ∧
    (∀ i : Fin 3, ContDiffOn ℝ ∞ (E i) U) ∧
    (∀ i : Fin 3, ContDiffOn ℝ ∞ (fun y => (R y)^2 •
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U) := by
  classical
  intro Ω SegΩ V χ U T N C0 D M f E
  have hPaired := exists_referencePairedRadialRemainder_profile_open_room
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hJacobi := exists_referenceJacobiNativeMultiplier_profile_open_room
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hNatural := contDiffOn_referenceHighAdjointMovingDifferenceQuotient_weighted_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hU : IsOpen U := (isOpen_ne_fun hR.continuous continuous_const).inter
    ((hPaired.1.preimage hχ.continuous).inter (hJacobi.1.preimage hχ.continuous))
  have hTOn : ContDiffOn ℝ ∞ T U := by
    intro y hy
    have hActual := contDiffAt_referencePairedRadialSecondRemainder_product_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1
    exact (hActual.2.fst.comp y hχ.contDiffAt).contDiffWithinAt
  have hNOn (i j : Fin 3) : ContDiffOn ℝ ∞ (N i j) U := by
    intro y hy
    have hActual := contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (χ y) hy.2.2
    exact (hActual.comp y hχ.contDiffAt).contDiffWithinAt
  have hTWeighted (power : ℕ) : ContDiffOn ℝ ∞ (fun y => (R y)^power • T y) U :=
    (hR.pow power).contDiffOn.smul hTOn
  have hNWeighted (power : ℕ) (i j : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => (R y)^power • N i j y) U :=
    (hR.pow power).contDiffOn.smul (hNOn i j)
  have hZero (y : R3) (hy : y ∈ U) : (q,(y,(0 : ℝ))) ∈ Ω := by
    simpa only [zero_mul] using hy.2.1 0 ⟨le_refl 0,zero_le_one⟩
  have hC0On (j : Fin 3) : ContDiffOn ℝ ∞ (C0 j) U := by
    intro y hy
    exact ((contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,0)) j (hZero y hy)).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).contDiffWithinAt
  let A : (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let DJoint : (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun z =>
    deriv (fun t : ℝ => A (z.1,(z.2.1,t))) z.2.2
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hA : ContDiffOn ℝ ∞ A Ω := contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hDJoint : ContDiffOn ℝ ∞ DJoint Ω := contDiffOn_deriv_joint_radialSlice A Ω hΩ hA
  have hDOn : ContDiffOn ℝ ∞ D U := by
    intro y hy
    exact ((hDJoint.contDiffAt (hΩ.mem_nhds (hZero y hy))).comp y
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).contDiffWithinAt
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := by
    intro y hy
    exact ((contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i
      hR.contDiffAt hy.1).comp y (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hEOn (i : Fin 3) : ContDiffOn ℝ ∞ (E i) U := by
    have h1 := (hTWeighted 2).clm_comp (contDiffOn_const (c := M i))
    have h2 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
      (hC0On j).clm_comp (hNWeighted 2 i j))
    have h3 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
      hDOn.clm_comp ((contDiffOn_const (c := M j)).clm_comp (hNWeighted 3 i j)))
    have h4 := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
      (hTWeighted 2).clm_comp ((contDiffOn_const (c := M j)).clm_comp (hNWeighted 2 i j)))
    exact (((h1.add h2).add h3).add h4).add ((hfOn i).smul (hTWeighted 3))
  have hQuotientOn (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => (R y)^2 •
      referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U :=
    (hNatural.2 2 i).mono (by
      intro y hy
      refine ⟨hy.1,?_,hy.2.2⟩
      simpa only [one_mul] using hy.2.1 1 ⟨zero_le_one,le_refl 1⟩)
  exact ⟨hU,hTWeighted,hNWeighted,hC0On,hDOn,hfOn,hEOn,hQuotientOn⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceHighAdjoint_weighted_correction_open_room
