import Calderon.ActualDensityCovariantSecondNormalForm
import Calderon.ActualDensityNormalFormHorizontalDistribution

/-! Ordered actual identity, with every native correction retained. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceDensityCovariantSecondAction
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL referenceRadialEndpointInvertibleLocus

lemma referenceDensityCovariantSecondAction_grouped_normal_form
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (i j : Fin 3) (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
    let Klo : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    let W : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => D k x+V k x+K k x
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
    let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    (referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerWeightedHorizontalAction g L q R (W j) y i + (R y)⁻¹ • Alo i (W j y) + Klo (W j y) -
        ∑ k : Fin 3, Gamma k • Iout (W k y)) ∧
    (referenceLowerWeightedHorizontalAction g L q R (W j) y i =
      referenceLowerWeightedHorizontalAction g L q R (D j) y i + referenceLowerWeightedHorizontalAction g L q R (V j) y i + referenceLowerWeightedHorizontalAction g L q R (K j) y i) := by
  trace "COVARIANT_LEADING_ENTER"
  dsimp only
  let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
  let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let Klo : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let F0 : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x))
  let E0 : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let W : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => D k x+V k x+K k x
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j
  change (referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerWeightedHorizontalAction g L q R (W j) y i + (R y)⁻¹ • Alo i (W j y) + Klo (W j y) -
        ∑ k : Fin 3, Gamma k • Iout (W k y)) ∧
    (referenceLowerWeightedHorizontalAction g L q R (W j) y i =
      referenceLowerWeightedHorizontalAction g L q R (D j) y i + referenceLowerWeightedHorizontalAction g L q R (V j) y i + referenceLowerWeightedHorizontalAction g L q R (K j) y i)
  have hW (k : Fin 3) : W k = (fun x => D k x+V k x+F0 k x+E0 k x) := by
    funext x
    dsimp only [W,K,F0,E0]
    exact (add_assoc _ _ _).symm
  trace "COVARIANT_LEADING_SUMMANDS_ENTER"
  have hTerms := contDiffAt_referenceHighDensityFirstAction_normal_form_summands
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y j
      hR.contDiffAt hr hu hInv hp
  have hD0 : DifferentiableAt ℝ (D j) y := hTerms.1.differentiableAt (by simp)
  have hV0 : DifferentiableAt ℝ (V j) y := hTerms.2.1.differentiableAt (by simp)
  have hF0 : DifferentiableAt ℝ (F0 j) y := hTerms.2.2.1.differentiableAt (by simp)
  have hE0 : DifferentiableAt ℝ (E0 j) y := hTerms.2.2.2.differentiableAt (by simp)
  have hK0 : DifferentiableAt ℝ (K j) y := hF0.add hE0
  have hK : referenceLowerWeightedHorizontalAction g L q R (K j) y i =
      referenceLowerWeightedHorizontalAction g L q R (F0 j) y i + referenceLowerWeightedHorizontalAction g L q R (E0 j) y i :=
    referenceLowerWeightedHorizontalAction_add g L q R (F0 j) (E0 j) y i hF0 hE0
  trace "COVARIANT_LEADING_SUMMANDS_READY"
  have hFour := referenceLowerWeightedHorizontalAction_normal_form_add
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y i j
      hR.contDiffAt hr hu hInv hp
  have hDistribution : referenceLowerWeightedHorizontalAction g L q R (W j) y i =
      referenceLowerWeightedHorizontalAction g L q R (D j) y i + referenceLowerWeightedHorizontalAction g L q R (V j) y i + referenceLowerWeightedHorizontalAction g L q R (K j) y i := by
    calc
      _ = referenceLowerWeightedHorizontalAction g L q R (fun x => D j x+V j x+F0 j x+E0 j x) y i := by rw [hW]
      _ = referenceLowerWeightedHorizontalAction g L q R (D j) y i + referenceLowerWeightedHorizontalAction g L q R (V j) y i +
          referenceLowerWeightedHorizontalAction g L q R (F0 j) y i + referenceLowerWeightedHorizontalAction g L q R (E0 j) y i := hFour
      _ = _ := by rw [hK]; abel
  trace "COVARIANT_LEADING_DISTRIBUTION_READY"
  have hNormal := referenceDensityCovariantSecondAction_normal_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j
      hR.continuous.continuousAt hr
  trace "COVARIANT_LEADING_NORMAL_PARENT_READY"
  let W4 : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) :=
    fun k x => D k x+V k x+F0 k x+E0 k x
  trace "COVARIANT_LEADING_NORMAL_ALIAS_ENTER"
  change referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerWeightedHorizontalAction g L q R (W4 j) y i +
      (R y)⁻¹ • Alo i (W4 j y) +
      Iout (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
        ((q,y),fderiv ℝ R y) i (W4 j y)) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (W4 j y) -
      ∑ k : Fin 3, Gamma k • Iout (W4 k y) at hNormal
  trace "COVARIANT_LEADING_NORMAL_ALIAS_READY"
  have hW4 : W4 = W := by
    funext k
    exact (hW k).symm
  rw [hW4] at hNormal
  trace "COVARIANT_LEADING_NORMAL_SECTION_REWRITTEN"
  have hKloApply (z : SphereSobolev (1/2 : ℝ)) : Klo z =
      Iout (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
        ((q,y),fderiv ℝ R y) i z) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i z := rfl
  have hNormalGrouped : referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerWeightedHorizontalAction g L q R (W j) y i + (R y)⁻¹ • Alo i (W j y) + Klo (W j y) -
        ∑ k : Fin 3, Gamma k • Iout (W k y) := by
    rw [hKloApply]
    exact hNormal.trans (by abel)
  trace "COVARIANT_LEADING_NORMAL_GROUPED"
  exact ⟨hNormalGrouped,hDistribution⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction_grouped_normal_form
