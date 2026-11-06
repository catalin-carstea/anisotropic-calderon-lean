import Calderon.ActualDensityFirstNormalFormSummandSmoothness

/-! Horizontal distribution of the four normal-form summands, as genuine native half-valued
sections. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
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

attribute [local irreducible] referenceHighWeightedHorizontalAction
  referenceLowerWeightedHorizontalAction referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient sphereSobolevAngularCoordinateTransposeL
  sphereSobolevInclusionL referenceRadialEndpointInvertibleLocus

lemma referenceLowerWeightedHorizontalAction_normal_form_add
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let D0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      referenceHighWeightedHorizontalAction g L q R u x j
    let V0 : R3 → SphereSobolev (1/2 : ℝ) := fun x => (R x)⁻¹ •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u x)
    let F0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) j (u x))
    let E0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x j (u x)
    referenceLowerWeightedHorizontalAction g L q R (fun x => D0 x+V0 x+F0 x+E0 x) y i =
      referenceLowerWeightedHorizontalAction g L q R D0 y i +
      referenceLowerWeightedHorizontalAction g L q R V0 y i +
      referenceLowerWeightedHorizontalAction g L q R F0 y i +
      referenceLowerWeightedHorizontalAction g L q R E0 y i := by
  dsimp only
  let D0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      referenceHighWeightedHorizontalAction g L q R u x j
  let V0 : R3 → SphereSobolev (1/2 : ℝ) := fun x => (R x)⁻¹ •
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u x)
  let F0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) j (u x))
  let E0 : R3 → SphereSobolev (1/2 : ℝ) := fun x =>
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x j (u x)
  have hTerms := contDiffAt_referenceHighDensityFirstAction_normal_form_summands
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y j hR hr hu hInv hp
  have hD : DifferentiableAt ℝ D0 y := hTerms.1.differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V0 y := hTerms.2.1.differentiableAt (by simp)
  have hF0 : DifferentiableAt ℝ F0 y := hTerms.2.2.1.differentiableAt (by simp)
  have hE0 : DifferentiableAt ℝ E0 y := hTerms.2.2.2.differentiableAt (by simp)
  have hDV := referenceLowerWeightedHorizontalAction_add g L q R D0 V0 y i hD hV
  have hDVF := referenceLowerWeightedHorizontalAction_add g L q R
    (fun x => D0 x+V0 x) F0 y i (hD.add hV) hF0
  have hAll := referenceLowerWeightedHorizontalAction_add g L q R
    (fun x => D0 x+V0 x+F0 x) E0 y i ((hD.add hV).add hF0) hE0
  rw [hDVF,hDV] at hAll
  simpa only [D0,V0,F0,E0] using hAll

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_normal_form_add
