import Calderon.ActualDensityFirstActionNormalForms
import Calderon.ActualPhysicalDensityHigherFirstSectionDomain

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-second-action-germ-normal-form-v004.md. Genuine original first-section germ. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
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
  referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL

lemma referenceDensityCovariantSecondAction_normal_form
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i j : Fin 3) (hR : ContinuousAt R y) (hr : R y ≠ 0) :
    let W : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun (k : Fin 3) (x : R3) =>
      referenceHighWeightedHorizontalAction g L q R u x k +
      (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x) +
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
    referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
    referenceLowerWeightedHorizontalAction g L q R (W j) y i +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (W j y) +
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i (W j y)) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (W j y) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W k y) := by
  dsimp only
  let W : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun (k : Fin 3) (x : R3) =>
      referenceHighWeightedHorizontalAction g L q R u x k +
      (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x) +
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  have hNear : ∀ᶠ x in 𝓝 y, R x ≠ 0 := hR.eventually_ne hr
  have hFirst (k : Fin 3) :
      (fun x => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x k) =ᶠ[𝓝 y] W k := by
    filter_upwards [hNear] with x hx
    exact referenceHighDensityFirstAction_normal_form
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x k hx
  have hOuter := referenceLowerDensityFirstAction_congr_of_eventuallyEq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun x => referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j)
      (W j) y i (hFirst j)
  have hLower := referenceLowerDensityFirstAction_normal_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (W j) y i hr
  have hConnection :
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
            (referenceHighDensityFirstAction
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k)) =
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W k y) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg
      (fun z : SphereSobolev (1/2 : ℝ) => referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) z)
      ((hFirst k).self_of_nhds)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a-b)
    (hOuter.trans hLower) hConnection
  unfold referenceDensityCovariantSecondAction
  simpa only [W] using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction_normal_form
