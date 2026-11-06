import Calderon.ActualFullAdjointFirstActions

/-! The formal Y = -H + Cprimal - GammaTrace; the genuine global integration by parts is treated
separately. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceLowerFullAdjointFirstAction
  referenceLowerHorizontalAction referenceLowerMovingBoundaryActionFamily
  referenceLowerHorizontalAngularL referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL

lemma referenceLowerFullAdjointFirstAction_congr_of_eventuallyEq
    (q : ℝ) (R : R3 → ℝ) (v wv : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (h : v =ᶠ[𝓝 y] wv) :
    referenceLowerFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
    referenceLowerFullAdjointFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R wv y i := by
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let Ω := referenceLowerHorizontalAngularL g L q y i
  let C0 := referenceLowerMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
  let delta := ∑ j : Fin 3, referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) j) j i
  have hDerivative := congrArg
    (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => J (A e)) h.fderiv_eq
  have hAngular := congrArg Ω h.self_of_nhds
  have hMoving := congrArg C0 h.self_of_nhds
  have hScalar := congrArg (fun z : SphereSobolev (1/2 : ℝ) => delta • J z) h.self_of_nhds
  have hHorizontal := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    hDerivative hAngular
  have hTotal := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => -x+z) hHorizontal hMoving) hScalar
  simpa only [referenceLowerFullAdjointFirstAction,referenceLowerHorizontalAction,J,e,Ω,C0,delta] using hTotal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerFullAdjointFirstAction_congr_of_eventuallyEq
