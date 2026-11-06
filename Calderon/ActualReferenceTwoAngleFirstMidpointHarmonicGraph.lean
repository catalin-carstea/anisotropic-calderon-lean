import Calderon.SubmoduleRealNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ActualReferenceTwoAngleWeakOperatorContinuity
import Calderon.ActualReferenceTwoAngleFirstMidpointDerivative
import Calderon.ActualReferenceTwoAngleMidpointCovariance
import Calderon.HarmonicSphereRotationAngleDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-first-harmonic-graph-v029.md. Exact actual physical harmonic graph. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open Filter
open scoped Topology

open SphereHarmonic

open SmoothSphereRotation SmoothSphereRotationProjection
attribute [local irreducible] referenceTwoAngleSharpMidpointRadialTraceFamily
  referenceTwoAngleFirstMidpointDerivativeFamily sphereSobolevSingleL sphereSobolevCoefficientL

lemma referenceTwoAngleFirstMidpointDerivativeFamily_harmonic_block
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL 0 m
      (referenceTwoAngleFirstMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p)
        (sphereSobolevSingleL 1 n u)) =
    harmonicSphereRotation m i j (sphereSobolevCoefficientL 0 m
      (referenceTwoAngleSharpMidpointRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p))
        (sphereSobolevSingleL 1 n u))) -
    sphereSobolevCoefficientL 0 m
      (referenceTwoAngleSharpMidpointRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p))
        (sphereSobolevSingleL 1 n (harmonicSphereRotation n i j u))) := by
  let M : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun θ =>
    referenceTwoAngleSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
  let D : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := referenceTwoAngleFirstMidpointDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p)
  let J := sphereSobolevSingleL 1 n
  let C0 := sphereSobolevCoefficientL 0 m
  have hM : HasDerivAt M D 0 := hasDerivAt_referenceTwoAngleMidpoint_first_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l φ p hp
  have hu := hasDerivAt_harmonicSphereOrthogonalPullback_coordinate_zero hO hD i j n u
  have hInput : HasDerivAt
      (fun θ : ℝ => J (harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) n u))
      (J (harmonicSphereRotation n i j u)) 0 := J.hasFDerivAt.comp_hasDerivAt 0 hu
  have hValue := hM.clm_apply hInput
  have hProjected := C0.hasFDerivAt.comp_hasDerivAt 0 hValue
  have hLeft : HasDerivAt
      (fun θ : ℝ => C0 (M θ (J (harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) n u))))
      (C0 (D (J u) + M 0 (J (harmonicSphereRotation n i j u)))) 0 := by
    simpa (config := { instances := true }) only
      [Function.comp_def, harmonicSphereOrthogonalPullback_coordinate_zero,
       submodule_normedAddCommGroup_addCommGroup_eq_natural,
       submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
       submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
       submodule_normedSpace_module_eq] using hProjected
  have hRight := hasDerivAt_harmonicSphereOrthogonalPullback_coordinate_zero
    hO hD i j m (C0 (M 0 (J u)))
  have hNear : ∀ᶠ θ : ℝ in 𝓝 0, (θ,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l :=
    (continuousAt_id.prodMk continuousAt_const).eventually
      ((isOpen_referenceTwoAngleRadialInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l).mem_nhds hp)
  have hCurve : (fun θ : ℝ => C0 (M θ (J
      (harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) n u)))) =ᶠ[𝓝 0]
      (fun θ : ℝ => harmonicSphereOrthogonalPullback (coordinateRotationIsometry i j θ) m
        (C0 (M 0 (J u)))) := by
    filter_upwards [hNear] with θ hθ
    have hCov := referenceTwoAngleSharpMidpointRadialTraceFamily_first_angle_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l θ φ p hp hθ (J u)
    have hc := congrArg C0 hCov
    simpa only [J,C0,sphereSobolevOrthogonalPullbackL_single,
      sphereSobolevCoefficientL_orthogonalPullback] using hc
  have hEq := (hLeft.congr_of_eventuallyEq hCurve.symm).unique hRight
  have hSum : C0 (D (J u)) + C0 (M 0 (J (harmonicSphereRotation n i j u))) =
      harmonicSphereRotation m i j (C0 (M 0 (J u))) := by
    simpa only [map_add] using hEq
  exact eq_sub_iff_add_eq.mpr hSum

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFirstMidpointDerivativeFamily_harmonic_block
