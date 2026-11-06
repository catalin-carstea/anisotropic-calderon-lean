import Calderon.ActualFiniteHarmonicModelSecondAngularSymmetricBase

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
  ActualReferenceParallelRaising ActualNormalizedSphereRotation ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondDriftNativeAdjunction
  ActualNormalizedSecondDriftDefectCoefficients ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondMetricDrift
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ReferenceDensityBounds NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWSymmetricFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSymmetricFunction
lemma coordinateFieldWordPartial_nativeW_symmetric_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ +
      ⟪F x,coordinateFieldWordPartial w
        (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) G x)⟫_ℝ =
    ⟪coordinateFieldWordPartial w
        (nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let v := G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2) +
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ SphereL2 v2)
  let Q : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  let WN := nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let WS := nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  have hWN : ContDiff ℝ ∞ WN :=
    contDiff_nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hWS : ContDiff ℝ ∞ WS :=
    contDiff_nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hfunc : (fun y => J (WN y)) = fun y => Q (WS y) := by
    funext y
    rw [hJ,hQ]
    exact nativeW_symmetric_inner_half_at hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F G x y
  have hfixed (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
      (T : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => T (A y)) = fun y => T (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w (fun y => T (A y))) =
        fun y => T (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map T (coordinateFieldWordPartial w A)
        (contDiff_coordinateFieldWordPartial w A hA) (coordinateDirection k) y
  have hw := congrArg (fun f : R3 → ℝ => coordinateFieldWordPartial w f) hfunc
  rw [hfixed WN hWN J,hfixed WS hWS Q] at hw
  have he := congrFun hw x
  rw [hJ,hQ] at he
  exact he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
