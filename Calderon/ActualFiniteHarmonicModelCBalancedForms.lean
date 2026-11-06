import Calderon.ActualFiniteHarmonicModelSecondAngularJets
import Calderon.ActualFiniteHarmonicModelCBalancedCoefficient

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  BalancedAngularShift ActualReferenceDDHigherGeometryJets SectionFiveErrorForms
  ActualNormalizedSphereRotation ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelDefectCoefficients
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection SmoothSphereFields
  SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWBalancedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWBalancedFunction
lemma coordinateFieldWordPartial_nativeC_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w
        (nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0g (y : R3) : PreservesSphereSpectralGraphs hO hD (K0 y) :=
    preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h y
  have hHalfG : (G x,coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have h32_2 : (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 2) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x) k,smul_smul,← besselWeight_add]
    norm_num
  have hHalf32 : (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
      coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈ sphereBesselGraph hO hD 1 := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,smul_smul,← besselWeight_add]
    norm_num
  have h12 : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hi2Explicit : inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 2) F x) =
      coreWeightOperator hO hD (besselWeight 1) F x := inverseDegreeMultiplier_of_besselGraph hO hD _ _ h12
  have hi32Explicit : inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) =
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x := inverseDegreeMultiplier_of_besselGraph hO hD _ _ hHalf32
  have hdiag (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪A (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) _ _ _ _
      (hA _ _ _ h32_2) hHalfG
  have hK0form (y : R3) :
      ⟪referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y
          (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y
          (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [K0,h] using hdiag (K0 y) (hK0g y)
  have hJ0form (y : R3) :
      ⟪normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p y
          (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p y
          (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    exact hdiag _ (preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftZeroNormalizedCoefficient
      hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR [] y)
  have hr0 (a : Fin 3) :
      ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ :=
    balancedRaising_inner_realization hF hO hD a (F x) _ _ (G x) _
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreRaising_graph hO hD hF a F x) hHalfG
  have hProfR (a : Fin 3) :
      ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x -
        coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x -
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simp only [map_sub,inner_sub_left,
      normalizedRaising_second_weight_inner_threehalf_half hO hD hF a F G x,hr0 a]
  let WN := nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let WB := nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  have hinner (y : R3) :
      ⟪WN y (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪WB y (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    dsimp only [WN,WB]
    unfold nativeCSecondAngularCoefficient nativeCSecondBalancedAngularCoefficient
    dsimp only
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,inner_add_left,inner_sub_left,sum_inner,real_inner_smul_left,
      hi2Explicit,hi32Explicit]
    simp_rw [hK0form,hJ0form,hProfR,
      normalizedRaising_rotation_second_weight_inner_threehalf_half hO hD hF,
      normalizedRaising_double_shift_inner_threehalf_half hO hD hF]
  have hWN : ContDiff ℝ ∞ WN :=
    contDiff_nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hWB : ContDiff ℝ ∞ WB :=
    contDiff_nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let J1 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ (G x)).comp
      (ContinuousLinearMap.apply ℝ SphereL2 (coreWeightOperator hO hD (besselWeight 2) F x))
  let J2 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)).comp
      (ContinuousLinearMap.apply ℝ SphereL2 (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x))
  have hfunc : (fun y => J1 (WN y)) = fun y => J2 (WB y) := by
    funext y
    change ⟪G x,WN y (coreWeightOperator hO hD (besselWeight 2) F x)⟫_ℝ =
      ⟪coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x,
        WB y (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)⟫_ℝ
    rw [real_inner_comm (WN y (coreWeightOperator hO hD (besselWeight 2) F x)) (G x),
      real_inner_comm (WB y (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x))
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)]
    exact hinner y
  have hfixed (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
      (J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => J (A y)) = fun y => J (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w (fun y => J (A y))) =
        fun y => J (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map J
        (coordinateFieldWordPartial w A) (contDiff_coordinateFieldWordPartial w A hA) (coordinateDirection k) y
  have hw := congrArg (fun f : R3 → ℝ => coordinateFieldWordPartial w f) hfunc
  rw [hfixed WN hWN J1,hfixed WB hWB J2] at hw
  have he := congrFun hw x
  change ⟪G x,coordinateFieldWordPartial w WN x (coreWeightOperator hO hD (besselWeight 2) F x)⟫_ℝ =
    ⟪coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x,
      coordinateFieldWordPartial w WB x (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)⟫_ℝ at he
  rw [real_inner_comm (coordinateFieldWordPartial w WN x (coreWeightOperator hO hD (besselWeight 2) F x)) (G x),
    real_inner_comm (coordinateFieldWordPartial w WB x (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x))
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)] at he
  exact he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
