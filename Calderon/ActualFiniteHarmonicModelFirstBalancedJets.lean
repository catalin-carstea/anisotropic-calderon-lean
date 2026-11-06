import Calderon.ActualFiniteHarmonicModelFirstCoefficientJets
import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelErrorAssembly
  BalancedAngularShift ActualModelCommutatorWords ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDHigherGeometryJets
  ActualReferenceDDSpectralTransport ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint
  ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftWeightedCoefficients
  NaturalAngularAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame SmoothSphereFields SmoothAngularApplication
  SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeBFirstBalancedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeBFirstBalancedFunction
def modelFirstBalancedCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
    (∑ a : Fin 3, physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x • balancedRaising hF hO hD a) +
    normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x

lemma contDiff_modelFirstBalancedCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (modelFirstBalancedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hK := contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    hδ hR h hh j
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hJ := contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
    L lam δ R p hδ hR j
  unfold modelFirstBalancedCoefficient
  exact (hK.add (ContDiff.sum fun a _ => (hm a).smul contDiff_const)).add hJ

lemma coordinateFieldWordPartial_nativeB_firstNormalized_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x
        (coreWeightOperator hO hD (besselWeight 1) F x), G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w
        (modelFirstBalancedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let v := G x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let HN := modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j
  let HB := modelFirstBalancedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 :=
    coreWeightOperator_graph hO hD (besselWeight 1) F x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) :=
    coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) :=
    coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [hu1 k,huh k,smul_smul,← besselWeight_add]
    norm_num
  have hr (a : Fin 3) :
      ⟪normalizedRaising hF hO hD a u1,v⟫_ℝ =
        ⟪balancedRaising hF hO hD a uh,vh⟫_ℝ :=
    balancedRaising_inner_realization hF hO hD a u uh _ v vh huh
      (normalizedRaising_graph hF hO hD a u u1 hu1) hvh
  have hdiag (A : SphereL2 →L[ℝ] SphereL2)
      (hA : PreservesSphereSpectralGraphs hO hD A) :
      ⟪A u1,v⟫_ℝ = ⟪A uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (A uh) (A u1) v vh (hA _ uh u1 hub) hvh
  have hK (y : R3) : PreservesSphereSpectralGraphs hO hD
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j y) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1
      L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j y
  have hJ (y : R3) : PreservesSphereSpectralGraphs hO hD
      (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j y) := by
    unfold normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hinner (y : R3) : ⟪HN y u1,v⟫_ℝ = ⟪HB y uh,vh⟫_ℝ := by
    have hKy := hdiag _ (hK y)
    have hJy := hdiag _ (hJ y)
    dsimp only [HN,HB]
    unfold modelFirstNormalizedCoefficient modelFirstBalancedCoefficient
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply,inner_add_left,sum_inner,real_inner_smul_left]
    simp_rw [hr,hKy,hJy]
  have hHN : ContDiff ℝ ∞ HN :=
    contDiff_modelFirstNormalizedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  have hHB : ContDiff ℝ ∞ HB :=
    contDiff_modelFirstBalancedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  let J1 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u1)
  let J2 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hfunc : (fun y => J1 (HN y)) = fun y => J2 (HB y) := by
    funext y
    change ⟪v,HN y u1⟫_ℝ = ⟪vh,HB y uh⟫_ℝ
    rw [real_inner_comm (HN y u1) v,real_inner_comm (HB y uh) vh]
    exact hinner y
  have hfixed (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
      (J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => J (A y)) =
        fun y => J (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => J (A y))) =
          fun y => J (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map J
        (coordinateFieldWordPartial w A) (contDiff_coordinateFieldWordPartial w A hA)
        (coordinateDirection k) y
  have hw := congrArg (fun f : R3 → ℝ => coordinateFieldWordPartial w f) hfunc
  rw [hfixed HN hHN J1,hfixed HB hHB J2] at hw
  have he := congrFun hw x
  change ⟪v,coordinateFieldWordPartial w HN x u1⟫_ℝ =
    ⟪vh,coordinateFieldWordPartial w HB x uh⟫_ℝ at he
  rw [real_inner_comm (coordinateFieldWordPartial w HN x u1) v,
    real_inner_comm (coordinateFieldWordPartial w HB x uh) vh] at he
  exact he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
