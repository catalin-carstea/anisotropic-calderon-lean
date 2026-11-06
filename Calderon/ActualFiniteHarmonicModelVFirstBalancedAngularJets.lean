import Calderon.ActualFiniteHarmonicModelVFirstAngularJets
import Calderon.BalancedAngularShift
import Calderon.ActualReferenceDDHigherSpectralGraphs

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  BalancedAngularShift ActualModelCommutatorWords ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDHigherGeometryJets
  ActualReferenceDDSpectralTransport ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftWeightedCoefficients
  NaturalAngularAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame SmoothSphereFields SmoothAngularApplication
  SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev vFirstBalancedAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vFirstBalancedAngularFunction
def nativeVFirstBalancedAngularCoefficient (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (∑ a : Fin 3,
    (-physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x) •
      (balancedDerivative hF hO hD a + balancedRaising hF hO hD a)) -
    (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
      ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x)) +
    (adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j -
      2 * (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))) •
      inverseDegreeMultiplier hO hD


lemma contDiff_nativeVFirstBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) := by
  have hh := ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have he (a : Fin 3) : ContDiff ℝ ∞
      (fun x => referenceMetricGramFrame g1 L (lam,x) a j) :=
    ((contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hK := contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    hδ hR (referenceNormalizedPrincipalDifference g1 g2 L lam) hh j
  have hKa : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.adjoint
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x)) :=
    contDiff_angularAdjoint _ hK
  have ha := contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb : ContDiff ℝ ∞ (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  unfold nativeVFirstBalancedAngularCoefficient
  exact ((ContDiff.sum fun a _ => ((hm a).neg.smul
    contDiff_const)).sub (hK.add hKa)).add
      ((ha.sub (contDiff_const.mul (hr.mul hb))).smul contDiff_const)


lemma coordinateFieldWordPartial_nativeV_firstAngular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x
        (coreWeightOperator hO hD (besselWeight 1) F x), G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w
        (nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let v := G x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let HN := nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  let HB := nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
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
  have hd (a : Fin 3) :
      ⟪normalizedDerivative hF hO hD a u1,v⟫_ℝ =
        ⟪balancedDerivative hF hO hD a uh,vh⟫_ℝ :=
    balancedDerivative_inner_realization hF hO hD a u uh _ v vh huh
      (normalizedDerivative_graph hF hO hD a u u1 hu1) hvh
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
  have hI := hdiag (inverseDegreeMultiplier hO hD)
    (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hinner (y : R3) : ⟪HN y u1,v⟫_ℝ = ⟪HB y uh,vh⟫_ℝ := by
    have hKy := hdiag _ (hK y)
    have hKay := hdiag _ (preservesSphereSpectralGraphs_adjoint hO hD _ (hK y))
    dsimp only [HN,HB]
    unfold nativeVFirstAngularCoefficient nativeVFirstBalancedAngularCoefficient
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,inner_add_left,
      inner_sub_left,sum_inner,real_inner_smul_left]
    simp_rw [hd,hr,hKy,hKay,hI]
  have hHN : ContDiff ℝ ∞ HN :=
    contDiff_nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  have hHB : ContDiff ℝ ∞ HB :=
    contDiff_nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
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


lemma nativeV_firstAngular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x, G x⟫_ℝ =
      ⟪nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [nativeV_firstAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x]
  exact coordinateFieldWordPartial_nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1
    L lam δ R p j hg2 hδ hR [] F G x


lemma coefficientDerivative_nativeV_firstAngular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) F x, G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_nativeV_firstAngular_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
    (coordinateDirection i) F x]
  exact coordinateFieldWordPartial_nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1
    L lam δ R p j hg2 hδ hR [i] F G x


lemma coefficientDerivative_second_nativeV_firstAngular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i k : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)) F x, G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection k)
          (nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j)) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_second_nativeV_firstAngular_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
    (coordinateDirection i) (coordinateDirection k) F x]
  exact coordinateFieldWordPartial_nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1
    L lam δ R p j hg2 hδ hR [i,k] F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
