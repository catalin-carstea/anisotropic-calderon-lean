import Calderon.ActualFiniteHarmonicModelSecondAngularJets
import Calderon.ActualFiniteHarmonicModelSecondAngularBalancedBasis

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
def nativeWSecondBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x =>
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let I := inverseDegreeMultiplier hO hD
    let Id := ContinuousLinearMap.id ℝ SphereL2
    let mu := fun y : R3 => referenceDensityFamily g1 L (lam,y)
    let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
    (adjointZeroCoefficient coordinateDirection mu (actualPrincipalMatrix g1 L lam δ R p h) x) •
      (I.comp I) -
    (mu x)⁻¹ • ∑ j : Fin 3,
      (weightedAngularAdjointDerivative (coordinateDirection j) mu
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j) x).comp I +
    (ContinuousLinearMap.adjoint (K0 x) - K0 x) +
    (∑ a : Fin 3, physicalMixedDensityCorrection g1 L lam h a x •
      ((balancedDerivative hF hO hD a).comp I)) +
    ((∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
      ((balancedDerivative hF hO hD a).comp (Id - (2 : ℝ) • I))) -
      (∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
        ((balancedRaising hF hO hD a).comp (Id - I)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (-physicalMixedConnectionCoefficient g1 L lam h a b c x) •
        ((normalizedRotation hO hD b c).comp
          ((balancedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        physicalMixedConnectionCoefficient g1 L lam h a b c x •
          ((balancedRaising hF hO hD a).comp (normalizedRotation hO hD b c)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
      ((balancedDerivative hF hO hD b).comp
        ((balancedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
        ((balancedRaising hF hO hD a).comp
          ((balancedRaising hF hO hD b).comp (Id + I))))) +
    (-2 : ℝ) • (referenceRadius δ R p L x • ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
          referenceFrameConnectionCoefficient g1 L lam x
            (referenceMetricGramFrame g1 L (lam,x) a) b c •
              ((normalizedRotation hO hD b c).comp I))) -
    normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • (I.comp I)

lemma contDiff_nativeWSecondBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhentry (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0 : ContDiff ℝ ∞ K0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
      hδ hR h hh
  have hprof (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedProfileCoefficient g1 L lam δ R p h a) :=
    contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a
  have hconn (a b c : Fin 3) : ContDiff ℝ ∞ (physicalMixedConnectionCoefficient g1 L lam h a b c) :=
    contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhentry a b c
  have hpure (a b : Fin 3) : ContDiff ℝ ∞ (physicalPureAngularCoefficient g1 L lam δ R p h a b) :=
    contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a b
  let mu := fun x : R3 => referenceDensityFamily g1 L (lam,x)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmui : ContDiff ℝ ∞ (fun x : R3 => (mu x)⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  let K (j : Fin 3) := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hK (j : Fin 3) : ContDiff ℝ ∞ (K j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      hδ hR h hh j
  let H (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (K j)
  have hB (j : Fin 3) : ContDiff ℝ ∞ (fun y => mu y • angularAdjoint (K j) y) :=
    hmu.smul (contDiff_angularAdjoint (K j) (hK j))
  have hH (j : Fin 3) : ContDiff ℝ ∞ (H j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hB j)
  have hK0a : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.adjoint (K0 x)) :=
    contDiff_angularAdjoint K0 hK0
  have hdens (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedDensityCorrection g1 L lam h a) :=
    contDiff_physicalMixedDensityCorrection g1 hg1 L lam h hhentry a
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) :=
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
      (contDiff_const.prodMk contDiff_id)
  have hGamma (a b c : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceFrameConnectionCoefficient g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) a) b c) :=
    AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
      g1 hg1 L lam _ (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a) b c
  have ha0 := contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hdiv := contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR
  let I := inverseDegreeMultiplier hO hD
  let J : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    referenceRadius δ R p L y • ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
          referenceFrameConnectionCoefficient g1 L lam y
            (referenceMetricGramFrame g1 L (lam,y) a) b c •
              ((normalizedRotation hO hD b c).comp I))
  have hJ : ContDiff ℝ ∞ J := hr.smul (ContDiff.sum fun a _ => (hb a).smul
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (1/2 : ℝ))).smul
      (ContDiff.sum fun b _ => ContDiff.sum fun c _ => (hGamma a b c).smul contDiff_const)))
  unfold nativeWSecondBalancedAngularCoefficient
  dsimp only
  exact ((((((((ha0.smul contDiff_const).sub
    (hmui.smul (ContDiff.sum fun j _ => (hH j).clm_comp contDiff_const))).add
      (hK0a.sub hK0)).add
      (ContDiff.sum fun a _ => (hdens a).smul contDiff_const)).add
      ((ContDiff.sum fun a _ => (hprof a).smul contDiff_const).sub
        (ContDiff.sum fun a _ => (hprof a).smul contDiff_const))).add
      ((ContDiff.sum fun a _ => ContDiff.sum fun b _ => ContDiff.sum fun c _ =>
        (hconn a b c).neg.smul contDiff_const).sub
        (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ContDiff.sum fun c _ =>
          (hconn a b c).smul contDiff_const))).add
      ((ContDiff.sum fun a _ => ContDiff.sum fun b _ => (hpure a b).smul contDiff_const).sub
        (ContDiff.sum fun a _ => ContDiff.sum fun b _ => (hpure a b).smul contDiff_const))).add
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (-2 : ℝ))).smul hJ)).sub
      (hdiv.smul contDiff_const)



lemma coordinateFieldWordPartial_nativeW_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w
        (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let mu := fun y : R3 => referenceDensityFamily g1 L (lam,y)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  let K (j : Fin 3) := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hK (j : Fin 3) : ContDiff ℝ ∞ (K j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hKg (j : Fin 3) (y : R3) : PreservesSphereSpectralGraphs hO hD (K j y) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j y
  let H (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (K j)
  have hB (j : Fin 3) : ContDiff ℝ ∞ (fun y => mu y • angularAdjoint (K j) y) :=
    hmu.smul (contDiff_angularAdjoint (K j) (hK j))
  have hBg (j : Fin 3) (y : R3) : PreservesSphereSpectralGraphs hO hD
      (mu y • angularAdjoint (K j) y) := preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_adjoint hO hD (K j y) (hKg j y))
  have hHg (j : Fin 3) (y : R3) : PreservesSphereSpectralGraphs hO hD (H j y) :=
    preservesSphereSpectralGraphs_directionalFDeriv hO hD
      (fun z => mu z • angularAdjoint (K j) z) (hB j) (hBg j) y (coordinateDirection j)
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
  have hIg := preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  have hI2form :
      ⟪inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [ContinuousLinearMap.comp_apply,hi2Explicit,hi32Explicit] using
      hdiag ((inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD))
        (preservesSphereSpectralGraphs_comp hO hD _ _ hIg hIg)
  have hHIform (j : Fin 3) (y : R3) :
      ⟪weightedAngularAdjointDerivative (coordinateDirection j)
          (fun z => referenceDensityFamily g1 L (lam,z))
          (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
            (referenceNormalizedPrincipalDifference g1 g2 L lam) j) y
          (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪weightedAngularAdjointDerivative (coordinateDirection j)
          (fun z => referenceDensityFamily g1 L (lam,z))
          (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
            (referenceNormalizedPrincipalDifference g1 g2 L lam) j) y
          (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [H,K,mu,h,ContinuousLinearMap.comp_apply,hi2Explicit,hi32Explicit] using
      hdiag ((H j y).comp (inverseDegreeMultiplier hO hD))
        (preservesSphereSpectralGraphs_comp hO hD _ _ (hHg j y) hIg)
  have hK0form (y : R3) :
      ⟪referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y
          (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y
          (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [K0,h] using hdiag (K0 y) (hK0g y)
  have hK0aform (y : R3) :
      ⟪ContinuousLinearMap.adjoint (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y)
          (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪ContinuousLinearMap.adjoint (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) y)
          (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [K0,h] using hdiag (ContinuousLinearMap.adjoint (K0 y))
      (preservesSphereSpectralGraphs_adjoint hO hD _ (hK0g y))
  have hRotIform (b c : Fin 3) :
      ⟪normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simpa only [ContinuousLinearMap.comp_apply,hi2Explicit,hi32Explicit] using
      hdiag ((normalizedRotation hO hD b c).comp (inverseDegreeMultiplier hO hD))
        (preservesSphereSpectralGraphs_comp hO hD _ _
          (preservesSphereSpectralGraphs_normalizedRotation hO hD b c) hIg)
  have hd0 (a : Fin 3) :
      ⟪normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ :=
    balancedDerivative_inner_realization hF hO hD a (F x) _ _ (G x) _
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreDerivative_graph hO hD hF a F x) hHalfG
  have hr0 (a : Fin 3) :
      ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ :=
    balancedRaising_inner_realization hF hO hD a (F x) _ _ (G x) _
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreRaising_graph hO hD hF a F x) hHalfG
  have hProfD (a : Fin 3) :
      ⟪normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simp only [map_sub,map_smul,inner_sub_left,real_inner_smul_left,
      normalizedDerivative_second_weight_inner_threehalf_half hO hD hF a F G x,hd0 a]
  have hProfR (a : Fin 3) :
      ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x -
        coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x -
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    simp only [map_sub,inner_sub_left,
      normalizedRaising_second_weight_inner_threehalf_half hO hD hF a F G x,hr0 a]
  let WN := nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let WB := nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  have hinner (y : R3) :
      ⟪WN y (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪WB y (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
    dsimp only [WN,WB]
    unfold nativeWSecondAngularCoefficient nativeWSecondBalancedAngularCoefficient
    dsimp only
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,inner_add_left,inner_sub_left,sum_inner,real_inner_smul_left,
      hi2Explicit,hi32Explicit]
    simp_rw [hI2form,hHIform,hK0form,hK0aform,hd0,hProfD,hProfR,hRotIform,
      normalizedRotation_derivative_shift_inner_threehalf_half hO hD hF,
      normalizedRaising_rotation_second_weight_inner_threehalf_half hO hD hF,
      normalizedDerivative_double_shift_inner_threehalf_half hO hD hF,
      normalizedRaising_double_shift_inner_threehalf_half hO hD hF]
  have hWN : ContDiff ℝ ∞ WN :=
    contDiff_nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hWB : ContDiff ℝ ∞ WB :=
    contDiff_nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
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


lemma nativeW_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ =
      ⟪nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [nativeW_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x]
  exact coordinateFieldWordPartial_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [] F G x


lemma coefficientDerivative_nativeW_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪ActualModelCommutatorWords.coefficientDerivative
        (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_nativeW_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (coordinateDirection i) F x]
  exact coordinateFieldWordPartial_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [i] F G x


lemma coefficientDerivative_second_nativeW_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i k : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪ActualModelCommutatorWords.coefficientDerivative
        (coreDirectionalDerivative hO hD (coordinateDirection i))
        (ActualModelCommutatorWords.coefficientDerivative
          (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection k)
          (nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p)) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_second_nativeW_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (coordinateDirection i) (coordinateDirection k) F x]
  exact coordinateFieldWordPartial_nativeW_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [i,k] F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
