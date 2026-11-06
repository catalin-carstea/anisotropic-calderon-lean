import Calderon.ActualFiniteHarmonicModelReference
import Calderon.ActualFiniteHarmonicModelCoefficientCore
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph BoundedAngularShift AngularShiftGraph SmoothSphereFields
  AmbientAngularShift AngularDerivativeBesselField ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceDDSpectralTransport ActualReferenceDDNativeAdjunction
  ActualReferenceOrdinaryPrincipal ActualReferenceParallelRaising
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondDriftNativeAdjunction
  ActualNormalizedSecondDriftWeightedCoefficients ActualNormalizedSecondMetricDrift
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection
  ActualPhysicalPureAngular ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
  SmoothMetricFrame MovingFrameConnection SpectralCoreRegularity
open SmoothAngularApplication SmoothAmbientAngularCasimir

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeZeroCoefficientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeZeroCoefficientFunction

def nativeCField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def nativeWField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

lemma contDiff_modelAdjointZeroCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x => adjointZeroCoefficient coordinateDirection
      (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x : R3 => (referenceDensityFamily g1 L (lam,x))⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hh := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 =>
      actualPrincipalMatrix g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) x i j) := by
    unfold actualPrincipalMatrix
    exact hr.mul (((contDiff_referenceInverseEntryFamily g1 hg1 L i j).comp
      (contDiff_const.prodMk contDiff_id)).add ((contDiff_apply_apply ℝ ℝ i j).comp hh))
  unfold adjointZeroCoefficient
  exact hmi.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_directionalFDeriv (coordinateDirection j) _
      (contDiff_directionalFDeriv (coordinateDirection i) _ (hm.mul (ha i j))))

def coreModelZeroCoefficientAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhentry (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0 : ContDiff ℝ ∞ K0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
      hδ hR h hh
  have hK0g (x : R3) : PreservesSphereSpectralGraphs hO hD (K0 x) :=
    preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace
      hO hD g1 hg1 L lam δ R p h x
  have hprof (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedProfileCoefficient g1 L lam δ R p h a) :=
    contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a
  have hconn (a b c : Fin 3) : ContDiff ℝ ∞ (physicalMixedConnectionCoefficient g1 L lam h a b c) :=
    contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhentry a b c
  have hpure (a b : Fin 3) : ContDiff ℝ ∞ (physicalPureAngularCoefficient g1 L lam δ R p h a b) :=
    contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a b
  let J0 := normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p
  have hJ0 : ContDiff ℝ ∞ J0 :=
    contDiff_normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR
  have hJ0g (x : R3) : PreservesSphereSpectralGraphs hO hD (J0 x) := by
    unfold J0 normalizedSecondDriftZeroNormalizedCoefficient
    apply preservesSphereSpectralGraphs_smul
    apply preservesSphereSpectralGraphs_sum
    intro a
    apply preservesSphereSpectralGraphs_smul
    exact preservesSphereSpectralGraphs_comp hO hD _ _
      (preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficient
        hO hD g1 hg1 L lam δ R p a x)
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  exact coreCoefficientAction hO hD K0 hK0 hK0g * coreWeightOperator hO hD (besselWeight 2) +
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedProfileCoefficient g1 L lam δ R p h a)
      (hprof a) * coreNormalizedRaising hO hD hF a *
        (coreWeightOperator hO hD (besselWeight 2) - coreWeightOperator hO hD (besselWeight 1))) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      coreScalar hO hD (physicalMixedConnectionCoefficient g1 L lam h a b c)
        (hconn a b c) * coreRaising hO hD hF a * coreRotation hO hD b c) +
    (∑ a : Fin 3, ∑ b : Fin 3,
      coreScalar hO hD (physicalPureAngularCoefficient g1 L lam δ R p h a b)
        (hpure a b) * coreNormalizedRaising hO hD hF a *
          coreWeightOperator hO hD (besselWeight 1) * coreRaising hO hD hF b) +
    coreCoefficientAction hO hD J0 hJ0 hJ0g * coreWeightOperator hO hD (besselWeight 2)

def coreModelDefectZeroCoefficientAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhentry (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0 : ContDiff ℝ ∞ K0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
      hδ hR h hh
  have hK0g (x : R3) : PreservesSphereSpectralGraphs hO hD (K0 x) :=
    preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace
      hO hD g1 hg1 L lam δ R p h x
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
  have hKg (j : Fin 3) (x : R3) : PreservesSphereSpectralGraphs hO hD (K j x) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
      hO hD g1 hg1 L lam δ R p h j x
  let H (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (K j)
  have hB (j : Fin 3) : ContDiff ℝ ∞ (fun y => mu y • angularAdjoint (K j) y) :=
    hmu.smul (contDiff_angularAdjoint (K j) (hK j))
  have hBg (j : Fin 3) (x : R3) : PreservesSphereSpectralGraphs hO hD
      (mu x • angularAdjoint (K j) x) :=
    preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_adjoint hO hD (K j x) (hKg j x))
  have hH (j : Fin 3) : ContDiff ℝ ∞ (H j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hB j)
  have hHg (j : Fin 3) (x : R3) : PreservesSphereSpectralGraphs hO hD (H j x) :=
    preservesSphereSpectralGraphs_directionalFDeriv hO hD
      (fun y => mu y • angularAdjoint (K j) y) (hB j) (hBg j) x (coordinateDirection j)
  have hK0a : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.adjoint (K0 x)) :=
    contDiff_angularAdjoint K0 hK0
  have hK0ag (x : R3) : PreservesSphereSpectralGraphs hO hD (ContinuousLinearMap.adjoint (K0 x)) :=
    preservesSphereSpectralGraphs_adjoint hO hD (K0 x) (hK0g x)
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
  let driftConnection := coreScalar hO hD (referenceRadius δ R p L) hr *
    ∑ a : Fin 3, coreScalar hO hD
      (fun x => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) (hb a) *
      ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3, coreScalar hO hD
        (fun y => referenceFrameConnectionCoefficient g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a) b c) (hGamma a b c) * coreRotation hO hD b c)
  exact coreScalar hO hD
      (fun x => adjointZeroCoefficient coordinateDirection mu
        (actualPrincipalMatrix g1 L lam δ R p h) x)
      (contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR) -
    coreScalar hO hD (fun x => (mu x)⁻¹) hmui *
      (∑ j : Fin 3, coreCoefficientAction hO hD (H j) (hH j) (hHg j) *
        coreWeightOperator hO hD (besselWeight 1)) +
    (coreCoefficientAction hO hD (fun x => ContinuousLinearMap.adjoint (K0 x)) hK0a hK0ag -
      coreCoefficientAction hO hD K0 hK0 hK0g) * coreWeightOperator hO hD (besselWeight 2) +
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedDensityCorrection g1 L lam h a)
      (hdens a) * coreDerivative hO hD hF a) +
    ((∑ a : Fin 3, coreScalar hO hD (physicalMixedProfileCoefficient g1 L lam δ R p h a)
      (hprof a) * coreNormalizedDerivative hO hD hF a *
        (coreWeightOperator hO hD (besselWeight 2) - (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1))) -
      (∑ a : Fin 3, coreScalar hO hD (physicalMixedProfileCoefficient g1 L lam δ R p h a)
        (hprof a) * coreNormalizedRaising hO hD hF a *
          (coreWeightOperator hO hD (besselWeight 2) - coreWeightOperator hO hD (besselWeight 1)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      coreScalar hO hD (fun y => -physicalMixedConnectionCoefficient g1 L lam h a b c y)
        (hconn a b c).neg * coreRotation hO hD b c * coreDerivative hO hD hF a) -
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        coreScalar hO hD (physicalMixedConnectionCoefficient g1 L lam h a b c)
          (hconn a b c) * coreRaising hO hD hF a * coreRotation hO hD b c)) +
    ((∑ a : Fin 3, ∑ b : Fin 3,
      coreScalar hO hD (physicalPureAngularCoefficient g1 L lam δ R p h a b)
        (hpure a b) * coreNormalizedDerivative hO hD hF b *
          coreWeightOperator hO hD (besselWeight 1) * coreDerivative hO hD hF a) -
      (∑ a : Fin 3, ∑ b : Fin 3,
        coreScalar hO hD (physicalPureAngularCoefficient g1 L lam δ R p h a b)
          (hpure a b) * coreNormalizedRaising hO hD hF a *
            coreWeightOperator hO hD (besselWeight 1) * coreRaising hO hD hF b)) +
    (-2 : ℝ) • driftConnection -
    coreScalar hO hD (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p)
      (contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR)

lemma modelZero_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreModelZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  let G := representativeAmbient hO hD r
  let hG := contDiff_representativeAmbient hO hD r
  have h0 : ambientSphereL2 G hG x = F x := ambientSphereL2_representative hO hD r x
  have h1 : ambientBesselField hO hD 1 (by norm_num) G hG x =
      coreWeightOperator hO hD (besselWeight 1) F x :=
    (coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) x).symm
  have h2 : ambientBesselField hO hD 2 (by norm_num) G hG x =
      coreWeightOperator hO hD (besselWeight 2) F x :=
    (coreWeightOperator_eq_ambientBesselField hO hD F r 2 (by norm_num) x).symm
  have hPR (a : Fin 3) : ambientMixedRaisingDegreeField hF hO hD a G hG x =
      normalizedRaising hF hO hD a
        (coreWeightOperator hO hD (besselWeight 2) F x -
          coreWeightOperator hO hD (besselWeight 1) F x) := by
    unfold ambientMixedRaisingDegreeField ambientMixedDegreeBesselField
    rw [h2,h1]
  have hRC (a b c : Fin 3) : ambientMixedRaisingRotationField hF hO hD a b c G hG x =
      coreRaising hO hD hF a (coreRotation hO hD b c F) x := by
    apply sphereRaisingGraph_output_unique hF hO hD a (coreRotation hO hD b c F x)
    · rw [coreRotation_eq_ambientAngularRotation hO hD b c F r x]
      exact ambientRaisingField_graph hF hO hD a (ambientAngularRotation b c G)
        (contDiff_ambientAngularRotation b c G hG) x
    · exact coreRaising_graph hO hD hF a (coreRotation hO hD b c F) x
  have hRR (a b : Fin 3) : ambientDoubleRaisingField hF hO hD a b G hG x =
      normalizedRaising hF hO hD a
        (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF b F) x) := by
    unfold ambientDoubleRaisingField
    rw [← coreWeightRaising_eq_ambientRaisingBesselField hO hD hF b F r x]
  have hJ0 : normalizedSecondDriftZeroBaseField hO hD g1 g2 hg1 L lam δ R p G hG x =
      normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
    rw [← h2]
    unfold normalizedSecondDriftZeroBaseField normalizedSecondDriftZeroNormalizedCoefficient
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply]
    rw [inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x]
    simp_rw [referenceWeightedZeroBaseNormalizedCoefficient_apply_one hO hD g1 hg1 L lam δ R p _ G hG x]
  change modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x = _
  unfold modelZeroBaseField
  rw [referenceWeightedZeroBaseTrace_eq_normalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x,h2,hJ0]
  simp only [physicalMixedProfileRaising, physicalMixedConnectionRaising, physicalPureAngularRaising,
    hPR, hRC, hRR, coreModelZeroCoefficientAction,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, coreCoefficientAction, coreScalar,
    coreNormalizedRaising, coreNormalizedDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma modelDefectZero_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreModelDefectZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  let G := representativeAmbient hO hD r
  let hG := contDiff_representativeAmbient hO hD r
  have h0 : ambientSphereL2 G hG x = F x := ambientSphereL2_representative hO hD r x
  have h1 : ambientBesselField hO hD 1 (by norm_num) G hG x =
      coreWeightOperator hO hD (besselWeight 1) F x :=
    (coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) x).symm
  have h2 : ambientBesselField hO hD 2 (by norm_num) G hG x =
      coreWeightOperator hO hD (besselWeight 2) F x :=
    (coreWeightOperator_eq_ambientBesselField hO hD F r 2 (by norm_num) x).symm
  have hPR (a : Fin 3) : ambientMixedRaisingDegreeField hF hO hD a G hG x =
      normalizedRaising hF hO hD a
        (coreWeightOperator hO hD (besselWeight 2) F x -
          coreWeightOperator hO hD (besselWeight 1) F x) := by
    unfold ambientMixedRaisingDegreeField ambientMixedDegreeBesselField
    rw [h2,h1]
  have hRC (a b c : Fin 3) : ambientMixedRaisingRotationField hF hO hD a b c G hG x =
      coreRaising hO hD hF a (coreRotation hO hD b c F) x := by
    apply sphereRaisingGraph_output_unique hF hO hD a (coreRotation hO hD b c F x)
    · rw [coreRotation_eq_ambientAngularRotation hO hD b c F r x]
      exact ambientRaisingField_graph hF hO hD a (ambientAngularRotation b c G)
        (contDiff_ambientAngularRotation b c G hG) x
    · exact coreRaising_graph hO hD hF a (coreRotation hO hD b c F) x
  have hRR (a b : Fin 3) : ambientDoubleRaisingField hF hO hD a b G hG x =
      normalizedRaising hF hO hD a
        (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF b F) x) := by
    unfold ambientDoubleRaisingField
    rw [← coreWeightRaising_eq_ambientRaisingBesselField hO hD hF b F r x]
  have hPD (a : Fin 3) : ambientMixedDegreeDerivativeField hF hO hD a G hG x =
      normalizedDerivative hF hO hD a
        (coreWeightOperator hO hD (besselWeight 2) F x -
          (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1) F x) := by
    unfold ambientMixedDegreeDerivativeField
    rw [h2,h1]
  have hDC (a b c : Fin 3) : ambientMixedRotatedDerivativeField hF hO hD a b c G hG x =
      coreRotation hO hD b c (coreDerivative hO hD hF a F) x := by
    have hg := ambientMixedRotatedDerivativeField_graph hF hO hD a b c G hG x
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k
        (ambientMixedRotatedDerivativeField hF hO hD a b c G hG x) =
      sphereHarmonicCoordinate hO hD k
        (coreBlockOperator hO hD (fun l => SmoothSphereRotationProjection.harmonicSphereRotation l b c)
          (coreDerivative hO hD hF a F) x)
    rw [coreBlockOperator_coordinate hO hD _ (coreDerivative hO hD hF a F) x k,
      coreDerivative_eq_ambientDerivativeField hO hD hF a F r x]
    exact hg k
  have hDD (a b : Fin 3) : ambientDoubleDerivativeField hF hO hD b a G hG x =
      normalizedDerivative hF hO hD b
        (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF a F) x) := by
    unfold ambientDoubleDerivativeField
    rw [← coreWeightDerivative_eq_ambientDerivativeBesselField hO hD hF a F r x]
  have hDerivativeRep (a : Fin 3) : ambientDerivativeField hF hO hD a G hG x = coreDerivative hO hD hF a F x :=
    (coreDerivative_eq_ambientDerivativeField hO hD hF a F r x).symm
  have hOmega (b c : Fin 3) : ambientSphereL2 (ambientAngularRotation b c G)
      (contDiff_ambientAngularRotation b c G hG) x = coreRotation hO hD b c F x :=
    (coreRotation_eq_ambientAngularRotation hO hD b c F r x).symm
  have hDriftConn : normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x =
      referenceRadius δ R p L x • ∑ a : Fin 3,
        normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
          ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
            referenceFrameConnectionCoefficient g1 L lam x (referenceMetricGramFrame g1 L (lam,x) a) b c •
              coreRotation hO hD b c F x) := by
    unfold normalizedSecondDriftAngularConnectionField
    simp_rw [normalizedReferenceAngularConnection_ambient hO hD g1 L lam G hG x]
    simp only [ambientReferenceAngularConnection,hOmega]
  change modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p G hG x = _
  unfold modelDefectZeroBaseField
  simp only [referenceWeightedZeroBaseAdjoint, physicalMixedProfileDefect,
    physicalMixedProfileAdjoint, physicalMixedProfileRaising,
    physicalMixedConnectionDefect, physicalMixedConnectionAdjoint, physicalMixedConnectionRaising,
    physicalPureAngularDefect, physicalPureAngularAdjoint, physicalPureAngularRaising]
  rw [referenceWeightedZeroBaseTrace_eq_normalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x]
  simp only [h0,h1,h2,hDerivativeRep,hPR,hPD,hRC,hDC,hRR,hDD,hDriftConn,
    coreModelDefectZeroCoefficientAction,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, coreCoefficientAction, coreScalar,
    coreNormalizedRaising, coreNormalizedDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma nativeCField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeCField hO hD hF g1 g2 hg1 L lam δ R p F =
      (coreModelZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F : R3 → SphereL2) := by
  funext x
  exact modelZero_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
    (coreAmbientRepresentative hO hD F) x

lemma nativeWField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeWField hO hD hF g1 g2 hg1 L lam δ R p F =
      (coreModelDefectZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F : R3 → SphereL2) := by
  funext x
  exact modelDefectZero_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
    (coreAmbientRepresentative hO hD F) x

def nativeC
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeCField hO hD hF g1 g2 hg1 L lam δ R p F, by
    rw [nativeCField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F]
    exact (coreModelZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeCField hO hD hF g1 g2 hg1 L lam δ R p (F+G) =
      nativeCField hO hD hF g1 g2 hg1 L lam δ R p F +
      nativeCField hO hD hF g1 g2 hg1 L lam δ R p G
    simp only [nativeCField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeCField hO hD hF g1 g2 hg1 L lam δ R p (c • F) =
      c • nativeCField hO hD hF g1 g2 hg1 L lam δ R p F
    simp only [nativeCField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

def nativeW
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeWField hO hD hF g1 g2 hg1 L lam δ R p F, by
    rw [nativeWField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F]
    exact (coreModelDefectZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeWField hO hD hF g1 g2 hg1 L lam δ R p (F+G) =
      nativeWField hO hD hF g1 g2 hg1 L lam δ R p F +
      nativeWField hO hD hF g1 g2 hg1 L lam δ R p G
    simp only [nativeWField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeWField hO hD hF g1 g2 hg1 L lam δ R p (c • F) =
      c • nativeWField hO hD hF g1 g2 hg1 L lam δ R p F
    simp only [nativeWField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

lemma nativeCField_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    modelZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeCField hO hD hF g1 g2 hg1 L lam δ R p F x := by
  rw [modelZero_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x]
  exact congrFun (nativeCField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).symm x

lemma nativeWField_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    modelDefectZeroBaseField hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeWField hO hD hF g1 g2 hg1 L lam δ R p F x := by
  rw [modelDefectZero_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x]
  exact congrFun (nativeWField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).symm x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
