import Calderon.ActualFiniteHarmonicModelSecondAngularNormalization
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
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
private abbrev nativeWSecondJetFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSecondJetFunction
lemma contDiff_nativeWSecondAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) := by
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
  unfold nativeWSecondAngularCoefficient
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


lemma coefficientDerivative_nativeW_secondAngular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x =
      directionalFDeriv v (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  have hact : (fun y => nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y) =
      (fun y => (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y (U y)) :=
    funext (fun y => nativeW_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y) x -
      nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeW_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) (U : R3 → SphereL2)
    (contDiff_nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) U.property.1 x,hW]
  abel


lemma coefficientDerivative_second_nativeW_secondAngular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u)
        (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x =
      directionalFDeriv v (directionalFDeriv u
        (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p)) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y = directionalFDeriv u (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y
        (coreWeightOperator hO hD (besselWeight 2) G y) :=
    coefficientDerivative_nativeW_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR u G y
  have hact : (fun y => A F y) =
      (fun y => directionalFDeriv u (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y (U y)) :=
    funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => A F y) x - A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p))
    (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
