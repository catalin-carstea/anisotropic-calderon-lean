import Calderon.ActualReferenceDDSpectralTransport
import Calderon.ActualReferenceDDHigherGeometryJets
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherSpectralGraphs
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising AmbientReferenceCovariantCore
  ActualHorizontalNormBridge ActualReferenceParallelRaising ActualReferenceModelTrace
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDGeometryBounds
  ActualReferenceDDCoefficientSmallness ActualReferenceDDSpectralTransport
  ActualReferenceDDHigherGeometryJets ActualPhysicalMixedReferenceCancellation
  ActualPhysicalMixedNative ReferenceDensityBounds MetricOperator
  PrincipalCommutator ConformalDepth RadiusProfile ActualScalarPrincipalAdjoint

lemma contDiff_referenceWeightedZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3) :
    ContDiff ℝ ∞ (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a) := by
  have hfa := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold referenceWeightedZeroBaseNormalizedCoefficient
  exact (contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a).add
    (hfa.smul contDiff_const)

lemma contDiff_referenceCovectorFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b j : Fin 3) :
    ContDiff ℝ ∞ (referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j) := by
  have hE (c : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g L (lam,x) c j) :=
    (contDiff_piLp_apply (p := 2) (i := j)).comp
      (contDiff_referenceMetricGramFrame_slice g hg L lam c)
  have hGamma : ContDiff ℝ ∞ (fun x => referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) j) :=
    (contDiff_referenceDDGammaFrameEntryJoint g hg L a b j).comp
      (contDiff_const.prodMk contDiff_id)
  have hNegGamma : ContDiff ℝ ∞ (fun x =>
      (-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
        (referenceMetricGramFrame g L (lam,x) b)) j)) := by
    exact hGamma.neg
  have hK (c : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam c
  have hfa (c : Fin 3) := contDiff_referenceFrameDerivative g hg L lam c _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold referenceCovectorFirstBaseNormalizedCoefficient
  exact (((hNegGamma.smul contDiff_const).add ((hE a).smul (hK b))).add
    ((hE b).smul (hK a))).add
      ((((hfa b).mul (hE a)).add ((hfa a).mul (hE b))).smul contDiff_const)

lemma contDiff_referenceWeightedFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (j : Fin 3) :
    ContDiff ℝ ∞ (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) := by
  have he : referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j =
      fun x => referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
        physicalMixedQFrameCoefficient g L lam h a b x •
          referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x := by
    funext x
    exact referenceWeightedFirstBaseNormalizedCoefficient_eq_sum hO hD g hg L lam δ R p h j x
  rw [he]
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h (fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh) a b).smul
        (contDiff_referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b j))

lemma contDiff_referenceCovectorZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3) :
    ContDiff ℝ ∞ (referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b) := by
  have hK (c : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam c
  have hfa (c : Fin 3) := contDiff_referenceFrameDerivative g hg L lam c _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hZ (c : Fin 3) := contDiff_referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR c
  have hdK : ContDiff ℝ ∞ (fun x => directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) b)) x) := by
    have he : (fun x => referenceDDFrameAngularConnectionDerivativeJoint hO hD g L a b (lam,x)) =
        fun x => directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
          (fun y => normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) b)) x := by
      funext x
      exact referenceDDFrameAngularConnectionDerivativeJoint_eq hO hD g hg L lam x a b
    rw [← he]
    exact (contDiff_referenceDDFrameAngularConnectionDerivativeJoint hO hD g hg L a b).comp
      (contDiff_const.prodMk contDiff_id)
  have hdf : ContDiff ℝ ∞ (fun x => directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x) := by
    exact ((hfa b).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hkappa (c : Fin 3) : ContDiff ℝ ∞ (fun x => referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b) := by
    have he : (fun x => referenceFrameConnectionJoint g L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z a) (lam,x) c b) =
        fun x => referenceFrameConnectionCoefficient g L lam x
          (referenceMetricGramFrame g L (lam,x) a) c b := by
      funext x
      exact referenceFrameConnectionJoint_eq g hg L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z a) (lam,x) c b
    rw [← he]
    exact (contDiff_referenceFrameConnectionJoint g hg L
      (fun z : ℝ × R3 => referenceMetricGramFrame g L z a)
      (contDiff_referenceMetricGramFrame g hg L a) c b).comp (contDiff_const.prodMk contDiff_id)
  unfold referenceCovectorZeroBaseNormalizedCoefficient
  exact ((((hdK.clm_comp contDiff_const).add (hdf.smul contDiff_const)).add
    ((hK a).clm_comp (hZ b))).sub
      (ContDiff.sum fun c _ => (hkappa c).smul ((hZ c).clm_comp contDiff_const))).add
        ((hfa a).smul ((hZ b).sub ((hZ b).clm_comp contDiff_const)))

lemma contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h) := by
  unfold referenceWeightedZeroBaseNormalizedCoefficientTrace
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h (fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh) a b).smul
        (contDiff_referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b))

lemma preservesSphereSpectralGraphs_coordinateFieldWordPartial
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, PreservesSphereSpectralGraphs hO hD (A x))
    (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (coordinateFieldWordPartial w A x) := by
  induction w generalizing x with
  | nil => exact hgraph x
  | cons k w ih =>
    exact preservesSphereSpectralGraphs_directionalFDeriv hO hD
      (coordinateFieldWordPartial w A) (contDiff_coordinateFieldWordPartial w A hA)
      (fun y => ih y) x (coordinateDirection k)

lemma preservesSphereSpectralGraphs_coordinateWord_referenceWeightedZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3) (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD
      (coordinateFieldWordPartial w (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a)
    (fun y => preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a y) w x

lemma preservesSphereSpectralGraphs_coordinateWord_referenceCovectorFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b j : Fin 3) (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD
      (coordinateFieldWordPartial w (referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b j)
    (fun y => preservesSphereSpectralGraphs_referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j y) w x

lemma preservesSphereSpectralGraphs_coordinateWord_referenceWeightedFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (j : Fin 3) (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD
      (coordinateFieldWordPartial w (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR h hh j)
    (fun y => preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j y) w x

lemma preservesSphereSpectralGraphs_coordinateWord_referenceCovectorZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3) (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD
      (coordinateFieldWordPartial w (referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR a b)
    (fun y => preservesSphereSpectralGraphs_referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b y) w x

lemma preservesSphereSpectralGraphs_coordinateWord_referenceWeightedZeroBaseNormalizedCoefficientTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (w : List (Fin 3)) (x : R3) :
    PreservesSphereSpectralGraphs hO hD
      (coordinateFieldWordPartial w (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p hδ hR h hh)
    (fun y => preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h y) w x

end OAI.AnisotropicCalderon.ActualReferenceDDHigherSpectralGraphs
