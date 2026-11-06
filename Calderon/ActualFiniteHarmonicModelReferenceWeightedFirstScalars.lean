import Calderon.ActualReferenceDDHigherSpectralGraphs
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients
import Calderon.ProfileRadiusJets

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualReferenceParallelRaising ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDHigherSpectralGraphs ActualPhysicalMixedReferenceCancellation AmbientReferenceRaising
  AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection PrincipalCommutator
  ConformalDepth NaturalAngularAdjoint ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeReferenceWeightedFirstFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeReferenceWeightedFirstFunction

def nativeReferenceWeightedFirstScalarCoefficient
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (j : Fin 3) : R3 → ℝ := fun x =>
  -referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x *
      (referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
        (referenceMetricGramFrame g L (lam,x) b)) j

def nativeReferenceWeightedFirstDegreeCoefficient
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (j : Fin 3) : R3 → ℝ := fun x =>
  referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x *
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g L (lam,x) a j +
        referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g L (lam,x) b j)

def nativeReferenceWeightedFirstRotationCoefficient
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (j : Fin 3) (s t : Fin 3) : R3 → ℝ := fun x =>
  (1/2 : ℝ) * referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x *
      (referenceMetricGramFrame g L (lam,x) a j *
          referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) b) s t +
        referenceMetricGramFrame g L (lam,x) b j *
          referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) s t)

lemma contDiff_nativeReferenceWeightedFirstScalarCoefficient
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ContDiff ℝ ∞ (nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j) := by
  have hr := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedQFrameCoefficient g L lam h a b) :=
    contDiff_physicalMixedQFrameCoefficient g hg L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a b
  have hgamma (a b : Fin 3) : ContDiff ℝ ∞ (fun x =>
      (referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
        (referenceMetricGramFrame g L (lam,x) b)) j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      ((((contDiff_referenceConnectionFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).clm_apply
        (contDiff_referenceMetricGramFrame_slice g hg L lam a)).clm_apply
          (contDiff_referenceMetricGramFrame_slice g hg L lam b))
  unfold nativeReferenceWeightedFirstScalarCoefficient
  exact hr.neg.mul (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (hq a b).mul (hgamma a b))))

lemma contDiff_nativeReferenceWeightedFirstDegreeCoefficient
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ContDiff ℝ ∞ (nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j) := by
  have hr := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedQFrameCoefficient g L lam h a b) :=
    contDiff_physicalMixedQFrameCoefficient g hg L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a b
  have he (a : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g L (lam,x) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hp (a : Fin 3) : ContDiff ℝ ∞
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (_root_.OAI.AnisotropicCalderon.ConformalDepth.contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceWeightedFirstDegreeCoefficient
  exact hr.mul (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (hq a b).mul (((hp b).mul (he a)).add ((hp a).mul (he b))))))

lemma contDiff_nativeReferenceWeightedFirstRotationCoefficient
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (s t : Fin 3) :
    ContDiff ℝ ∞ (nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t) := by
  have hr := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedQFrameCoefficient g L lam h a b) :=
    contDiff_physicalMixedQFrameCoefficient g hg L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a b
  have he (a : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g L (lam,x) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g hg L lam a)
  have hGamma (a : Fin 3) : ContDiff ℝ ∞ (fun x =>
      referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) s t) :=
    contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam a) s t
  unfold nativeReferenceWeightedFirstRotationCoefficient
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (1/2 : ℝ))).mul hr).mul
    (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
      (hq a b).mul (((he a).mul (hGamma b)).add ((he b).mul (hGamma a))))))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
