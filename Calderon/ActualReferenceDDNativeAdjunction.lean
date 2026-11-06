import Calderon.ActualReferenceDDHigherSpectralGraphs
import Calderon.NaturalAngularAdjointIntegration

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualReferenceDDNativeAdjunction
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication ActualReferenceDDSpectralTransport
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceOrdinaryPrincipal ActualReferenceModelTrace ActualScalarPrincipalAdjoint
  ScalarBaseAdjoint PrincipalCommutator ReferenceDensityBounds NaturalAngularAdjoint
  ActualUnboundedFirstPrincipalFormBound ActualPerturbedDefect SmoothMetricFrame ConformalDepth RadiusProfile

/- Source-only native graph-domain adjunction. The input expansion was sealed
   before this proof-body candidate. Raw W1/W2 are never declared L2 bounded. -/

lemma spectralGraph_preserving_inner_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (A : SphereL2 →L[ℝ] SphereL2)
    (hA : PreservesSphereSpectralGraphs hO hD A)
    (u U v V : SphereL2)
    (hu : (u,U) ∈ spectralGraph hO hD w) (hv : (v,V) ∈ spectralGraph hO hD w) :
    ⟪A U,v⟫_ℝ = ⟪u,ContinuousLinearMap.adjoint A V⟫_ℝ := by
  calc
    _ = ⟪A u,V⟫_ℝ := spectralGraph_inner_symm hO hD w
      (A u) (A U) v V (hA w u U hu) hv
    _ = _ := (ContinuousLinearMap.adjoint_inner_right A u V).symm

def referenceWeightedFirstBaseAdjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  angularFirstBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
    (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h)
    (ambientBesselField hO hD 1 (by norm_num) G hG)

def referenceWeightedZeroBaseAdjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ContinuousLinearMap.adjoint
    (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x)
    (ambientBesselField hO hD 2 (by norm_num) G hG x)

def referenceWeightedCovectorTraceAdjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  scalarSecondBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
    (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x +
  referenceWeightedFirstBaseAdjoint hO hD g hg L lam δ R p h G hG x +
  referenceWeightedZeroBaseAdjoint hO hD g hg L lam δ R p h G hG x

def referenceWeightedCovectorTraceDefect
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceWeightedCovectorTraceAdjoint hO hD g hg L lam δ R p h G hG x -
  referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x

lemma referenceWeightedFirstBaseTrace_inner_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G H : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x,
      ambientSphereL2 H hH x⟫_ℝ =
    ⟪angularFirstBase coordinateDirection
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h)
      (ambientSphereL2 G hG) x,ambientBesselField hO hD 1 (by norm_num) H hH x⟫_ℝ := by
  rw [referenceWeightedFirstBaseTrace_eq_normalizedCoefficient]
  simp only [angularFirstBase,sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  have hu := SectionFiveErrorForms.directionalDeriv_besselGraph hO hD 1
    (coordinateDirection j) (ambientSphereL2 G hG)
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG) x
  exact spectralGraph_inner_symm hO hD (besselWeight 1) _ _ _ _
    (preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
      hO hD g hg L lam δ R p h j x (besselWeight 1) _ _ hu)
    (ambientBesselField_graph hO hD 1 (by norm_num) H hH x)

lemma referenceWeightedZeroBaseTrace_inner_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G H : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x,
      ambientSphereL2 H hH x⟫_ℝ =
    ⟪ambientSphereL2 G hG x,referenceWeightedZeroBaseAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
  rw [referenceWeightedZeroBaseTrace_eq_normalizedCoefficient]
  exact spectralGraph_preserving_inner_adjoint hO hD (besselWeight 2) _
    (preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace
      hO hD g hg L lam δ R p h x) _ _ _ _
    (ambientBesselField_graph hO hD 2 (by norm_num) G hG x)
    (ambientBesselField_graph hO hD 2 (by norm_num) H hH x)

theorem compact_referenceWeightedFirstBaseTrace_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField) (hh : ContDiff ℝ ∞ h)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
    ∫ x, referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,referenceWeightedFirstBaseAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
  simp_rw [referenceWeightedFirstBaseTrace_inner_adjoint hO hD g hg L lam δ R p h G H hG hH]
  exact compact_angularFirstBase_adjoint coordinateDirection _ _ _ _
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id))
    (fun j => contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR h hh j)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD 1 (by norm_num) H hH)
    (hasCompactSupport_ambientSphereL2 G hG K hK hzG)
    (fun x => (referenceDensityFamily_pos g hg L (lam,x)).ne')

lemma contDiff_referenceWeightedCovectorTraceAdjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField) (hh : ContDiff ℝ ∞ h)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedCovectorTraceAdjoint hO hD g hg L lam δ R p h G hG) := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hne := fun x => (referenceDensityFamily_pos g hg L (lam,x)).ne'
  have hhentry := fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh
  have hS := contDiff_scalarSecondBaseAdjoint coordinateDirection _ _ _ hm
    (contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hhentry)
    (contDiff_ambientSphereL2 G hG) hne
  have hF := contDiff_angularFirstBaseAdjoint coordinateDirection _ _ _ hm
    (fun j => contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR h hh j)
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) hne
  have hZ := (contDiff_angularAdjoint _
    (contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p hδ hR h hh)).clm_apply
    (contDiff_ambientBesselField hO hD 2 (by norm_num) G hG)
  exact (hS.add hF).add hZ

lemma contDiff_referenceWeightedCovectorTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField) (hh : ContDiff ℝ ∞ h)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG) := by
  have he : referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG =
      fun x => scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
        (ambientSphereL2 G hG) x +
        referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x +
        referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x :=
    funext (referenceWeightedCovectorTrace_ordinary_decomposition hO hD g hg L lam δ R p hδ hR h G hG)
  rw [he]
  have hhentry := fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh
  exact ((contDiff_scalarSecondBase coordinateDirection _ _
    (contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hhentry)
    (contDiff_ambientSphereL2 G hG)).add
    (contDiff_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p hδ hR h hhentry G hG)).add
    (contDiff_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p hδ hR h hhentry G hG)

theorem compact_referenceWeightedCovectorTrace_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField) (hh : ContDiff ℝ ∞ h)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
    ∫ x, referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,referenceWeightedCovectorTraceAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
  let mu := fun y => referenceDensityFamily g L (lam,y)
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp := fun x => referenceDensityFamily_pos g hg L (lam,x)
  have hne := fun x => (hp x).ne'
  have hu := contDiff_ambientSphereL2 G hG
  have hv := contDiff_ambientSphereL2 H hH
  have hcG := hasCompactSupport_ambientSphereL2 G hG K hK hzG
  have hcH := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  have hhentry := fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh
  have ha := contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hhentry
  have hB := fun j => contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p hδ hR h hh j
  have hC := contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p hδ hR h hh
  have hSB := contDiff_scalarSecondBase coordinateDirection _ _ ha hu
  have hSA := contDiff_scalarSecondBaseAdjoint coordinateDirection mu _ _ hm ha hv hne
  have hFB := contDiff_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p hδ hR h hhentry G hG
  have hFA := contDiff_angularFirstBaseAdjoint coordinateDirection mu _ _ hm hB
    (contDiff_ambientBesselField hO hD 1 (by norm_num) H hH) hne
  have hCB := contDiff_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p hδ hR h hhentry G hG
  have hCA := (contDiff_angularAdjoint _ hC).clm_apply
    (contDiff_ambientBesselField hO hD 2 (by norm_num) H hH)
  have iSB := integrable_density_pair_of_contDiff g hg L lam _ _ hSB hv hcH
  have iFB := integrable_density_pair_of_contDiff g hg L lam _ _ hFB hv hcH
  have iCB := integrable_density_pair_of_contDiff g hg L lam _ _ hCB hv hcH
  have iSA : Integrable (fun x => mu x * ⟪ambientSphereL2 G hG x,
      scalarSecondBaseAdjoint coordinateDirection mu (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 H hH) x⟫_ℝ) := by
    simpa only [real_inner_comm] using integrable_density_pair_of_contDiff g hg L lam _ _ hSA hu hcG
  have iFA : Integrable (fun x => mu x * ⟪ambientSphereL2 G hG x,
      referenceWeightedFirstBaseAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ) := by
    have hi := integrable_density_pair_of_contDiff g hg L lam _ _ hFA hu hcG
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => congrArg (fun z : ℝ => mu x*z)
      (real_inner_comm
        (angularFirstBaseAdjoint coordinateDirection mu
          (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h)
          (ambientBesselField hO hD 1 (by norm_num) H hH) x)
        (ambientSphereL2 G hG x)).symm
  have iCA : Integrable (fun x => mu x * ⟪ambientSphereL2 G hG x,
      referenceWeightedZeroBaseAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ) := by
    have hi := integrable_density_pair_of_contDiff g hg L lam _ _ hCA hu hcG
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => congrArg (fun z : ℝ => mu x*z)
      (real_inner_comm
        (angularAdjoint (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h) x
          (ambientBesselField hO hD 2 (by norm_num) H hH x))
        (ambientSphereL2 G hG x)).symm
  have hsum (f0 f1 f2 : R3 → ℝ)
      (i0 : Integrable f0) (i1 : Integrable f1) (i2 : Integrable f2) :
      (∫ x, f0 x+f1 x+f2 x) = (∫ x, f0 x)+(∫ x, f1 x)+(∫ x, f2 x) := by
    have h01 : (∫ x, f0 x+f1 x) = (∫ x, f0 x)+(∫ x, f1 x) := by
      simpa only [Pi.add_apply] using integral_add i0 i1
    have h012 : (∫ x, f0 x+f1 x+f2 x) = (∫ x, f0 x+f1 x)+(∫ x, f2 x) := by
      simpa only [Pi.add_apply] using integral_add (i0.add i1) i2
    rw [h012,h01]
  have hscalar := compact_scalarSecondBase_adjoint coordinateDirection mu _ _ _ hm ha hu hv hcG hp
  have hfirst := compact_referenceWeightedFirstBaseTrace_adjoint hO hD g hg L lam δ R p hδ hR h hh G H hG hH K hK hzG
  have hzero : (∫ x, mu x *
      ⟪referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, mu x * ⟪ambientSphereL2 G hG x,referenceWeightedZeroBaseAdjoint hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrArg (fun z : ℝ => mu x*z)
      (referenceWeightedZeroBaseTrace_inner_adjoint hO hD g hg L lam δ R p h G H hG hH x)
  dsimp [mu] at iSA iFA iCA hscalar hzero
  simp only [referenceWeightedCovectorTrace_ordinary_decomposition hO hD g hg L lam δ R p hδ hR,
    referenceWeightedCovectorTraceAdjoint,inner_add_left,inner_add_right,mul_add]
  rw [hsum _ _ _ iSB iFB iCB,hsum _ _ _ iSA iFA iCA,hscalar,hfirst,hzero]

theorem referenceWeightedCovectorTraceDefect_normal_form
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedCovectorTraceDefect hO hD g hg L lam δ R p h G hG x =
      (scalarSecondBaseAdjoint coordinateDirection (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x -
        scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x) +
      (referenceWeightedFirstBaseAdjoint hO hD g hg L lam δ R p h G hG x -
        referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x) +
      (referenceWeightedZeroBaseAdjoint hO hD g hg L lam δ R p h G hG x -
        referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x) := by
  rw [referenceWeightedCovectorTraceDefect,referenceWeightedCovectorTraceAdjoint,
    referenceWeightedCovectorTrace_ordinary_decomposition hO hD g hg L lam δ R p hδ hR]
  abel

end OAI.AnisotropicCalderon.ActualReferenceDDNativeAdjunction
