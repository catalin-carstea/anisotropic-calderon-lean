import Calderon.ActualReferenceDDNativeAdjunction
import Calderon.ActualNormalizedSecondDriftNativeAdjunction

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondModelErrorAssembly
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication AmbientReferenceRaising
  ActualReferenceModelTrace ActualReferenceOrdinaryPrincipal ActualReferenceDDNativeAdjunction
  ActualPhysicalMixedNative ActualPhysicalMixedFirst ActualPhysicalMixedProfile
  ActualPhysicalMixedConnection ActualPhysicalPureAngular ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondDriftNativeAdjunction
  ActualScalarPrincipalAdjoint ActualPerturbedDefect ScalarBaseAdjoint PrincipalCommutator
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  ActualUnboundedFirstPrincipalFormBound SmoothMetricFrame ConformalDepth RadiusProfile

/- Actual normalized Q/h/b E/F-free model. No claim that this model equals
   the physical moving-sphere operator with E/F trace corrections. -/

def normalizedSecondReferenceModelOperator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceModelTrace hF hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  normalizedSecondModelDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x

def normalizedSecondModelError
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceWeightedCovectorTrace hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  physicalMixedNativeRaising hF hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  physicalPureAngularRaising hF hO hD g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x

def normalizedSecondModelErrorAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceWeightedCovectorTraceAdjoint hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  physicalMixedNativeAdjoint hF hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  physicalPureAngularAdjoint hF hO hD g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
  normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG x

def normalizedSecondModelErrorDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p G hG x -
  normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x

lemma contDiff_referenceNormalizedPrincipalDifference
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) : ContDiff ℝ ∞ (referenceNormalizedPrincipalDifference g1 g2 L lam) := by
  exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j =>
    contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j

lemma referenceNormalizedPrincipalDifference_symm
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (i j : Fin 3) :
    referenceNormalizedPrincipalDifference g1 g2 L lam x i j =
      referenceNormalizedPrincipalDifference g1 g2 L lam x j i := by
  have hs := referenceNormalizedPrincipalDifference_isHermitian g1 g2 hg1 hg2 L lam x
  simpa only [Matrix.conjTranspose_apply,star_trivial] using
    congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A j i) hs.eq

theorem normalizedSecondReferenceModelOperator_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondReferenceModelOperator hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g1 hg1 L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x +
      normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x := by
  unfold normalizedSecondReferenceModelOperator normalizedSecondModelError
  rw [referenceModelTrace_decomposition hF hO hD g1 hg1 L lam δ R p hδ hR _ x
    (referenceNormalizedPrincipalDifference_symm g1 g2 hg1 hg2 L lam x) G hG,
    normalizedSecondModelDriftField_split hF hO hD g1 g2 hg1 L lam δ R p G hG hδ hR x]
  abel

theorem normalizedSecondModelError_ordinary_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      scalarSecondBase coordinateDirection
        (fun y => referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (ambientSphereL2 G hG) x +
      referenceWeightedFirstBaseTrace hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      referenceWeightedZeroBaseTrace hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedNativeRaising hF hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalPureAngularRaising hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG x := by
  unfold normalizedSecondModelError
  rw [referenceWeightedCovectorTrace_ordinary_decomposition hO hD g1 hg1 L lam δ R p hδ hR]
  have ha : actualPrincipalMatrix g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) =
      fun y => referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y :=
    funext (actualPrincipalMatrix_normalized_eq g1 g2 L lam δ R p)
  rw [ha]

theorem normalizedSecondModelErrorDefect_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelErrorDefect hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      referenceWeightedCovectorTraceDefect hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedFirstDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedProfileDefect hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedConnectionDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalPureAngularDefect hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x := by
  unfold normalizedSecondModelErrorDefect normalizedSecondModelErrorAdjoint normalizedSecondModelError
  have he := physicalMixedNativeDefect_decomposition hF hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x
  unfold physicalMixedNativeDefect at he
  simp only [referenceWeightedCovectorTraceDefect,physicalPureAngularDefect,
    normalizedSecondWeightedDriftAdjointDefect]
  rw [show physicalMixedNativeAdjoint hF hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x =
      physicalMixedNativeRaising hF hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      (physicalMixedFirstDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedProfileDefect hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedConnectionDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x) from by
      have := sub_eq_iff_eq_add.mp he
      exact this.trans (add_comm _ _)]
  abel

lemma contDiff_normalizedSecondModelError_and_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG) ∧
    ContDiff ℝ ∞ (normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p G hG) := by
  have hh := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have he := fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j
  have hDD := contDiff_referenceWeightedCovectorTrace hO hD g1 hg1 L lam δ R p hδ hR _ hh G hG
  have hDDA := contDiff_referenceWeightedCovectorTraceAdjoint hO hD g1 hg1 L lam δ R p hδ hR _ hh G hG
  have hM := contDiff_physicalMixedNativeFields hF hO hD g1 hg1 L lam δ R p _ hδ hR he G hG
  have hP := contDiff_physicalPureAngularFields hF hO hD g1 L lam δ R p _ hg1 hδ hR he G hG
  have hDrift := contDiff_normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR
  have hDA := contDiff_normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR
  exact ⟨((hDD.add hM.1).add hP.1).add hDrift,((hDDA.add hM.2.1).add hP.2.1).add hDA⟩

theorem compact_normalizedSecondModelError_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 H hH x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪ambientSphereL2 G hG x,normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ := by
  have hh := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have he := fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j
  have hu := contDiff_ambientSphereL2 G hG
  have hv := contDiff_ambientSphereL2 H hH
  have hcG := hasCompactSupport_ambientSphereL2 G hG K hK hzG
  have hcH := hasCompactSupport_ambientSphereL2 H hH K hK hzH
  have hDD := contDiff_referenceWeightedCovectorTrace hO hD g1 hg1 L lam δ R p hδ hR _ hh G hG
  have hDDA := contDiff_referenceWeightedCovectorTraceAdjoint hO hD g1 hg1 L lam δ R p hδ hR _ hh H hH
  have hM := contDiff_physicalMixedNativeFields hF hO hD g1 hg1 L lam δ R p _ hδ hR he G hG
  have hMA := contDiff_physicalMixedNativeFields hF hO hD g1 hg1 L lam δ R p _ hδ hR he H hH
  have hP := contDiff_physicalPureAngularFields hF hO hD g1 L lam δ R p _ hg1 hδ hR he G hG
  have hPA := contDiff_physicalPureAngularFields hF hO hD g1 L lam δ R p _ hg1 hδ hR he H hH
  have hDrift := contDiff_normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR
  have hDA := contDiff_normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p H hH hg2 hδ hR
  have iDD := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hDD hv hcH
  have iM := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hM.1 hv hcH
  have iP := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hP.1 hv hcH
  have iD := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hDrift hv hcH
  have iDDA := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hDDA hu hcG
  have iMA := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hMA.2.1 hu hcG
  have iPA := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hPA.2.1 hu hcG
  have iDA := integrable_density_pair_of_contDiff g1 hg1 L lam _ _ hDA hu hcG
  have iDDAR : Integrable (fun x => referenceDensityFamily g1 L (lam,x) *
      ⟪ambientSphereL2 G hG x,referenceWeightedCovectorTraceAdjoint hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using iDDA
  have iMAR : Integrable (fun x => referenceDensityFamily g1 L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedNativeAdjoint hF hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using iMA
  have iPAR : Integrable (fun x => referenceDensityFamily g1 L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalPureAngularAdjoint hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using iPA
  have iDAR : Integrable (fun x => referenceDensityFamily g1 L (lam,x) *
      ⟪ambientSphereL2 G hG x,normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using iDA
  have hsum (f0 f1 f2 f3 : R3 → ℝ)
      (i0 : Integrable f0) (i1 : Integrable f1) (i2 : Integrable f2) (i3 : Integrable f3) :
      (∫ x, f0 x+f1 x+f2 x+f3 x) =
        (∫ x, f0 x)+(∫ x, f1 x)+(∫ x, f2 x)+(∫ x, f3 x) := by
    have h01 : (∫ x, f0 x+f1 x) = (∫ x, f0 x)+(∫ x, f1 x) := by
      simpa only [Pi.add_apply] using integral_add i0 i1
    have h012 : (∫ x, f0 x+f1 x+f2 x) = (∫ x, f0 x+f1 x)+(∫ x, f2 x) := by
      simpa only [Pi.add_apply] using integral_add (i0.add i1) i2
    have h0123 : (∫ x, f0 x+f1 x+f2 x+f3 x) = (∫ x, f0 x+f1 x+f2 x)+(∫ x, f3 x) := by
      simpa only [Pi.add_apply] using integral_add ((i0.add i1).add i2) i3
    rw [h0123,h012,h01]
  simp only [normalizedSecondModelError,normalizedSecondModelErrorAdjoint,inner_add_left,inner_add_right,mul_add]
  rw [hsum _ _ _ _ iDD iM iP iD,hsum _ _ _ _ iDDAR iMAR iPAR iDAR,
    compact_referenceWeightedCovectorTrace_adjoint hO hD g1 hg1 L lam δ R p hδ hR _ hh G H hG hH K K hK hK hzG hzH,
    compact_physicalMixedNative_adjoint hF hO hD g1 hg1 L lam δ R p _ hδ hR he G H hG hH K K hK hK hzG hzH,
    compact_physicalPureAngular_adjoint hF hO hD g1 L lam δ R p _ hg1 hδ hR he G H hG hH K K hK hK hzG hzH,
    compact_normalizedSecondWeightedDrift_adjoint hO hD g1 g2 hg1 L lam δ R p G H hG hH hg2 hδ hR K hK hzG hzH]

end OAI.AnisotropicCalderon.ActualNormalizedSecondModelErrorAssembly
