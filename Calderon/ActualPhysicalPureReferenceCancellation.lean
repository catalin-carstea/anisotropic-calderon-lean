import Calderon.ActualPhysicalPureAngular
import Calderon.MetricFrameTrace
import Calderon.HarmonicDerivativeOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter MvPolynomial
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalPureReferenceCancellation
open SphereHarmonic SmoothSphereRotationProjection SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph HarmonicDerivativeOperator SphereDerivativeAdjoint AngularPolynomial
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift SmoothMetricFrame
  ActualHorizontalNormBridge ActualBalancedFirstPrincipalError ActualPhysicalPureAngular
  MetricFrameTrace MetricOperator MetricVolume ReferenceDensityBounds ConformalDepth RadiusProfile

/- Actual inverse reference metric contraction of native raw pure angular composition.
   All harmonic modes and native raising/lowering graph domains retained.
   Physical trace/E/F/Gamma/U/J assembly is a separate obligation. -/

lemma referenceInverseEntry_eq_frame_sum (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (i j : Fin 3) :
    referenceInverseEntryFamily g L i j (lam,x) =
      ∑ a : Fin 3, referenceMetricGramFrame g L (lam,x) a i * referenceMetricGramFrame g L (lam,x) a j := inverseMatrix_entry_eq_metricFrame_sum (referenceMetric (dilatedMetric g lam) L x)
    (dilatedReferenceMetric_posDef g hg lam L x) _
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) i j

lemma referenceFrameEntry_coFrame_duality (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (c a : Fin 3) :
    (∑ i : Fin 3, frameEntry g L c i (lam,x) * referenceCoFrameEntry g L i a (lam,x)) =
      if c = a then 1 else 0 := by
  have ht := congrArg (fun v : R3 =>
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x v,
      referenceMetricGramFrame g L (lam,x) a⟫_ℝ)
    (referenceGramFrame_eq_sum_coordinateDirection g L lam x c)
  have he := referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x) c a
  rw [he] at ht
  simpa only [map_sum,map_smul,sum_inner,real_inner_smul_left,referenceCoFrameEntry] using ht.symm

lemma referenceInverse_coFrame_contraction (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, referenceInverseEntryFamily g L i j (lam,x) *
      referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)) =
      if a = b then 1 else 0 := by
  have ht : (∑ i : Fin 3, ∑ j : Fin 3, referenceInverseEntryFamily g L i j (lam,x) *
      referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)) =
      ∑ c : Fin 3, (∑ i : Fin 3, frameEntry g L c i (lam,x) * referenceCoFrameEntry g L i a (lam,x)) *
        (∑ j : Fin 3, frameEntry g L c j (lam,x) * referenceCoFrameEntry g L j b (lam,x)) := by
    simp_rw [referenceInverseEntry_eq_frame_sum g hg L lam x]
    simp only [frameEntry,Fin.sum_univ_three]
    ring
  rw [ht]
  simp_rw [referenceFrameEntry_coFrame_duality g hg L lam x]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_three]

lemma sum_double_harmonicDerivativeAdjoint_eq_zero (hF : SphereFischerInner) (k : ℕ)
    (u : harmonicSphereSubspace k) :
    (∑ i : Fin 3, harmonicDerivativeAdjoint hF (k+1) i (harmonicDerivativeAdjoint hF k i u)) = 0 := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  have himage (i : Fin 3) : harmonicDerivativeAdjoint hF k i (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialSphereMap (k+1) ⟨sphereDerivativeAdjoint k i p,
        sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property⟩ := by
    rw [harmonicDerivativeAdjoint_apply_image]
    rfl
  simp_rw [himage,harmonicDerivativeAdjoint_apply_image]
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ i : Fin 3, polynomialSphereL2
    (sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p))) = 0
  rw [← map_sum,sum_double_sphereDerivativeAdjoint_eq_zero hF k p p.property,map_zero]

lemma sum_double_sphereRaisingGraph_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u : SphereL2) (r rr : Fin 3 → SphereL2)
    (hr : ∀ i, (u,r i) ∈ sphereRaisingGraph hF hO hD i)
    (hrr : ∀ i, (r i,rr i) ∈ sphereRaisingGraph hF hO hD i) :
    (∑ i : Fin 3, rr i) = 0 := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  change sphereHarmonicCoordinate hO hD m (∑ i : Fin 3, rr i) =
    sphereHarmonicCoordinate hO hD m 0
  rw [map_sum,map_zero]
  cases m with
  | zero => exact Finset.sum_eq_zero (fun i hi => (hrr i).1)
  | succ m =>
    cases m with
    | zero =>
      apply Finset.sum_eq_zero
      intro i hi
      rw [(hrr i).2 0,(hr i).1,map_zero]
    | succ k =>
      have hc (i : Fin 3) : sphereHarmonicCoordinate hO hD ((k+1)+1) (rr i) =
          harmonicDerivativeAdjoint hF (k+1) i
            (harmonicDerivativeAdjoint hF k i (sphereHarmonicCoordinate hO hD k u)) := by
        rw [(hrr i).2 (k+1),(hr i).2 k]
      simp_rw [hc]
      exact sum_double_harmonicDerivativeAdjoint_eq_zero hF k _

lemma sum_ambientDoubleRaisingField_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (∑ i : Fin 3, ambientDoubleRaisingField hF hO hD i i G hG x) = 0 := sum_double_sphereRaisingGraph_eq_zero hF hO hD (ambientSphereL2 G hG x)
    (fun i => ambientRaisingField hF hO hD i G hG x)
    (fun i => ambientDoubleRaisingField hF hO hD i i G hG x)
    (fun i => ambientRaisingField_graph hF hO hD i G hG x)
    (fun i => ambientDoubleRaisingField_graph hF hO hD i i G hG x)

lemma sum_double_harmonicDerivative_eq_zero (hF : SphereFischerInner) (k : ℕ)
    (u : harmonicSphereSubspace ((k+1)+1)) :
    (∑ i : Fin 3, harmonicDerivative hF k i (harmonicDerivative hF (k+1) i u)) = 0 := by
  rcases harmonicPolynomialSphereMap_surjective ((k+1)+1) u with ⟨p,rfl⟩
  have himage (i : Fin 3) : harmonicDerivative hF (k+1) i
      (harmonicPolynomialSphereMap ((k+1)+1) p) =
      harmonicPolynomialSphereMap (k+1) ⟨pderiv i p,
        pderiv_harmonicHomogeneous_succ (k+1) i p p.property⟩ := by
    rw [harmonicDerivative_apply_image]
    rfl
  simp_rw [himage,harmonicDerivative_apply_image]
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ i : Fin 3, polynomialSphereL2 (pderiv i (pderiv i p))) = 0
  rw [← map_sum]
  change polynomialSphereL2 (laplacian p) = 0
  rw [p.property.2,map_zero]

lemma sum_double_sphereDerivativeGraph_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u : SphereL2) (d dd : Fin 3 → SphereL2)
    (hd : ∀ i, (u,d i) ∈ sphereDerivativeGraph hF hO hD i)
    (hdd : ∀ i, (d i,dd i) ∈ sphereDerivativeGraph hF hO hD i) :
    (∑ i : Fin 3, dd i) = 0 := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (∑ i : Fin 3, dd i) =
    sphereHarmonicCoordinate hO hD k 0
  rw [map_sum,map_zero]
  have hc (i : Fin 3) : sphereHarmonicCoordinate hO hD k (dd i) =
      harmonicDerivative hF k i (harmonicDerivative hF (k+1) i
        (sphereHarmonicCoordinate hO hD ((k+1)+1) u)) := by
    rw [hdd i k,hd i (k+1)]
  simp_rw [hc]
  exact sum_double_harmonicDerivative_eq_zero hF k _

lemma sum_ambientDoubleDerivativeField_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (∑ i : Fin 3, ambientDoubleDerivativeField hF hO hD i i G hG x) = 0 := sum_double_sphereDerivativeGraph_eq_zero hF hO hD (ambientSphereL2 G hG x)
    (fun i => ambientDerivativeField hF hO hD i G hG x)
    (fun i => ambientDoubleDerivativeField hF hO hD i i G hG x)
    (fun i => ambientDerivativeField_graph hF hO hD i G hG x)
    (fun i => ambientDoubleDerivativeField_graph hF hO hD i i G hG x)

def physicalPureQAngularCoefficient (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (a b : Fin 3) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ((referenceInverseEntryFamily g L i j (lam,x) + h x i j) / referenceRadius δ R p L x) *
      referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)

lemma physicalPureQAngularCoefficient_decomposition (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (a b : Fin 3) (x : R3) :
    physicalPureQAngularCoefficient g L lam δ R p h a b x =
      ((if a = b then 1 else 0) / referenceRadius δ R p L x) +
        physicalPureAngularCoefficient g L lam δ R p h a b x := by
  have ht : (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceInverseEntryFamily g L i j (lam,x) / referenceRadius δ R p L x) *
        referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)) =
      (∑ i : Fin 3, ∑ j : Fin 3, referenceInverseEntryFamily g L i j (lam,x) *
        referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)) /
        referenceRadius δ R p L x := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [physicalPureQAngularCoefficient,add_div,add_mul,Finset.sum_add_distrib]
  rw [ht,referenceInverse_coFrame_contraction g hg L lam x]
  rfl

def physicalPureQAngularRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, physicalPureQAngularCoefficient g L lam δ R p h a b x •
    ambientDoubleRaisingField hF hO hD a b G hG x

def physicalPureQAngularAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, physicalPureQAngularCoefficient g L lam δ R p h a b x •
    ambientDoubleDerivativeField hF hO hD b a G hG x

theorem physicalPureQAngularRaising_eq_perturbation
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalPureQAngularRaising hF hO hD g hg L lam δ R p h G hG x =
      physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x := by
  have hdiag (a : Fin 3) : (∑ b : Fin 3,
      ((if a = b then 1 else 0) / referenceRadius δ R p L x) •
        ambientDoubleRaisingField hF hO hD a b G hG x) =
      (1 / referenceRadius δ R p L x) • ambientDoubleRaisingField hF hO hD a a G hG x := by
    fin_cases a <;> simp [Fin.sum_univ_three]
  simp only [physicalPureQAngularRaising,physicalPureQAngularCoefficient_decomposition g hg L lam δ R p h,
    add_smul,Finset.sum_add_distrib]
  simp_rw [hdiag]
  rw [← Finset.smul_sum,sum_ambientDoubleRaisingField_eq_zero hF hO hD G hG x,
    smul_zero,zero_add]
  rfl

theorem physicalPureQAngularAdjoint_eq_perturbation
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalPureQAngularAdjoint hF hO hD g hg L lam δ R p h G hG x =
      physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x := by
  have hdiag (a : Fin 3) : (∑ b : Fin 3,
      ((if a = b then 1 else 0) / referenceRadius δ R p L x) •
        ambientDoubleDerivativeField hF hO hD b a G hG x) =
      (1 / referenceRadius δ R p L x) • ambientDoubleDerivativeField hF hO hD a a G hG x := by
    fin_cases a <;> simp [Fin.sum_univ_three]
  simp only [physicalPureQAngularAdjoint,physicalPureQAngularCoefficient_decomposition g hg L lam δ R p h,
    add_smul,Finset.sum_add_distrib]
  simp_rw [hdiag]
  rw [← Finset.smul_sum,sum_ambientDoubleDerivativeField_eq_zero hF hO hD G hG x,
    smul_zero,zero_add]
  rfl

theorem physicalPureQAngular_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪physicalPureQAngularRaising hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x,physicalPureQAngularAdjoint hF hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
  rw [physicalPureQAngularRaising_eq_perturbation,physicalPureQAngularAdjoint_eq_perturbation]
  exact physicalPureAngular_inner_adjoint hF hO hD g L lam δ R p h G H hG hH x

end OAI.AnisotropicCalderon.ActualPhysicalPureReferenceCancellation
