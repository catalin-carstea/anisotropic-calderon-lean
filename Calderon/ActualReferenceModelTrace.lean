import Calderon.ActualReferenceScaledRaisingTransport
import Calderon.ActualPhysicalMixedReferenceCancellation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceModelTrace
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile ActualScalarPrincipalAdjoint

/- Genuine native E/F-free, drift-free ordered reference model trace.
   Raw raising/connection/degree domains and covector Γ index are retained.
   This is not identified with fullphysicalP/U/J/E/F/H. -/

lemma physicalMixedQFrameCoefficient_symm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (x : R3) (hsymm : ∀ i j, h x i j = h x j i) (a b : Fin 3) :
    physicalMixedQFrameCoefficient g L lam h a b x = physicalMixedQFrameCoefficient g L lam h b a x := by
  rw [physicalMixedQFrameCoefficient_decomposition g hg L lam h a b x,
    physicalMixedQFrameCoefficient_decomposition g hg L lam h b a x]
  have hd : (if a = b then (1 : ℝ) else 0) = if b = a then 1 else 0 := by simp [eq_comm]
  rw [hd]
  congr 1
  unfold physicalMixedFrameCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsymm j i]
  ring

def referenceModelInputField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceWeightedInputField hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      inverseRadiusRaisingField hF hO hD δ R L p a G hG x

def referenceModelBesselField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => referenceWeightedBesselField hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      (referenceRadius δ R p L x)⁻¹ • ambientRaisingBesselField hF hO hD a G hG x

lemma referenceModelBesselField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceModelInputField hF hO hD g hg L lam δ R p a G hG x,
      referenceModelBesselField hF hO hD g hg L lam δ R p a G hG x) ∈ sphereBesselGraph hO hD 1 := by
  intro k
  change sphereHarmonicCoordinate hO hD k (referenceModelBesselField hF hO hD g hg L lam δ R p a G hG x) =
    besselWeight 1 k • sphereHarmonicCoordinate hO hD k (referenceModelInputField hF hO hD g hg L lam δ R p a G hG x)
  simp only [referenceModelInputField,referenceModelBesselField,inverseRadiusRaisingField,map_add,map_smul]
  rw [referenceWeightedBesselField_graph hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG x k,
    ambientRaisingBesselField_graph hF hO hD a G hG x k]
  simp only [smul_add,smul_smul]
  module

lemma contDiff_referenceModelInputField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceModelInputField hF hO hD g hg L lam δ R p a G hG) := by
  exact (contDiff_referenceWeightedInputField hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y))
    (contDiff_log_referenceRadius_profile δ R L p hδ hR) G hG).add
      (contDiff_inverseRadiusRaisingField hF hO hD δ R L p hδ hR a G hG)

lemma contDiff_referenceModelBesselField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceModelBesselField hF hO hD g hg L lam δ R p a G hG) := by
  exact (contDiff_referenceWeightedBesselField hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y))
    (contDiff_log_referenceRadius_profile δ R L p hδ hR) G hG).add
      ((contDiff_inverse_referenceRadius δ R L p hδ hR).smul
        (contDiff_ambientRaisingBesselField hF hO hD a G hG))

lemma referenceModelInputField_degreeGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceModelInputField hF hO hD g hg L lam δ R p a G hG x,
      referenceModelBesselField hF hO hD g hg L lam δ R p a G hG x -
        referenceModelInputField hF hO hD g hg L lam δ R p a G hG x) ∈
      spectralGraph hO hD (fun k => (k : ℝ)) := by
  intro k
  rw [map_sub,referenceModelBesselField_graph hF hO hD g hg L lam δ R p a G hG x k]
  simp only [besselWeight,Real.rpow_one]
  module

lemma referenceModelInputField_angularConnectionGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (referenceModelInputField hF hO hD g hg L lam δ R p a G hG x,
      normalizedReferenceAngularConnection hO hD g L lam x X
        (referenceModelBesselField hF hO hD g hg L lam δ R p a G hG x)) ∈
      referenceAngularConnectionGraph hO hD g L lam x X := by
  exact normalizedReferenceAngularConnection_graph hO hD g L lam x X _ _
    (referenceModelBesselField_graph hF hO hD g hg L lam δ R p a G hG x)

lemma referenceModelInputField_raisingGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceModelInputField hF hO hD g hg L lam δ R p b G hG x,
      normalizedRaising hF hO hD a (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x)) ∈
      sphereRaisingGraph hF hO hD a := by
  exact normalizedRaising_graph hF hO hD a _ _
    (referenceModelBesselField_graph hF hO hD g hg L lam δ R p b G hG x)

def referenceWeightedCovectorSecondField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG) x +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
      (referenceWeightedBesselField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x) -
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b •
      referenceWeightedInputField hO hD g hg L lam 1 c
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (referenceWeightedBesselField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x -
        referenceWeightedInputField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x)

def referenceModelCovectorSecondField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (referenceModelInputField hF hO hD g hg L lam δ R p b G hG) x +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
      (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x) -
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b •
      referenceModelInputField hF hO hD g hg L lam δ R p c G hG x +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x -
        referenceModelInputField hF hO hD g hg L lam δ R p b G hG x)

lemma referenceModelCovectorSecondField_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG x =
      referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x +
      weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p b G hG x
        (referenceMetricGramFrame g L (lam,x) a) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  unfold referenceModelCovectorSecondField referenceModelInputField referenceModelBesselField
  rw [directionalFDeriv_add (referenceMetricGramFrame g L (lam,x) a)
    (referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG)
    (inverseRadiusRaisingField hF hO hD δ R L p b G hG)
    (contDiff_referenceWeightedInputField hO hD g hg L lam 1 b _ hf G hG)
    (contDiff_inverseRadiusRaisingField hF hO hD δ R L p hδ hR b G hG) x,map_add]
  unfold referenceWeightedCovectorSecondField weightedInverseRadiusRaisingCovectorDerivative
    inverseRadiusRaisingCovectorDerivative ambientDegreeRaisingField inverseRadiusRaisingField
  simp only [Fin.sum_univ_three,smul_add,smul_sub]
  change _ = _
  simp only [referenceFrameDerivative,directionalFDeriv]
  module

lemma referenceModelInputField_raising_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedRaising hF hO hD a (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x) =
      normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) +
      (referenceRadius δ R p L x)⁻¹ • ambientDoubleRaisingField hF hO hD a b G hG x := by
  simp only [referenceModelBesselField,map_add,map_smul]
  rfl

def referenceModelTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x •
      (referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG x +
        (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
          (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x))

def referenceWeightedCovectorTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x •
      referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x

lemma physicalPureQAngularCoefficient_eq_inverseRadius_mul
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (a b : Fin 3) (x : R3) :
    physicalPureQAngularCoefficient g L lam δ R p h a b x =
      (referenceRadius δ R p L x)⁻¹ * physicalMixedQFrameCoefficient g L lam h a b x := by
  unfold physicalPureQAngularCoefficient physicalMixedQFrameCoefficient
  simp only [div_eq_mul_inv,Fin.sum_univ_three]
  ring

lemma referenceModelTrace_term_expansion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG x +
      (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
        (referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x) =
    referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x +
      (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD b
        (referenceWeightedBesselField hO hD g hg L lam 1 a
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) +
      (referenceRadius δ R p L x)⁻¹ • normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) +
      ((referenceRadius δ R p L x)⁻¹)^2 • ambientDoubleRaisingField hF hO hD a b G hG x := by
  rw [referenceModelCovectorSecondField_decomposition hF hO hD g hg L lam δ R p hδ hR a b G hG x,
    referenceWeighted_inverseRadiusRaising_transport hF hO hD g hg L lam δ R p hδ hR a b G hG x,
    referenceModelInputField_raising_decomposition hF hO hD g hg L lam δ R p a b G hG x]
  simp only [smul_add,smul_smul,pow_two]
  abel

theorem referenceModelTrace_expansion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (x : R3) (hsymm : ∀ i j, h x i j = h x j i)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    referenceModelTrace hF hO hD g hg L lam δ R p h G hG x =
      referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x +
      physicalMixedQNativeRaising hF hO hD g hg L lam δ R p h G hG x +
      physicalPureQAngularRaising hF hO hD g hg L lam δ R p h G hG x := by
  have hr : referenceRadius δ R p L x ≠ 0 := (referenceRadius_pos δ R p L x hδ hR).ne'
  have hc (c : ℝ) : referenceRadius δ R p L x * (c * (referenceRadius δ R p L x)⁻¹) = c := by
    field_simp [hr] <;> ring
  have hcc (c : ℝ) : referenceRadius δ R p L x * (c * ((referenceRadius δ R p L x)⁻¹)^2) =
      (referenceRadius δ R p L x)⁻¹ * c := by
    field_simp [hr] <;> ring
  have hq (a b : Fin 3) := physicalMixedQFrameCoefficient_symm g hg L lam h x hsymm a b
  unfold referenceModelTrace referenceWeightedCovectorTrace physicalMixedQNativeRaising physicalPureQAngularRaising
  simp_rw [referenceModelTrace_term_expansion hF hO hD g hg L lam δ R p hδ hR _ _ G hG x,
    physicalPureQAngularCoefficient_eq_inverseRadius_mul g L lam δ R p h _ _ x]
  simp only [Fin.sum_univ_three,smul_add,smul_smul]
  simp_rw [hc,hcc]
  rw [hq 1 0,hq 2 0,hq 2 1]
  module

theorem referenceModelTrace_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (x : R3) (hsymm : ∀ i j, h x i j = h x j i)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    referenceModelTrace hF hO hD g hg L lam δ R p h G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g hg L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x +
      physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x +
      physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x := by
  rw [referenceModelTrace_expansion hF hO hD g hg L lam δ R p hδ hR h x hsymm G hG,
    physicalMixedQNativeRaising_decomposition hF hO hD g hg L lam δ R p h G hG x,
    physicalPureQAngularRaising_eq_perturbation hF hO hD g hg L lam δ R p h G hG x]
  abel

theorem referenceModelTrace_component_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (x : R3) (hsymm : ∀ i j, h x i j = h x j i)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    referenceModelTrace hF hO hD g hg L lam δ R p h G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g hg L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x +
      (physicalMixedFirstRaising hF hO hD g L lam h G hG x +
        physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x +
        physicalMixedConnectionRaising hF hO hD g L lam h G hG x) +
      physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x := by
  rw [referenceModelTrace_decomposition hF hO hD g hg L lam δ R p hδ hR h x hsymm G hG,
    physicalMixedNativeRaising_decomposition hF hO hD g hg L lam δ R p h G hG x]

lemma contDiff_normalizedReferenceAngularConnection_frame
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (a : Fin 3) :
    ContDiff ℝ ∞ (fun x => normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)) := by
  unfold normalizedReferenceAngularConnection
  exact (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam a) i j).smul contDiff_const).const_smul (1/2 : ℝ)

lemma contDiff_referenceWeightedCovectorSecondField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hInput (c : Fin 3) := contDiff_referenceWeightedInputField hO hD g hg L lam 1 c
    (fun y => Real.log (referenceRadius δ R p L y)) hf G hG
  have hBess (c : Fin 3) := contDiff_referenceWeightedBesselField hO hD g hg L lam 1 c
    (fun y => Real.log (referenceRadius δ R p L y)) hf G hG
  have hX := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hK := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hIndex : ContDiff ℝ ∞ (fun x => ∑ c : Fin 3,
      referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b •
        referenceWeightedInputField hO hD g hg L lam 1 c
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x) :=
    ContDiff.sum fun c _ =>
      (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _ hX c b).smul (hInput c)
  have hF := contDiff_referenceFrameDerivative g hg L lam a _ hf
  unfold referenceWeightedCovectorSecondField
  simpa only [directionalFDeriv,Pi.smul_apply',Pi.smul_apply,Pi.add_apply,Pi.sub_apply] using
    (((((hInput b).fderiv_right (m := ∞) (by simp)).clm_apply hX).add (hK.clm_apply (hBess b))).sub hIndex).add
      (hF.smul ((hBess b).sub (hInput b)))

lemma contDiff_referenceModelCovectorSecondField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG) := by
  have he : referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG =
      fun x => referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x +
        weightedInverseRadiusRaisingCovectorDerivative hF hO hD g L lam δ R p b G hG x
          (referenceMetricGramFrame g L (lam,x) a) :=
    funext (referenceModelCovectorSecondField_decomposition hF hO hD g hg L lam δ R p hδ hR a b G hG)
  rw [he]
  exact (contDiff_referenceWeightedCovectorSecondField hO hD g hg L lam δ R p hδ hR a b G hG).add
    (contDiff_referenceWeighted_inverseRadiusRaising hF hO hD g hg L lam δ R p hδ hR a b G hG)

lemma contDiff_referenceModelTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceModelTrace hF hO hD g hg L lam δ R p h G hG) := by
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h hh a b).smul
        ((contDiff_referenceModelCovectorSecondField hF hO hD g hg L lam δ R p hδ hR a b G hG).add
          ((contDiff_inverse_referenceRadius δ R L p hδ hR).smul
            ((normalizedRaising hF hO hD a).contDiff.comp
              (contDiff_referenceModelBesselField hF hO hD g hg L lam δ R p hδ hR b G hG)))))

lemma integrable_referenceModelTrace_density_pair
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K) (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪referenceModelTrace hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 H hH)
    (contDiff_referenceModelTrace hF hO hD g hg L lam δ R p hδ hR h hh G hG)
    (contDiff_ambientSphereL2 H hH) (hasCompactSupport_ambientSphereL2 H hH K hK hzH)

lemma referenceWeightedInputField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    referenceWeightedInputField hO hD g hg L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x = 0 := by
  have he := (inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x)).symm
  rw [he,referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,map_zero]

lemma referenceModelInputField_eq_zero_outside
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    referenceModelInputField hF hO hD g hg L lam δ R p a G hG x = 0 := by
  rw [referenceModelInputField,referenceWeightedInputField_eq_zero_outside hO hD g hg L lam δ R p a G hG K hK hz x hx,
    inverseRadiusRaisingField,ambientRaisingField_eq_zero hF hO hD a G hG K hz x hx,smul_zero,zero_add]

lemma referenceWeightedCovectorSecondField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x = 0 := by
  have he : (referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG) =ᶠ[𝓝 x] (fun _ : R3 => (0 : SphereL2)) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact referenceWeightedInputField_eq_zero_outside hO hD g hg L lam δ R p b G hG K hK hz y hy
  have hd : directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceWeightedInputField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG) x = 0 := by
    unfold directionalFDeriv
    rw [he.fderiv_eq]
    simp
  unfold referenceWeightedCovectorSecondField
  rw [hd]
  simp_rw [referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 _
    (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,
    referenceWeightedInputField_eq_zero_outside hO hD g hg L lam δ R p _ G hG K hK hz x hx]
  simp only [map_zero,zero_add,smul_zero,Finset.sum_const_zero,sub_self,add_zero]

lemma referenceModelCovectorSecondField_eq_zero_outside
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) :
    referenceModelCovectorSecondField hF hO hD g hg L lam δ R p a b G hG x = 0 := by
  rw [referenceModelCovectorSecondField_decomposition hF hO hD g hg L lam δ R p hδ hR a b G hG x,
    referenceWeightedCovectorSecondField_eq_zero_outside hO hD g hg L lam δ R p hδ hR a b G hG K hK hz x hx,
    referenceWeighted_inverseRadiusRaising_transport hF hO hD g hg L lam δ R p hδ hR a b G hG x,
    referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,
    map_zero,smul_zero,zero_add]

lemma hasCompactSupport_referenceModelInputField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceModelInputField hF hO hD g hg L lam δ R p a G hG) := by
  exact HasCompactSupport.intro hK
    (fun x hx => referenceModelInputField_eq_zero_outside hF hO hD g hg L lam δ R p a G hG K hK hz x hx)

lemma hasCompactSupport_referenceModelTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceModelTrace hF hO hD g hg L lam δ R p h G hG) := by
  exact HasCompactSupport.intro hK (by
    intro x hx
    have hW (b : Fin 3) : referenceModelBesselField hF hO hD g hg L lam δ R p b G hG x = 0 := by
      simp only [referenceModelBesselField,
        referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,
        ambientRaisingBesselField,ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
        ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
        zero_add,map_zero,smul_zero]
    unfold referenceModelTrace
    simp_rw [referenceModelCovectorSecondField_eq_zero_outside hF hO hD g hg L lam δ R p hδ hR _ _ G hG K hK hz x hx,hW]
    simp only [map_zero,smul_zero,add_zero,Finset.sum_const_zero])

end OAI.AnisotropicCalderon.ActualReferenceModelTrace
