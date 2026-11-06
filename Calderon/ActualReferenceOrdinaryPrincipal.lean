import Calderon.ActualReferenceModelTrace
import Calderon.ActualReferenceDecomposition
import Calderon.ActualScalarPrincipalAdjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceOrdinaryPrincipal
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds MetricOperator ActualScalarPrincipalAdjoint
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile

/- Exact native weighted DD ordinary principal/first-base/zero-base expansion.
   Genuine all-mode domains, covector Γ, actual density/radius conventions retained.
   E/F, drift, J and fullphysicalP/U/H allocation are treated separately. -/

lemma directionalFDeriv_second_coordinate_sum
    (u : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (x X Y : R3) :
    directionalFDeriv X (directionalFDeriv Y u) x =
      ∑ i : Fin 3, ∑ j : Fin 3, (X i * Y j) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x := by
  have hDf := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hf (V W : R3) : directionalFDeriv V (directionalFDeriv W u) x =
      (fderiv ℝ (fderiv ℝ u) x V) W := by
    unfold directionalFDeriv
    rw [fderiv_clm_apply (hDf x) (differentiableAt_const W)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,add_zero,zero_add]
  simp_rw [hf]
  conv_lhs => rw [vector_eq_sum_coordinateDirection X,vector_eq_sum_coordinateDirection Y]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma directionalFDeriv_variable_frame
    (u : R3 → SphereL2) (E : R3 → R3) (hu : ContDiff ℝ ∞ u) (hE : ContDiff ℝ ∞ E)
    (x X : R3) :
    directionalFDeriv X (fun y => directionalFDeriv (E y) u y) x =
      (∑ i : Fin 3, ∑ j : Fin 3, (X i * E x j) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x) +
      directionalFDeriv (directionalFDeriv X E x) u x := by
  have hDf := hu.fderiv_right (m := ∞) (by simp)
  change directionalFDeriv X (fun y => fderiv ℝ u y (E y)) x = _
  rw [directionalFDeriv_clm_apply X (fderiv ℝ u) E hDf hE x]
  have hf : directionalFDeriv X (directionalFDeriv (E x) u) x =
      directionalFDeriv X (fderiv ℝ u) x (E x) := by
    unfold directionalFDeriv
    rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const (E x))]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,add_zero,zero_add]
  rw [← hf,directionalFDeriv_second_coordinate_sum u hu x X (E x)]
  rfl

lemma referenceCoFrame_frameEntry_duality
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (i j : Fin 3) :
    (∑ a : Fin 3, referenceCoFrameEntry g L i a (lam,x) *
      referenceMetricGramFrame g L (lam,x) a j) = if i = j then 1 else 0 := by
  have ht := congrArg (fun v : R3 => v j)
    (coordinateDirection_eq_sum_referenceGramFrame g hg L lam x i)
  simpa [coordinateDirection,eq_comm] using ht.symm

lemma physicalMixedQFrameCoefficient_reconstruction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (h : MatrixField) (x : R3) (i j : Fin 3) :
    (∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x *
      referenceMetricGramFrame g L (lam,x) a i * referenceMetricGramFrame g L (lam,x) b j) =
      referenceInverseEntryFamily g L i j (lam,x) + h x i j := by
  have ht : (∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x *
      referenceMetricGramFrame g L (lam,x) a i * referenceMetricGramFrame g L (lam,x) b j) =
      ∑ u : Fin 3, ∑ v : Fin 3, (referenceInverseEntryFamily g L u v (lam,x) + h x u v) *
        (∑ a : Fin 3, referenceCoFrameEntry g L u a (lam,x) * referenceMetricGramFrame g L (lam,x) a i) *
        (∑ b : Fin 3, referenceCoFrameEntry g L v b (lam,x) * referenceMetricGramFrame g L (lam,x) b j) := by
    simp only [physicalMixedQFrameCoefficient,Fin.sum_univ_three]
    ring
  rw [ht]
  simp_rw [referenceCoFrame_frameEntry_duality g hg L lam x]
  simp

lemma referenceFrameDerivative_sub_covectorConnection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (a b : Fin 3) (x : R3) :
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => referenceMetricGramFrame g L (lam,y) b) x -
      ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) c b • referenceMetricGramFrame g L (lam,x) c =
    -(referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b)) := by
  have ht := covariantFrameDerivative_eq_sum
    (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
    (fun y => referenceConnectionFamily g L (lam,y))
    (fun y => referenceMetricGramFrame g L (lam,y)) x
    (referenceMetricGramFrame g L (lam,x) a)
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) b
  change directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => referenceMetricGramFrame g L (lam,y) b) x +
      referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
        (referenceMetricGramFrame g L (lam,x) b) = _ at ht
  change directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => referenceMetricGramFrame g L (lam,y) b) x +
      referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
        (referenceMetricGramFrame g L (lam,x) b) =
      ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) c b • referenceMetricGramFrame g L (lam,x) c at ht
  rw [← ht]
  module

lemma ambientBesselField_one_two_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientBesselField hO hD 1 (by norm_num) G hG x,
      ambientBesselField hO hD 2 (by norm_num) G hG x) ∈ sphereBesselGraph hO hD 1 := by
  intro k
  change sphereHarmonicCoordinate hO hD k (ambientBesselField hO hD 2 (by norm_num) G hG x) = _
  rw [ambientBesselField_graph hO hD 2 (by norm_num) G hG x k,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x k]
  simp only [besselWeight,Real.rpow_one,Real.rpow_two,smul_smul,pow_two]

lemma normalizedReferenceAngularConnection_ambient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    normalizedReferenceAngularConnection hO hD g L lam x X
      (ambientBesselField hO hD 1 (by norm_num) G hG x) =
      ambientReferenceAngularConnection g L lam G hG x X := by
  have hN := normalizedReferenceAngularConnection_graph hO hD g L lam x X _ _
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
  have hA := ambientReferenceAngularConnection_graph hO hD g L lam G hG x X
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (normalizedReferenceAngularConnection hO hD g L lam x X
        (ambientBesselField hO hD 1 (by norm_num) G hG x)) =
      sphereHarmonicCoordinate hO hD k (ambientReferenceAngularConnection g L lam G hG x X)
  exact (hN k).trans (hA k).symm

def referenceWeightedZeroBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
    (ambientBesselField hO hD 1 (by norm_num) G hG x) +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (ambientBesselField hO hD 1 (by norm_num) G hG x - ambientSphereL2 G hG x)

def referenceWeightedZeroBaseBesselField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
    (ambientBesselField hO hD 2 (by norm_num) G hG x) +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (ambientBesselField hO hD 2 (by norm_num) G hG x -
        ambientBesselField hO hD 1 (by norm_num) G hG x)

lemma contDiff_referenceWeightedZeroBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedZeroBaseField hO hD g hg L lam δ R p a G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hK := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hW := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hF := contDiff_referenceFrameDerivative g hg L lam a _ hf
  unfold referenceWeightedZeroBaseField
  exact (hK.clm_apply hW).add (hF.smul
    (hW.sub (contDiff_ambientSphereL2 G hG)))

lemma contDiff_referenceWeightedZeroBaseBesselField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hK := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hW := contDiff_ambientBesselField hO hD 2 (by norm_num) G hG
  have hF := contDiff_referenceFrameDerivative g hg L lam a _ hf
  unfold referenceWeightedZeroBaseBesselField
  exact (hK.clm_apply hW).add (hF.smul
    (hW.sub (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)))

lemma referenceWeightedZeroBaseBesselField_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceWeightedZeroBaseField hO hD g hg L lam δ R p a G hG x,
      referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG x) ∈ sphereBesselGraph hO hD 1 := by
  intro k
  have hK1 := normalizedReferenceAngularConnection_graph hO hD g L lam x
    (referenceMetricGramFrame g L (lam,x) a) _ _
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)
  have hK2 := normalizedReferenceAngularConnection_graph hO hD g L lam x
    (referenceMetricGramFrame g L (lam,x) a) _ _
    (ambientBesselField_one_two_graph hO hD G hG x)
  change sphereHarmonicCoordinate hO hD k
      (referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG x) = _
  simp only [referenceWeightedZeroBaseBesselField,referenceWeightedZeroBaseField,
    map_add,map_sub,map_smul,smul_add,smul_sub]
  rw [hK2 k,hK1 k]
  simp_rw [ambientBesselField_graph hO hD 2 (by norm_num) G hG x k,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x k]
  simp only [map_smul,besselWeight,Real.rpow_one,Real.rpow_two,smul_smul,pow_two]
  module

lemma referenceWeightedInputField_ordinary_expansion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedInputField hO hD g hg L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x =
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (ambientSphereL2 G hG) x +
      referenceWeightedZeroBaseField hO hD g hg L lam δ R p a G hG x := by
  unfold referenceWeightedInputField
  rw [one_smul,referenceHorizontalField_eq_base_add_angularConnection g hg L lam a G hG x]
  unfold referenceWeightedZeroBaseField ambientDegreeField
  rw [normalizedReferenceAngularConnection_ambient hO hD g L lam G hG x
    (referenceMetricGramFrame g L (lam,x) a)]
  abel

lemma referenceWeightedBesselField_ordinary_expansion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedBesselField hO hD g hg L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x =
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (ambientBesselField hO hD 1 (by norm_num) G hG) x +
      referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG x := by
  have hBase := SectionFiveErrorForms.directionalDeriv_besselGraph hO hD 1
    (referenceMetricGramFrame g L (lam,x) a) (ambientSphereL2 G hG)
    (ambientBesselField hO hD 1 (by norm_num) G hG) (contDiff_ambientSphereL2 G hG)
    (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG) x
  have hZ := referenceWeightedZeroBaseBesselField_graph hO hD g hg L lam δ R p a G hG x
  have hNative := referenceWeightedBesselField_graph hO hD g hg L lam 1 a
    (fun y => Real.log (referenceRadius δ R p L y)) G hG x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (referenceWeightedBesselField hO hD g hg L lam 1 a
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x) = _
  rw [hNative k,referenceWeightedInputField_ordinary_expansion hO hD g hg L lam δ R p a G hG x,
    map_add,map_add,smul_add]
  exact congrArg₂ (· + ·) (hBase k).symm (hZ k).symm

lemma directionalFDeriv_referenceWeightedZeroBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceWeightedZeroBaseField hO hD g hg L lam δ R p b G hG) x =
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b)) x
      (ambientBesselField hO hD 1 (by norm_num) G hG x) +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b)
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x) +
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x •
      (ambientBesselField hO hD 1 (by norm_num) G hG x - ambientSphereL2 G hG x) +
    referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x •
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x -
        directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (ambientSphereL2 G hG) x) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hK := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam b
  have hB1 := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hphi := contDiff_ambientSphereL2 G hG
  have hF := contDiff_referenceFrameDerivative g hg L lam b _ hf
  have hProfile : ContDiff ℝ ∞ (fun y =>
      referenceFrameDerivative g L lam b (fun z => Real.log (referenceRadius δ R p L z)) y •
        (ambientBesselField hO hD 1 (by norm_num) G hG y - ambientSphereL2 G hG y)) := by
    simpa only [Pi.smul_def',Pi.sub_apply] using hF.smul (hB1.sub hphi)
  unfold referenceWeightedZeroBaseField
  rw [directionalFDeriv_add (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b) (ambientBesselField hO hD 1 (by norm_num) G hG y))
      (fun y => referenceFrameDerivative g L lam b (fun z => Real.log (referenceRadius δ R p L z)) y •
        (ambientBesselField hO hD 1 (by norm_num) G hG y - ambientSphereL2 G hG y))
      (hK.clm_apply hB1) hProfile x,
    directionalFDeriv_clm_apply _ _ _ hK hB1,
    directionalFDeriv_smul _ _ _ hF (hB1.sub hphi)]
  have he : directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => ambientBesselField hO hD 1 (by norm_num) G hG y - ambientSphereL2 G hG y) x =
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x -
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (ambientSphereL2 G hG) x := by
    unfold directionalFDeriv
    rw [fderiv_fun_sub (hB1.differentiable (by simp) x) (hphi.differentiable (by simp) x)]
    rfl
  rw [he]
  abel

def referenceCovectorPrincipalField
    (g : MatrixField) (L lam : ℝ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (referenceMetricGramFrame g L (lam,x) a i * referenceMetricGramFrame g L (lam,x) b j) •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
        (ambientSphereL2 G hG)) x

def referenceCovectorFirstBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  directionalFDeriv (-(referenceConnectionFamily g L (lam,x)
    (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b)))
      (ambientSphereL2 G hG) x +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b)
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x) +
    referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x •
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x -
        directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (ambientSphereL2 G hG) x) +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) b)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x) +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) b)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x -
        directionalFDeriv (referenceMetricGramFrame g L (lam,x) b) (ambientSphereL2 G hG) x)

def referenceCovectorZeroBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (fun y => normalizedReferenceAngularConnection hO hD g L lam y
      (referenceMetricGramFrame g L (lam,y) b)) x
    (ambientBesselField hO hD 1 (by norm_num) G hG x) +
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x •
      (ambientBesselField hO hD 1 (by norm_num) G hG x - ambientSphereL2 G hG x) +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
      (referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p b G hG x) -
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b •
      referenceWeightedZeroBaseField hO hD g hg L lam δ R p c G hG x +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p b G hG x -
        referenceWeightedZeroBaseField hO hD g hg L lam δ R p b G hG x)

theorem referenceWeightedCovectorSecondField_ordinary_decomposition
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedCovectorSecondField hO hD g hg L lam δ R p a b G hG x =
      referenceCovectorPrincipalField g L lam a b G hG x +
      referenceCovectorFirstBaseField hO hD g hg L lam δ R p a b G hG x +
      referenceCovectorZeroBaseField hO hD g hg L lam δ R p a b G hG x := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hphi := contDiff_ambientSphereL2 G hG
  have hE := contDiff_referenceMetricGramFrame_slice g hg L lam b
  have hZ := contDiff_referenceWeightedZeroBaseField hO hD g hg L lam δ R p hδ hR b G hG
  have he : referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG =
      fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) b) (ambientSphereL2 G hG) y +
        referenceWeightedZeroBaseField hO hD g hg L lam δ R p b G hG y :=
    funext (referenceWeightedInputField_ordinary_expansion hO hD g hg L lam δ R p b G hG)
  have hCov : directionalFDeriv
      (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => referenceMetricGramFrame g L (lam,y) b) x) (ambientSphereL2 G hG) x =
      directionalFDeriv (-(referenceConnectionFamily g L (lam,x)
        (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b)))
        (ambientSphereL2 G hG) x +
      ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) c b •
        directionalFDeriv (referenceMetricGramFrame g L (lam,x) c) (ambientSphereL2 G hG) x := by
    apply sub_eq_iff_eq_add.mp
    have ht := congrArg (fderiv ℝ (ambientSphereL2 G hG) x)
      (referenceFrameDerivative_sub_covectorConnection g hg L lam a b x)
    simpa only [map_sub,map_sum,map_smul,directionalFDeriv] using ht
  have hPartial : ContDiff ℝ ∞ (fun y =>
      directionalFDeriv (referenceMetricGramFrame g L (lam,y) b) (ambientSphereL2 G hG) y) := by
    simpa only [directionalFDeriv] using (hphi.fderiv_right (m := ∞) (by simp)).clm_apply hE
  unfold referenceWeightedCovectorSecondField
  rw [he,directionalFDeriv_add (referenceMetricGramFrame g L (lam,x) a)
    (fun y => directionalFDeriv (referenceMetricGramFrame g L (lam,y) b) (ambientSphereL2 G hG) y)
    (referenceWeightedZeroBaseField hO hD g hg L lam δ R p b G hG) hPartial hZ x,
    directionalFDeriv_variable_frame _ _ hphi hE x,
    directionalFDeriv_referenceWeightedZeroBaseField hO hD g hg L lam δ R p hδ hR a b G hG x,hCov]
  simp_rw [referenceWeightedInputField_ordinary_expansion hO hD g hg L lam δ R p _ G hG x,
    referenceWeightedBesselField_ordinary_expansion hO hD g hg L lam δ R p _ G hG x]
  unfold referenceCovectorPrincipalField referenceCovectorFirstBaseField referenceCovectorZeroBaseField
  simp only [map_add,smul_add,smul_sub,Fin.sum_univ_three]
  module

theorem referenceCovectorPrincipalField_trace_eq_scalarSecondBase
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
      physicalMixedQFrameCoefficient g L lam h a b x • referenceCovectorPrincipalField g L lam a b G hG x =
    scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x := by
  have ht : referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
      physicalMixedQFrameCoefficient g L lam h a b x • referenceCovectorPrincipalField g L lam a b G hG x =
      ∑ i : Fin 3, ∑ j : Fin 3,
      (referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
        physicalMixedQFrameCoefficient g L lam h a b x * referenceMetricGramFrame g L (lam,x) a i *
          referenceMetricGramFrame g L (lam,x) b j) •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG)) x := by
    simp only [referenceCovectorPrincipalField,Fin.sum_univ_three,smul_add,smul_smul]
    module
  rw [ht]
  simp_rw [physicalMixedQFrameCoefficient_reconstruction g hg L lam h x]
  rfl

def referenceWeightedFirstBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x • referenceCovectorFirstBaseField hO hD g hg L lam δ R p a b G hG x

def referenceWeightedZeroBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x • referenceCovectorZeroBaseField hO hD g hg L lam δ R p a b G hG x

theorem referenceWeightedCovectorTrace_ordinary_decomposition
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedCovectorTrace hO hD g hg L lam δ R p h G hG x =
      scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x +
      referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x +
      referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x := by
  unfold referenceWeightedCovectorTrace
  simp_rw [referenceWeightedCovectorSecondField_ordinary_decomposition hO hD g hg L lam δ R p hδ hR _ _ G hG x]
  simp only [smul_add,Finset.sum_add_distrib]
  rw [referenceCovectorPrincipalField_trace_eq_scalarSecondBase g hg L lam δ R p h G hG x]
  rfl

lemma contDiff_referenceCovectorFirstBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceCovectorFirstBaseField hO hD g hg L lam δ R p a b G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hEa := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hEb := contDiff_referenceMetricGramFrame_slice g hg L lam b
  have hphi := contDiff_ambientSphereL2 G hG
  have hB1 := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hGamma : ContDiff ℝ ∞ (fun x => -(referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b))) :=
    ((((contDiff_referenceConnectionFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).clm_apply hEa).clm_apply hEb).neg
  have hDaPhi := (hphi.fderiv_right (m := ∞) (by simp)).clm_apply hEa
  have hDbPhi := (hphi.fderiv_right (m := ∞) (by simp)).clm_apply hEb
  have hDaB1 := (hB1.fderiv_right (m := ∞) (by simp)).clm_apply hEa
  have hDbB1 := (hB1.fderiv_right (m := ∞) (by simp)).clm_apply hEb
  have hKa := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hKb := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam b
  have hFa := contDiff_referenceFrameDerivative g hg L lam a _ hf
  have hFb := contDiff_referenceFrameDerivative g hg L lam b _ hf
  unfold referenceCovectorFirstBaseField
  simpa only [directionalFDeriv,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.smul_apply'] using
    (((((hphi.fderiv_right (m := ∞) (by simp)).clm_apply hGamma).add (hKb.clm_apply hDaB1)).add
      (hFb.smul (hDaB1.sub hDaPhi))).add (hKa.clm_apply hDbB1)).add (hFa.smul (hDbB1.sub hDbPhi))

lemma contDiff_referenceCovectorZeroBaseField
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceCovectorZeroBaseField hO hD g hg L lam δ R p a b G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hEa := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hphi := contDiff_ambientSphereL2 G hG
  have hB1 := contDiff_ambientBesselField hO hD 1 (by norm_num) G hG
  have hKa := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hKb := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam b
  have hFa := contDiff_referenceFrameDerivative g hg L lam a _ hf
  have hFb := contDiff_referenceFrameDerivative g hg L lam b _ hf
  have hDaKb := (hKb.fderiv_right (m := ∞) (by simp)).clm_apply hEa
  have hDaFb := (hFb.fderiv_right (m := ∞) (by simp)).clm_apply hEa
  have hZ (c : Fin 3) := contDiff_referenceWeightedZeroBaseField hO hD g hg L lam δ R p hδ hR c G hG
  have hZ1 := contDiff_referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p hδ hR b G hG
  have hIndex : ContDiff ℝ ∞ (fun x => ∑ c : Fin 3,
      referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b •
        referenceWeightedZeroBaseField hO hD g hg L lam δ R p c G hG x) :=
    ContDiff.sum fun c _ =>
      (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _ hEa c b).smul (hZ c)
  unfold referenceCovectorZeroBaseField
  simpa only [directionalFDeriv,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.smul_apply'] using
    ((((hDaKb.clm_apply hB1).add (hDaFb.smul (hB1.sub hphi))).add
      (hKa.clm_apply hZ1)).sub hIndex).add (hFa.smul (hZ1.sub (hZ b)))

lemma contDiff_referenceWeightedFirstBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG) := by
  unfold referenceWeightedFirstBaseTrace
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h hh a b).smul
        (contDiff_referenceCovectorFirstBaseField hO hD g hg L lam δ R p hδ hR a b G hG))

lemma integrable_referenceWeightedFirstBaseTrace_density_pair
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K) (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 H hH)
    (contDiff_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG)
    (contDiff_ambientSphereL2 H hH) (hasCompactSupport_ambientSphereL2 H hH K hK hzH)

lemma contDiff_referenceWeightedZeroBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG) := by
  unfold referenceWeightedZeroBaseTrace
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h hh a b).smul
        (contDiff_referenceCovectorZeroBaseField hO hD g hg L lam δ R p hδ hR a b G hG))

lemma integrable_referenceWeightedZeroBaseTrace_density_pair
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K) (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g hg L lam _ (ambientSphereL2 H hH)
    (contDiff_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG)
    (contDiff_ambientSphereL2 H hH) (hasCompactSupport_ambientSphereL2 H hH K hK hzH)

theorem referenceModelTrace_ordinary_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (x : R3) (hsymm : ∀ i j, h x i j = h x j i)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    referenceModelTrace hF hO hD g hg L lam δ R p h G hG x =
      (2 : ℝ) • referenceAllModeRaising hF hO hD g hg L lam
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x +
      scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) x +
      referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x +
      referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x +
      physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x +
      physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x := by
  rw [referenceModelTrace_decomposition hF hO hD g hg L lam δ R p hδ hR h x hsymm G hG,
    referenceWeightedCovectorTrace_ordinary_decomposition hO hD g hg L lam δ R p hδ hR h G hG x]
  abel

end OAI.AnisotropicCalderon.ActualReferenceOrdinaryPrincipal
