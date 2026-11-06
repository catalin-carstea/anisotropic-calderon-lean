import Calderon.ActualReferenceDDGeometryBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceDDCoefficientSmallness
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient ActualReferenceDDGeometryBounds
  ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds MetricOperator ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile WeightedBaseSpectral

/- Actual native DD coefficient order-zero bounds. All higher coefficient jets,
   half-derivative forms, full physical U/E/F/drift allocation remain separate. -/

lemma norm_id_sub_inverseDegreeMultiplier_le_two
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ‖ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD‖ ≤ 2 := by
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ SphereL2‖ + ‖inverseDegreeMultiplier hO hD‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add ContinuousLinearMap.norm_id_le (norm_inverseDegreeMultiplier_le_one hO hD)
    _ = 2 := by norm_num

lemma norm_inverseDegreeMultiplier_sub_square_le_two
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ‖inverseDegreeMultiplier hO hD - (inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)‖ ≤ 2 := by
  have hDnorm := norm_inverseDegreeMultiplier_le_one hO hD
  have hSquare : ‖(inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)‖ ≤ 1 := by
    calc
      _ ≤ ‖inverseDegreeMultiplier hO hD‖ * ‖inverseDegreeMultiplier hO hD‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hDnorm hDnorm (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact (norm_sub_le _ _).trans (by linarith)

def referenceCovectorFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
    (referenceMetricGramFrame g L (lam,x) b)) j) • inverseDegreeMultiplier hO hD +
  referenceMetricGramFrame g L (lam,x) a j •
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b) +
  referenceMetricGramFrame g L (lam,x) b j •
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a) +
  (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g L (lam,x) a j +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g L (lam,x) b j) •
    (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)

lemma referenceWeightedFirstBaseNormalizedCoefficient_eq_sum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (j : Fin 3) (x : R3) :
    referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x =
      referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
        physicalMixedQFrameCoefficient g L lam h a b x •
          referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x := by
  rfl

lemma norm_referenceWeightedZeroBaseNormalizedCoefficient_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (x : R3) (M F beta : ℝ) (hM : 1 ≤ M) (hF : 1 ≤ F) (hb : 1 ≤ beta)
    (hK : ∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M)
    (hf : ∀ a, |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F*beta)
    (a : Fin 3) :
    ‖referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a x‖ ≤ (M+2*F)*beta := by
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hId := norm_id_sub_inverseDegreeMultiplier_le_two hO hD
  have hTerm : ‖referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)‖ ≤ F*beta*2 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf a) hId (norm_nonneg _) (mul_nonneg hF0 hb0)
  unfold referenceWeightedZeroBaseNormalizedCoefficient
  calc
    _ ≤ ‖normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)‖ +
        ‖referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
          (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)‖ := norm_add_le _ _
    _ ≤ M+F*beta*2 := add_le_add (hK a) hTerm
    _ ≤ (M+2*F)*beta := by nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hb)]

lemma norm_referenceCovectorFirstBaseNormalizedCoefficient_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (x : R3) (M F beta : ℝ) (hM : 1 ≤ M) (hF : 1 ≤ F) (hb : 1 ≤ beta)
    (hGamma : ∀ a b j, |referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) j| ≤ M)
    (he : ∀ a j, |referenceMetricGramFrame g L (lam,x) a j| ≤ M)
    (hK : ∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M)
    (hf : ∀ a, |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F*beta)
    (a b j : Fin 3) :
    ‖referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x‖ ≤
      (M+2*M^2+4*F*M)*beta := by
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 ≤ beta := by linarith
  let Ka := normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
  let Kb := normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b)
  let fa := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x
  let fb := referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x
  let ea := referenceMetricGramFrame g L (lam,x) a j
  let eb := referenceMetricGramFrame g L (lam,x) b j
  let Gam := referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
    (referenceMetricGramFrame g L (lam,x) b) j
  let T1 : SphereL2 →L[ℝ] SphereL2 := (-Gam) • inverseDegreeMultiplier hO hD
  let T2 : SphereL2 →L[ℝ] SphereL2 := ea • Kb
  let T3 : SphereL2 →L[ℝ] SphereL2 := eb • Ka
  let T4 : SphereL2 →L[ℝ] SphereL2 := (fb*ea+fa*eb) • (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)
  have h1 : ‖T1‖ ≤ M := by
    dsimp [T1]
    rw [norm_smul,Real.norm_eq_abs,abs_neg]
    exact (mul_le_mul (hGamma a b j) (norm_inverseDegreeMultiplier_le_one hO hD)
      (norm_nonneg _) hM0).trans (by simp)
  have h2 : ‖T2‖ ≤ M^2 := by
    dsimp [T2]
    rw [norm_smul,Real.norm_eq_abs]
    convert mul_le_mul (he a j) (hK b) (norm_nonneg _) hM0 using 1 <;> ring
  have h3 : ‖T3‖ ≤ M^2 := by
    dsimp [T3]
    rw [norm_smul,Real.norm_eq_abs]
    convert mul_le_mul (he b j) (hK a) (norm_nonneg _) hM0 using 1 <;> ring
  have hscalar : |fb*ea+fa*eb| ≤ 2*F*beta*M := by
    have ht1 : |fb*ea| ≤ F*beta*M := by
      rw [abs_mul]
      exact mul_le_mul (hf b) (he a j) (abs_nonneg _) (mul_nonneg hF0 hb0)
    have ht2 : |fa*eb| ≤ F*beta*M := by
      rw [abs_mul]
      exact mul_le_mul (hf a) (he b j) (abs_nonneg _) (mul_nonneg hF0 hb0)
    exact (abs_add_le _ _).trans (by linarith)
  have h4 : ‖T4‖ ≤ 4*F*M*beta := by
    dsimp [T4]
    rw [norm_smul,Real.norm_eq_abs]
    have ht := mul_le_mul hscalar (norm_id_sub_inverseDegreeMultiplier_le_two hO hD)
      (norm_nonneg _) (by positivity : 0 ≤ 2*F*beta*M)
    convert ht using 1 <;> ring
  change ‖T1+T2+T3+T4‖ ≤ (M+2*M^2+4*F*M)*beta
  calc
    _ ≤ ‖T1‖+‖T2‖+‖T3‖+‖T4‖ :=
      calc
        _ ≤ ‖T1+T2+T3‖+‖T4‖ := norm_add_le _ _
        _ ≤ (‖T1+T2‖+‖T3‖)+‖T4‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖T1‖+‖T2‖+‖T3‖+‖T4‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ M+M^2+M^2+4*F*M*beta := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ ≤ (M+2*M^2+4*F*M)*beta := by
      nlinarith [mul_nonneg (show 0 ≤ M+2*M^2 by positivity) (sub_nonneg.mpr hb)]

lemma norm_referenceCovectorZeroBaseNormalizedCoefficient_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (x : R3) (M F beta : ℝ) (hM : 1 ≤ M) (hF : 1 ≤ F) (hb : 1 ≤ beta)
    (hK : ∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M)
    (hDK : ∀ a b, ‖directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b)) x‖ ≤ M)
    (hkappa : ∀ a c b, |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b| ≤ M)
    (hf : ∀ a, |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F*beta)
    (hdf : ∀ a b, |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x| ≤ F*beta^2)
    (a b : Fin 3) :
    ‖referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x‖ ≤
      (M+2*F)*(1+4*M+2*F)*beta^2 := by
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 ≤ beta := by linarith
  have hb2 : beta ≤ beta^2 := by nlinarith
  have hb12 : 1 ≤ beta^2 := by nlinarith
  let Z : ℝ := M+2*F
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  let D := inverseDegreeMultiplier hO hD
  let Kb := directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (fun y => normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) b)) x
  let Ka := normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)
  let fder := directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x
  let fa := referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x
  let Zc := fun c : Fin 3 => referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p c x
  have hZc (c : Fin 3) : ‖Zc c‖ ≤ Z*beta :=
    norm_referenceWeightedZeroBaseNormalizedCoefficient_le hO hD g hg L lam δ R p x M F beta hM hF hb hK hf c
  have hDnorm : ‖D‖ ≤ 1 := norm_inverseDegreeMultiplier_le_one hO hD
  have hZD (c : Fin 3) : ‖(Zc c).comp D‖ ≤ Z*beta := by
    exact ((Zc c).opNorm_comp_le D).trans
      ((mul_le_mul (hZc c) hDnorm (norm_nonneg _) (mul_nonneg hZ0 hb0)).trans (by simp))
  let T1 := Kb.comp D
  let T2 := fder • (D-D.comp D)
  let T3 := Ka.comp (Zc b)
  let T4 := ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
    (referenceMetricGramFrame g L (lam,x) a) c b • (Zc c).comp D
  let T5 := fa • (Zc b-(Zc b).comp D)
  have h1 : ‖T1‖ ≤ M := by
    exact (Kb.opNorm_comp_le D).trans
      ((mul_le_mul (hDK a b) hDnorm (norm_nonneg _) hM0).trans (by simp))
  have h2 : ‖T2‖ ≤ 2*F*beta^2 := by
    dsimp [T2]
    rw [norm_smul,Real.norm_eq_abs]
    have ht := mul_le_mul (hdf a b) (norm_inverseDegreeMultiplier_sub_square_le_two hO hD)
      (norm_nonneg _) (mul_nonneg hF0 (sq_nonneg beta))
    convert ht using 1 <;> ring
  have h3 : ‖T3‖ ≤ M*Z*beta := by
    have ht := (Ka.opNorm_comp_le (Zc b)).trans
      (mul_le_mul (hK a) (hZc b) (norm_nonneg _) hM0)
    convert ht using 1 <;> ring
  have h4 : ‖T4‖ ≤ 3*M*Z*beta := by
    have hterm (c : Fin 3) : ‖referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) c b • (Zc c).comp D‖ ≤ M*Z*beta := by
      rw [norm_smul,Real.norm_eq_abs]
      convert mul_le_mul (hkappa a c b) (hZD c) (norm_nonneg _) hM0 using 1 <;> ring
    have ht : ‖T4‖ ≤ ∑ c : Fin 3, M*Z*beta :=
      (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun c _ => hterm c)
    simp only [Fin.sum_univ_three] at ht
    convert ht using 1 <;> ring
  have hdiff : ‖Zc b-(Zc b).comp D‖ ≤ 2*Z*beta := by
    exact (norm_sub_le _ _).trans (by linarith [hZc b,hZD b])
  have h5 : ‖T5‖ ≤ 2*F*Z*beta^2 := by
    dsimp [T5]
    rw [norm_smul,Real.norm_eq_abs]
    have ht := mul_le_mul (hf a) hdiff (norm_nonneg _) (mul_nonneg hF0 hb0)
    convert ht using 1 <;> ring
  change ‖T1+T2+T3-T4+T5‖ ≤ (M+2*F)*(1+4*M+2*F)*beta^2
  calc
    _ ≤ ‖T1‖+‖T2‖+‖T3‖+‖T4‖+‖T5‖ :=
      calc
        _ ≤ ‖T1+T2+T3-T4‖+‖T5‖ := norm_add_le _ _
        _ ≤ (‖T1+T2+T3‖+‖T4‖)+‖T5‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ ((‖T1+T2‖+‖T3‖)+‖T4‖)+‖T5‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
        _ ≤ ‖T1‖+‖T2‖+‖T3‖+‖T4‖+‖T5‖ :=
          add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ M+2*F*beta^2+M*Z*beta+3*M*Z*beta+2*F*Z*beta^2 :=
      add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    _ ≤ (M+2*F)*(1+4*M+2*F)*beta^2 := by
      have hMscale := mul_le_mul_of_nonneg_left hb12 hM0
      have hZscale := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 4*M*Z by positivity)
      dsimp [Z] at *
      nlinarith

lemma norm_referenceWeightedFirstBaseNormalizedCoefficient_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (x : R3) (M F beta : ℝ) (hM : 1 ≤ M) (hF : 1 ≤ F) (hb : 1 ≤ beta)
    (h : MatrixField) (Q : ℝ) (hQ : 0 ≤ Q)
    (hcQ : ∀ a b, |physicalMixedQFrameCoefficient g L lam h a b x| ≤ Q)
    (hGamma : ∀ a b j, |referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) j| ≤ M)
    (he : ∀ a j, |referenceMetricGramFrame g L (lam,x) a j| ≤ M)
    (hK : ∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M)
    (hf : ∀ a, |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F*beta)
    (j : Fin 3) :
    ‖referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x‖ ≤
      9*Q*(M+2*M^2+4*F*M)*referenceRadius δ R p L x*beta := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 ≤ beta := by linarith
  let C : ℝ := (M+2*M^2+4*F*M)*beta
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hterm (a b : Fin 3) : ‖physicalMixedQFrameCoefficient g L lam h a b x •
      referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x‖ ≤ Q*C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hcQ a b)
      (norm_referenceCovectorFirstBaseNormalizedCoefficient_le hO hD g hg L lam δ R p x M F beta hM hF hb hGamma he hK hf a b j)
      (norm_nonneg _) hQ
  have hsum : ‖∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x •
      referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x‖ ≤ 9*Q*C := by
    have ht : ‖∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x •
        referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x‖ ≤
        ∑ a : Fin 3, ∑ b : Fin 3, Q*C :=
      (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun b _ => hterm a b))
    have hcount : (∑ a : Fin 3, ∑ b : Fin 3, Q*C) = 9*Q*C := by
      simp only [Fin.sum_univ_three]
      ring
    exact ht.trans (le_of_eq hcount)
  rw [referenceWeightedFirstBaseNormalizedCoefficient_eq_sum hO hD g hg L lam δ R p h j x,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have ht := mul_le_mul_of_nonneg_left hsum hr.le
  convert ht using 1 <;> dsimp [C] <;> ring

lemma norm_referenceWeightedZeroBaseNormalizedCoefficientTrace_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (x : R3) (M F beta : ℝ) (hM : 1 ≤ M) (hF : 1 ≤ F) (hb : 1 ≤ beta)
    (h : MatrixField) (Q : ℝ) (hQ : 0 ≤ Q)
    (hcQ : ∀ a b, |physicalMixedQFrameCoefficient g L lam h a b x| ≤ Q)
    (hK : ∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M)
    (hDK : ∀ a b, ‖directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b)) x‖ ≤ M)
    (hkappa : ∀ a c b, |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) c b| ≤ M)
    (hf : ∀ a, |referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F*beta)
    (hdf : ∀ a b, |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x| ≤ F*beta^2) :
    ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x‖ ≤
      9*Q*(M+2*F)*(1+4*M+2*F)*referenceRadius δ R p L x*beta^2 := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hb0 : 0 ≤ beta := by linarith
  let C : ℝ := (M+2*F)*(1+4*M+2*F)*beta^2
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hterm (a b : Fin 3) : ‖physicalMixedQFrameCoefficient g L lam h a b x •
      referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x‖ ≤ Q*C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hcQ a b)
      (norm_referenceCovectorZeroBaseNormalizedCoefficient_le hO hD g hg L lam δ R p x M F beta hM hF hb hK hDK hkappa hf hdf a b)
      (norm_nonneg _) hQ
  have hsum : ‖∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x •
      referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x‖ ≤ 9*Q*C := by
    have ht : ‖∑ a : Fin 3, ∑ b : Fin 3, physicalMixedQFrameCoefficient g L lam h a b x •
        referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x‖ ≤
        ∑ a : Fin 3, ∑ b : Fin 3, Q*C :=
      (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun b _ => hterm a b))
    have hcount : (∑ a : Fin 3, ∑ b : Fin 3, Q*C) = 9*Q*C := by
      simp only [Fin.sum_univ_three]
      ring
    exact ht.trans (le_of_eq hcount)
  unfold referenceWeightedZeroBaseNormalizedCoefficientTrace
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have ht := mul_le_mul_of_nonneg_left hsum hr.le
  convert ht using 1 <;> dsimp [C] <;> ring

theorem exists_referenceDD_normalized_coefficient_smallness
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ Cfirst Czero : ℝ, 0 < Cfirst ∧ 0 < Czero ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, |h x i j| ≤ eps*referenceRadius δ R p L x) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
      (∀ j, ‖referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x‖ ≤ Cfirst*eps/beta) ∧
      ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x‖ ≤ Czero*eps := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_bounds hO hD g hg L K hK
  obtain ⟨F,hF,hprofile⟩ := exists_referenceDD_logRadius_frame_uniform_bounds hO hD g hg L hL K hK
  let Q : ℝ := 1+9*M^2
  let Cfirst : ℝ := 9*Q*(M+2*M^2+4*F*M)
  let Czero : ℝ := 9*Q*(M+2*F)*(1+4*M+2*F)
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hCfirst : 0 < Cfirst := by dsimp [Cfirst,Q]; positivity
  have hCzero : 0 < Czero := by dsimp [Czero,Q]; positivity
  refine ⟨Cfirst,Czero,hCfirst,hCzero,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh beta hb hsmall
  have hG := hgeom lam hlam x hx
  have hP := hprofile lam hlam δ hδ hδ1 R hR p hp x hx hb
  have hh1 := weighted_h_zero_le_one δ R L p x hδ hR beta eps hb heps1 hsmall h hh
  have hcQ (a b : Fin 3) : |physicalMixedQFrameCoefficient g L lam h a b x| ≤ Q :=
    physicalMixedQFrameCoefficient_bound g hg L lam h x M hM0 hG.2.2.2.2.2.2.1 hh1 a b
  have hrb := referenceRadius_mul_beta_le_eps_div δ R L p x hδ hR beta eps hb hsmall
  have hGamma := hG.2.2.1
  have he := hG.2.2.2.2.2.2.2
  have hKa := hG.2.2.2.1
  have hDK := hG.2.2.2.2.1
  have hkappa := hG.2.2.2.2.2.1
  refine ⟨?_,?_⟩
  · intro j
    have ht := norm_referenceWeightedFirstBaseNormalizedCoefficient_le hO hD g hg L lam δ R p hδ hR x M F beta hM hF hb h Q hQ0 hcQ hGamma he hKa hP.1 j
    have hw := mul_le_mul_of_nonneg_left hrb hCfirst.le
    calc
      _ ≤ Cfirst*(referenceRadius δ R p L x*beta) := by convert ht using 1 <;> dsimp [Cfirst] <;> ring
      _ ≤ Cfirst*(eps/beta) := hw
      _ = Cfirst*eps/beta := by ring
  · have ht := norm_referenceWeightedZeroBaseNormalizedCoefficientTrace_le hO hD g hg L lam δ R p hδ hR x M F beta hM hF hb h Q hQ0 hcQ hKa hDK hkappa hP.1 hP.2
    calc
      _ ≤ Czero*(referenceRadius δ R p L x*beta^2) := by convert ht using 1 <;> dsimp [Czero] <;> ring
      _ ≤ Czero*eps := mul_le_mul_of_nonneg_left hsmall hCzero.le

end OAI.AnisotropicCalderon.ActualReferenceDDCoefficientSmallness
