import Calderon.FiniteTensorRealization

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.IntegratedFischerIdentities
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew CurvatureRotation SphereHarmonic
  MovingFrameConnection FischerConnectionTransport WeightedFischerSquare
  SmoothMetricFrame FrameCurvaturePolynomial FiniteCovariantCurvature
  PolynomialSlotCompatibility FullCovectorCurvature IndexedCovariantCurvature
  ContractedFischerAdjunction WeightedIndexedCurvature ScalarContractedAdjunction
  FiniteTensorRealization FischerCovectorAdjunction FischerDensityIntegration ReferenceDensityBounds

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative
  finitePolynomialField finitePolynomialFieldDerivative referenceFrameAngularPolynomial
  referenceCovariantPolynomialDerivative

variable {ι : Type*} [Fintype ι]

def referenceLoweredWeightedTensorPolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ) :
    (Fin 3 × ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι)) → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun a i j => pderiv j (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)

def referenceLoweredWeightedTensorCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) :
    R3 → (Fin 3 × ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι)) → ℝ :=
  indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)

def referenceLoweredWeightedTensorField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) (i j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceWeightedCovectorPolynomialDerivative g L lam (fun a h => pderiv h (b a)) c f k t x
    (referenceMetricGramFrame g L (lam,x) i) j

lemma referenceLoweredWeightedTensorField_eq_finite (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) (i j : Fin 3) :
    referenceLoweredWeightedTensorField g L lam b c f k t x i j =
      finitePolynomialField (fun a => referenceLoweredWeightedTensorPolynomialFamily b a i j)
        (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) x :=
  (finitePolynomialField_referenceWeighted_lowered g L lam b c f k t x i j).symm

lemma contDiff_referenceLoweredWeightedTensorCoefficientFamily (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) :=
  contDiff_indexedCoefficientFamily _ (contDiff_pi.mp
    (contDiff_referenceWeightedIndexedCoefficientFamily g hg L lam c f k t hc hf))

lemma hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily (g : MatrixField)
    (L lam : ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) (hc : HasCompactSupport c) :
    HasCompactSupport (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) :=
  hasCompactSupport_indexedCoefficientFamily _
    (hasCompactSupport_referenceWeightedIndexedCoefficientFamily g L lam c f k t hc)

def referenceLoweredWeightedTraceField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, referenceLoweredWeightedTensorField g L lam b c f k t x i i

lemma referenceLoweredWeightedTraceField_eq_finite (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) :
    referenceLoweredWeightedTraceField g L lam b c f k t x =
      finitePolynomialField (referenceWeightedTracePolynomialFamily b)
        (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) x :=
  (finitePolynomialField_referenceWeighted_trace g L lam b c f k t x).symm

def referenceLoweredWeightedCrossEnergy (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
    fischerInner (referenceLoweredWeightedTensorField g L lam b c f k t x i j)
      (referenceLoweredWeightedTensorField g L lam b c f k t x j i)

def referenceLoweredWeightedTraceSquare (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    fischerInner (referenceLoweredWeightedTraceField g L lam b c f k t x)
      (referenceLoweredWeightedTraceField g L lam b c f k t x)

def referenceFrameHessianCoefficient (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (x : R3) (i j : Fin 3) : ℝ :=
  coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
    (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j)

def referenceLoweredHessianEnergy (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
    (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))

def referenceIntegratedFullCovectorCurvature (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
      (finitePolynomialField b c x)

lemma contDiff_referenceFrameHessianCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceFrameHessianCoefficient g L lam f x i j) := by
  have he (a : Fin 3) := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hG : ContDiff ℝ ∞ (fun x => referenceConnectionFamily g L (lam,x)) :=
    (contDiff_referenceConnectionFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hdd := hd.fderiv_right (m := ∞) (by simp)
  exact ((hdd.clm_apply (he i)).clm_apply (he j)).sub
    (hd.clm_apply ((hG.clm_apply (he i)).clm_apply (he j)))

lemma contDiff_referenceCurvatureAction_apply_frame (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceCurvatureAction g L lam x
      (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j)
      (referenceMetricGramFrame g L (lam,x) l)) := by
  have he (a : Fin 3) := contDiff_referenceMetricGramFrame_slice g hg L lam a
  have hG : ContDiff ℝ ∞ (fun x => referenceConnectionFamily g L (lam,x)) :=
    (contDiff_referenceConnectionFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hDG : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => referenceConnectionFamily g L (lam,y)) x) :=
    (contDiff_referenceConnection_spatial_fderiv g hg L).comp (contDiff_const.prodMk contDiff_id)
  have h := (((hDG.clm_apply (he i)).clm_apply (he j)).clm_apply (he l)).sub
    (((hDG.clm_apply (he j)).clm_apply (he i)).clm_apply (he l))
  have hp := ((hG.clm_apply (he i)).clm_apply ((hG.clm_apply (he j)).clm_apply (he l)))
  have hm := ((hG.clm_apply (he j)).clm_apply ((hG.clm_apply (he i)).clm_apply (he l)))
  simpa only [referenceCurvatureAction,coordinateCurvatureAction_apply] using (h.add hp).sub hm

lemma contDiff_referenceCurvatureRotationCoefficient_frame (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (i j a l : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceCurvatureRotationCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x)) i j a l) := by
  have hM : ContDiff ℝ ∞ (fun x => metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) :=
    (contDiff_referenceMetricOperator_joint g hg L).comp (contDiff_const.prodMk contDiff_id)
  exact (hM.clm_apply (contDiff_referenceCurvatureAction_apply_frame g hg L lam i j l)).inner ℝ
    (contDiff_referenceMetricGramFrame_slice g hg L lam a)

lemma fischerInner_referenceCovectorCurvature_eq (g : MatrixField) (L lam : ℝ)
    (x : R3) (e : Fin 3 → R3) (i j l : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (W : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    fischerInner p (referenceCovectorCurvaturePolynomial g L lam x e i j W l) =
      -(∑ a : Fin 3, ∑ t : Fin 3, referenceCurvatureRotationCoefficient g L lam x e i j a t *
        fischerInner p (X t*pderiv a (W l))) -
      ∑ a : Fin 3, referenceCurvatureRotationCoefficient g L lam x e i j a l * fischerInner p (W a) := by
  simp only [referenceCovectorCurvaturePolynomial,referenceHorizontalCurvaturePolynomial,
    referenceCurvatureVectorFieldPolynomial,polynomialMatrixVectorField,
    mul_assoc, fischerInner_sub_right,fischerInner_neg_right,fischerInner_sum_right,fischerInner_C_mul_right]

variable {κ : Type*} [Fintype κ]

lemma integrable_referenceDensity_fischerPair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  exact (hr.continuous.mul (contDiff_fischerPair b d c z hc hz).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_fischerPair b d c z hcompact).mul_left

lemma integrable_referenceLoweredWeightedTensor_pair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s t : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c)
    (i j a l : Fin 3) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      fischerInner (referenceLoweredWeightedTensorField g L lam b c f k s x i j)
        (referenceLoweredWeightedTensorField g L lam b c f k t x a l)) := by
  simp_rw [referenceLoweredWeightedTensorField_eq_finite]
  exact integrable_referenceDensity_fischerPair g hg L lam _ _ _ _
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k s hc hf)
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf)
    (hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily g L lam c f k s hcompact)

lemma integrable_referenceLoweredWeightedTrace_square (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      fischerInner (referenceLoweredWeightedTraceField g L lam b c f k t x)
        (referenceLoweredWeightedTraceField g L lam b c f k t x)) := by
  simp_rw [referenceLoweredWeightedTraceField_eq_finite]
  exact integrable_referenceDensity_fischerPair g hg L lam _ _ _ _
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf)
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf)
    (hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t hcompact)

lemma integrable_referenceLoweredHessian_pair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c)
    (i j : Fin 3) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ((2*k*referenceFrameHessianCoefficient g L lam f x i j) *
        fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x)))) := by
  simp_rw [← finitePolynomialField_partial]
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hH := (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => 2*k)).mul
    (contDiff_referenceFrameHessianCoefficient g hg L lam f hf i j)
  exact (hr.continuous.mul (hH.continuous.mul (contDiff_fischerPair _ _ c c hc hc).continuous)).integrable_of_hasCompactSupport
    (hasCompactSupport_fischerPair _ _ c c hcompact).mul_left.mul_left

lemma contDiff_fischerInner_referenceCovectorCurvature_pair (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x)
      (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
        (fun a => finitePolynomialField (fun r => d r a) z x) l)) := by
  simp_rw [fischerInner_referenceCovectorCurvature_eq,← finitePolynomialField_partial,
    ← finitePolynomialField_multiplication]
  apply (ContDiff.sum (fun a _ => ContDiff.sum (fun t _ =>
    (contDiff_referenceCurvatureRotationCoefficient_frame g hg L lam i j a t).mul
      (contDiff_fischerPair _ _ c z hc hz)))).neg.sub
  exact ContDiff.sum (fun a _ =>
    (contDiff_referenceCurvatureRotationCoefficient_frame g hg L lam i j a l).mul
      (contDiff_fischerPair _ _ c z hc hz))

lemma integrable_referenceCovectorCurvature_pair (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hcompact : HasCompactSupport c) (i j l : Fin 3) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * fischerInner (finitePolynomialField b c x)
      (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
        (fun a => finitePolynomialField (fun r => d r a) z x) l)) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  apply (hr.continuous.mul
    (contDiff_fischerInner_referenceCovectorCurvature_pair g hg L lam b d c z hc hz i j l).continuous).integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  apply hcompact.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  rw [finitePolynomialField_eq_zero_of_coeff_eq_zero b c x hzero,fischerInner_zero_left]

lemma integrable_referenceWeightedTensorPolynomialDerivative_fischer_right (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) (i j : Fin 3) : Integrable (fun x => rho x * fischerInner
      (finitePolynomialField b c x) (referenceWeightedTensorPolynomialDerivative g L lam d z f k s x (V x) i j)) := by
  have hA := (integrable_referenceTensorPolynomialDerivative_fischer_right g hg L lam rho hr V hV b d c z hc hz hcompact i j).const_mul s
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).clm_apply hV
  have hw := (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => k)).mul hdf
  have hB : Integrable (fun x => rho x * ((k*fderiv ℝ f x (V x)) *
      fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i j) z x))) :=
    (hr.mul (hw.continuous.mul (contDiff_fischerPair _ _ c z hc hz).continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_fischerPair _ _ c z hcompact).mul_left.mul_left
  convert hA.add hB using 1
  funext x
  simp only [Pi.add_apply,referenceWeightedTensorPolynomialDerivative,fischerInner_add_right,fischerInner_C_mul_right]
  ring

def referenceLoweredWeightedSecondTensorField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s t : ℝ) (x : R3) (i j l : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceWeightedTensorPolynomialDerivative g L lam (referenceLoweredWeightedTensorPolynomialFamily b)
    (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) f k s x
    (referenceMetricGramFrame g L (lam,x) i) j l

lemma referenceLoweredWeightedSecondTensorField_eq_indexed (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j l : Fin 3) :
    referenceLoweredWeightedSecondTensorField g L lam b c f k s t x i j l =
      referenceWeightedLoweredCovectorIndexedHessian g L lam b c f k s t x i j l :=
  referenceWeightedTensorPolynomialDerivative_referenceWeighted_lowered g hg L lam b c f k s t hc hf x i j l

lemma referenceLoweredWeightedSecondTensorField_trace (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s t : ℝ) (x : R3) (j : Fin 3) :
    (∑ i : Fin 3, referenceLoweredWeightedSecondTensorField g L lam b c f k s t x j i i) =
      referenceWeightedPolynomialDerivative g L lam (referenceWeightedTracePolynomialFamily b)
        (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) f k s x
        (referenceMetricGramFrame g L (lam,x) j) :=
  (referenceWeightedPolynomialDerivative_tensorTrace g hg L lam
    (referenceLoweredWeightedTensorPolynomialFamily b)
    (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) f k s x
    (referenceMetricGramFrame g L (lam,x) j)).symm

lemma referenceLoweredWeightedSecondTensorField_mixed_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j l : Fin 3) :
    referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x j i l -
      referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j l =
    referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (fun a => pderiv a (finitePolynomialField b c x)) l -
    C (2*k*referenceFrameHessianCoefficient g L lam f x i j) * pderiv l (finitePolynomialField b c x) := by
  simp_rw [referenceLoweredWeightedSecondTensorField_eq_indexed g hg L lam b c f k _ _ hc hf]
  exact referenceWeightedLoweredCovectorIndexedHessian_mixed_commutator g hg L lam b c f k hc hf x i j l

lemma integrable_referenceLoweredWeightedSecondTensor_pair (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c)
    (a i j l : Fin 3) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      fischerInner (pderiv a (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k s t x i j l)) := by
  simp_rw [referenceLoweredWeightedSecondTensorField,← finitePolynomialField_partial]
  have hr := ((contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id) : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)))
  exact integrable_referenceWeightedTensorPolynomialDerivative_fischer_right g hg L lam _ hr.continuous
    _ (contDiff_referenceMetricGramFrame_slice g hg L lam i) _ _ c _ f k s hc
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf) hf hcompact j l

lemma referenceCovectorCurvaturePolynomial_partial_antisymm (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x : R3) (i j l : Fin 3) :
    referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) j i
      (fun a => pderiv a (finitePolynomialField b c x)) l =
    -referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (fun a => pderiv a (finitePolynomialField b c x)) l := by
  rw [← referenceLoweredCovectorIndexedHessian_antisymm g hg L lam b c hc x i j l,
    ← referenceLoweredCovectorIndexedHessian_antisymm g hg L lam b c hc x j i l]
  abel

theorem referenceLoweredWeightedCrossEnergy_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedCrossEnergy g L lam b c f k t =
    ∫ x : R3, referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-t) t x i j i) := by
  have h := compact_reference_contracted_weighted_tensor_fischer_adjoint g hg L lam
    (fun a j => pderiv j (b a))
    (fun a i j => referenceLoweredWeightedTensorPolynomialFamily b a j i)
    c (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) f k t hc
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf) hf hcompact
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with x
    simp_rw [← referenceLoweredWeightedTensorField_eq_finite]
    rfl
  · apply integral_congr_ae
    filter_upwards [] with x
    simp_rw [referenceWeightedTensorPolynomialDerivative_transpose,finitePolynomialField_partial]
    rfl

theorem referenceLoweredWeightedTraceSquare_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedTraceSquare g L lam b c f k t =
    ∫ x : R3, referenceDensityFamily g L (lam,x) * ∑ j : Fin 3, ∑ i : Fin 3,
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-t) t x j i i) := by
  have h := compact_reference_contracted_weighted_covector_fischer_adjoint g hg L lam
    (referenceWeightedTracePolynomialFamily b) (fun a j => pderiv j (b a))
    (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) c f k (-t)
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f k t hc hf) hc hf
    (hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t hcompact)
  have hr : (∫ x : R3, referenceDensityFamily g L (lam,x) * ∑ j : Fin 3, fischerInner
      (finitePolynomialField (referenceWeightedTracePolynomialFamily b)
        (referenceLoweredWeightedTensorCoefficientFamily g L lam c f k t) x)
      (referenceWeightedCovectorPolynomialDerivative g L lam (fun a j => pderiv j (b a)) c f k (- -t) x
        (referenceMetricGramFrame g L (lam,x) j) j)) =
      referenceLoweredWeightedTraceSquare g L lam b c f k t := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [neg_neg,← referenceLoweredWeightedTraceField_eq_finite,
      referenceLoweredWeightedTraceField,referenceLoweredWeightedTensorField,← fischerInner_sum_right]
  rw [hr] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [← fischerInner_sum_right,referenceLoweredWeightedSecondTensorField_trace g hg L lam b c f k (-t) t,
    finitePolynomialField_partial,fischerInner_symm]

lemma integrable_referenceLoweredHessian (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
      (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
        fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))) := by
  simp only [Finset.mul_sum]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    integrable_referenceLoweredHessian_pair g hg L lam b c f k hc hf hcompact i j))

lemma integrable_referenceFullCovectorCurvature (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
        (finitePolynomialField b c x)) := by
  simp only [referenceFullCovectorCurvatureContraction,Finset.mul_sum]
  apply integrable_finset_sum; intro i hi
  apply integrable_finset_sum; intro j hj
  simp_rw [← finitePolynomialField_partial]
  exact integrable_referenceCovectorCurvature_pair g hg L lam _ _ c c hc hc hcompact i j j

lemma referenceLoweredWeighted_mixed_first_pointwise (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x i j i)) =
    (∑ j : Fin 3, ∑ i : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x j i i)) -
    (∑ i : Fin 3, ∑ j : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))) +
    referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
      (finitePolynomialField b c x) := by
  have h (i j : Fin 3) := congrArg (fischerInner (pderiv j (finitePolynomialField b c x)))
    (referenceLoweredWeightedSecondTensorField_mixed_commutator g hg L lam b c f k hc hf x j i i)
  simp only [fischerInner_sub_right,fischerInner_C_mul_right] at h
  have hp (i j : Fin 3) :
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x i j i) =
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x j i i) -
      (2*k*referenceFrameHessianCoefficient g L lam f x j i) *
        fischerInner (pderiv j (finitePolynomialField b c x)) (pderiv i (finitePolynomialField b c x)) +
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) j i
          (fun a => pderiv a (finitePolynomialField b c x)) i) := by linarith [h i j]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,referenceFullCovectorCurvatureContraction]
  have hA : (∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x j i i)) =
      ∑ j : Fin 3, ∑ i : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x j i i) := Finset.sum_comm
  have hH : (∑ i : Fin 3, ∑ j : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x j i) *
      fischerInner (pderiv j (finitePolynomialField b c x)) (pderiv i (finitePolynomialField b c x))) =
      ∑ i : Fin 3, ∑ j : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
        fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x)) := Finset.sum_comm
  have hE : (∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) j i
        (fun a => pderiv a (finitePolynomialField b c x)) i)) =
      ∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv i (finitePolynomialField b c x))
        (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
          (fun a => pderiv a (finitePolynomialField b c x)) j) := Finset.sum_comm
  rw [hA,hH,hE]

lemma referenceLoweredWeighted_mixed_second_pointwise (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) :
    (∑ j : Fin 3, ∑ i : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x j i i)) =
    (∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j i)) -
    (∑ i : Fin 3, ∑ j : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))) -
    referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
      (finitePolynomialField b c x) := by
  have h (i j : Fin 3) := congrArg (fischerInner (pderiv j (finitePolynomialField b c x)))
    (referenceLoweredWeightedSecondTensorField_mixed_commutator g hg L lam b c f k hc hf x i j i)
  simp only [fischerInner_sub_right,fischerInner_C_mul_right] at h
  have hp (j i : Fin 3) :
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x j i i) =
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j i) -
      (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
        fischerInner (pderiv j (finitePolynomialField b c x)) (pderiv i (finitePolynomialField b c x)) -
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) j i
          (fun a => pderiv a (finitePolynomialField b c x)) i) := by
    rw [referenceCovectorCurvaturePolynomial_partial_antisymm g hg L lam b c hc x i j i,
      fischerInner_neg_right]
    linarith [h i j]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib,referenceFullCovectorCurvatureContraction]
  have hA : (∑ j : Fin 3, ∑ i : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j i)) =
      ∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j i) := Finset.sum_comm
  have hH : (∑ j : Fin 3, ∑ i : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv j (finitePolynomialField b c x)) (pderiv i (finitePolynomialField b c x))) =
      ∑ i : Fin 3, ∑ j : Fin 3, (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
        fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    rw [fischerInner_symm]
  rw [hA,hH]


theorem referenceLoweredWeighted_first_integrated_identity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedCrossEnergy g L lam b c f k 1 =
      referenceLoweredWeightedTraceSquare g L lam b c f k (-1) -
      referenceLoweredHessianEnergy g L lam b c f k + referenceIntegratedFullCovectorCurvature g L lam b c := by
  let B : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) * ∑ j : Fin 3, ∑ i : Fin 3,
    fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x j i i)
  let H : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
    (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))
  let E : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) *
    referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
      (finitePolynomialField b c x)
  have hB : Integrable B := by
    simp only [B,Finset.mul_sum]
    exact integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun i _ =>
      integrable_referenceLoweredWeightedSecondTensor_pair g hg L lam b c f k 1 (-1) hc hf hcompact j j i i))
  have hH : Integrable H := integrable_referenceLoweredHessian g hg L lam b c f k hc hf hcompact
  have hE : Integrable E := integrable_referenceFullCovectorCurvature g hg L lam b c hc hcompact
  have ht := referenceLoweredWeightedTraceSquare_adjoint g hg L lam b c f k (-1) hc hf hcompact
  simp only [neg_neg] at ht
  rw [referenceLoweredWeightedCrossEnergy_adjoint g hg L lam b c f k 1 hc hf hcompact,ht]
  change (∫ x : R3, referenceDensityFamily g L (lam,x) * _) = (∫ x, B x) - (∫ x, H x) + ∫ x, E x
  have hp : (fun x : R3 => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x i j i)) =
      fun x => (B x-H x)+E x := by
    funext x
    rw [referenceLoweredWeighted_mixed_first_pointwise g hg L lam b c f k hc hf]
    dsimp only [B,H,E]
    ring
  rw [hp]
  change (∫ x : R3, (B-H) x+E x) = _
  rw [integral_add (hB.sub hH) hE]
  change (∫ x : R3, B x-H x)+(∫ x : R3, E x) = _
  rw [integral_sub hB hH]

theorem referenceLoweredWeighted_second_integrated_identity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedTraceSquare g L lam b c f k 1 =
      referenceLoweredWeightedCrossEnergy g L lam b c f k (-1) -
      referenceLoweredHessianEnergy g L lam b c f k - referenceIntegratedFullCovectorCurvature g L lam b c := by
  let B : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
    fischerInner (pderiv j (finitePolynomialField b c x))
      (referenceLoweredWeightedSecondTensorField g L lam b c f k 1 (-1) x i j i)
  let H : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
    (2*k*referenceFrameHessianCoefficient g L lam f x i j) *
      fischerInner (pderiv i (finitePolynomialField b c x)) (pderiv j (finitePolynomialField b c x))
  let E : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x) *
    referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x))
      (finitePolynomialField b c x)
  have hB : Integrable B := by
    simp only [B,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceLoweredWeightedSecondTensor_pair g hg L lam b c f k 1 (-1) hc hf hcompact j i j i))
  have hH : Integrable H := integrable_referenceLoweredHessian g hg L lam b c f k hc hf hcompact
  have hE : Integrable E := integrable_referenceFullCovectorCurvature g hg L lam b c hc hcompact
  have ht := referenceLoweredWeightedCrossEnergy_adjoint g hg L lam b c f k (-1) hc hf hcompact
  simp only [neg_neg] at ht
  rw [referenceLoweredWeightedTraceSquare_adjoint g hg L lam b c f k 1 hc hf hcompact,ht]
  change (∫ x : R3, referenceDensityFamily g L (lam,x) * _) = (∫ x, B x) - (∫ x, H x) - ∫ x, E x
  have hp : (fun x : R3 => referenceDensityFamily g L (lam,x) * ∑ j : Fin 3, ∑ i : Fin 3,
      fischerInner (pderiv j (finitePolynomialField b c x))
        (referenceLoweredWeightedSecondTensorField g L lam b c f k (-1) 1 x j i i)) =
      fun x => (B x-H x)-E x := by
    funext x
    rw [referenceLoweredWeighted_mixed_second_pointwise g hg L lam b c f k hc hf]
    dsimp only [B,H,E]
    ring
  rw [hp]
  change (∫ x : R3, (B-H) x-E x) = _
  rw [integral_sub (hB.sub hH) hE]
  change (∫ x : R3, B x-H x)-(∫ x : R3, E x) = _
  rw [integral_sub hB hH]

lemma referenceWeightedPolynomialDerivative_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (s : ℝ) (x V : R3) :
    referenceWeightedPolynomialDerivative g L lam b c f k s x V ∈ harmonicHomogeneous k := by
  simpa only [referenceWeightedPolynomialDerivative,smul_eq_C_mul] using
    (harmonicHomogeneous k).add_mem
      ((harmonicHomogeneous k).smul_mem s
        (referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c x V))
      ((harmonicHomogeneous k).smul_mem ((k:ℝ)*fderiv ℝ f x V)
        (finitePolynomialField_harmonicHomogeneous k b hb c x))

lemma referenceLoweredWeightedCrossEnergy_pointwise_le (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (t : ℝ) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (referenceLoweredWeightedTensorField g L lam b c f k t x i j)
        (referenceLoweredWeightedTensorField g L lam b c f k t x j i)) ≤
    (k:ℝ)*referenceWeightedFrameEnergy g L lam b c f k t x := by
  simp only [referenceLoweredWeightedTensorField,referenceWeightedCovectorPolynomialDerivative_partial,
    referenceWeightedFrameEnergy]
  exact sum_fischerInner_pderiv_cross_le _ (fun i =>
    (referenceWeightedPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c f t x
      (referenceMetricGramFrame g L (lam,x) i)).1)

theorem referenceLoweredWeightedCrossEnergy_le (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedCrossEnergy g L lam b c f k t ≤
      (k:ℝ)*(∫ x : R3, referenceDensityFamily g L (lam,x) * referenceWeightedFrameEnergy g L lam b c f k t x) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hA : Integrable (fun x => referenceDensityFamily g L (lam,x) * ∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (referenceLoweredWeightedTensorField g L lam b c f k t x i j)
        (referenceLoweredWeightedTensorField g L lam b c f k t x j i)) := by
    simp only [Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceLoweredWeightedTensor_pair g hg L lam b c f k t t hc hf hcompact i j j i))
  have hB := integrable_referenceWeightedFrameEnergy g hg L lam _ hr.continuous b c f k t hc hf hcompact
  calc
    _ ≤ ∫ x : R3, (k:ℝ)*(referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f k t x) := by
      apply integral_mono hA (hB.const_mul (k:ℝ))
      intro x
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*((k:ℝ)*referenceWeightedFrameEnergy g L lam b c f k t x) :=
          mul_le_mul_of_nonneg_left (referenceLoweredWeightedCrossEnergy_pointwise_le g hg L lam k hk b hb c f t x)
            (referenceDensityFamily_pos g hg L (lam,x)).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

theorem referenceLoweredWeighted_second_integrated_inequality (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedTraceSquare g L lam b c f k 1 ≤
      (k:ℝ)*(∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f k (-1) x) -
      referenceLoweredHessianEnergy g L lam b c f k - referenceIntegratedFullCovectorCurvature g L lam b c := by
  rw [referenceLoweredWeighted_second_integrated_identity g hg L lam b c f k hc hf hcompact]
  exact sub_le_sub_right (sub_le_sub_right
    (referenceLoweredWeightedCrossEnergy_le g hg L lam k hk b hb c f (-1) hc hf hcompact) _) _

lemma referenceFullCovectorCurvatureContraction_zero (g : MatrixField) (L lam : ℝ)
    (x : R3) (e : Fin 3 → R3) :
    referenceFullCovectorCurvatureContraction g L lam x e 0 = 0 := by
  simp [referenceFullCovectorCurvatureContraction,referenceCovectorCurvaturePolynomial,
    referenceHorizontalCurvaturePolynomial,referenceCurvatureVectorFieldPolynomial,polynomialMatrixVectorField,fischerInner_zero_left]

theorem exists_referenceIntegratedFullCovectorCurvature_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ hF : SphereFischerInner, ∀ lam ∈ Set.Icc (0:ℝ) 1,
      ∀ k : ℕ, 1 ≤ k → ∀ b : ι → MvPolynomial (Fin 3) ℝ,
      (∀ a, b a ∈ harmonicHomogeneous k) → ∀ c : R3 → ι → ℝ,
      ContDiff ℝ ∞ c → HasCompactSupport c → (∀ x ∉ K, finitePolynomialField b c x = 0) →
      |referenceIntegratedFullCovectorCurvature g L lam b c| ≤
        A*(k:ℝ)^2*(∫ x : R3, referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  obtain ⟨A,hA,hbound⟩ := exists_referenceFullCovectorCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  refine ⟨A,hA,?_⟩
  intro hF lam hlam k hk b hb c hc hcompact hzero
  have hE := integrable_referenceFullCovectorCurvature g hg L lam b c hc hcompact
  have hU := integrable_referenceDensity_fischerPair g hg L lam b b c c hc hc hcompact
  have hp (x : R3) : |referenceDensityFamily g L (lam,x)*
      referenceFullCovectorCurvatureContraction g L lam x (referenceMetricGramFrame g L (lam,x)) (finitePolynomialField b c x)| ≤
      (A*(k:ℝ)^2)*(referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    by_cases hx : x ∈ K
    · rw [abs_mul,abs_of_pos (referenceDensityFamily_pos g hg L (lam,x))]
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*(A*(k:ℝ)^2*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
          mul_le_mul_of_nonneg_left (hbound hF lam hlam x hx _
            (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) k hk _
            (finitePolynomialField_harmonicHomogeneous k b hb c x))
            (referenceDensityFamily_pos g hg L (lam,x)).le
        _ = _ := by ring
    · rw [hzero x hx,referenceFullCovectorCurvatureContraction_zero]
      simp only [fischerInner_zero_left,mul_zero,abs_zero,le_refl]
  calc
    _ ≤ ∫ x : R3, |referenceDensityFamily g L (lam,x)*referenceFullCovectorCurvatureContraction g L lam x
      (referenceMetricGramFrame g L (lam,x)) (finitePolynomialField b c x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : R3, (A*(k:ℝ)^2)*(referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
      integral_mono hE.abs (hU.const_mul _) hp
    _ = _ := integral_const_mul _ _

theorem referenceLoweredWeighted_first_normalized_identity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℕ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedCrossEnergy g L lam b c f k 1 / sphereNormalization 3 k =
      referenceLoweredWeightedTraceSquare g L lam b c f k (-1) / sphereNormalization 3 k -
      referenceLoweredHessianEnergy g L lam b c f k / sphereNormalization 3 k +
      referenceIntegratedFullCovectorCurvature g L lam b c / sphereNormalization 3 k := by
  rw [referenceLoweredWeighted_first_integrated_identity g hg L lam b c f k hc hf hcompact]
  ring

theorem referenceLoweredWeighted_second_normalized_inequality (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    referenceLoweredWeightedTraceSquare g L lam b c f k 1 / sphereNormalization 3 k ≤
      (k:ℝ)*(∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f k (-1) x) / sphereNormalization 3 k -
      referenceLoweredHessianEnergy g L lam b c f k / sphereNormalization 3 k -
      referenceIntegratedFullCovectorCurvature g L lam b c / sphereNormalization 3 k := by
  have h := div_le_div_of_nonneg_right
    (referenceLoweredWeighted_second_integrated_inequality g hg L lam k hk b hb c f hc hf hcompact)
    (sphereNormalization_pos (n:=3) (by norm_num : 0 < 3) k).le
  simpa only [sub_div] using h

theorem exists_referenceIntegratedFullCovectorCurvature_uniform_normalized_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ hF : SphereFischerInner, ∀ lam ∈ Set.Icc (0:ℝ) 1,
      ∀ k : ℕ, 1 ≤ k → ∀ b : ι → MvPolynomial (Fin 3) ℝ,
      (∀ a, b a ∈ harmonicHomogeneous k) → ∀ c : R3 → ι → ℝ,
      ContDiff ℝ ∞ c → HasCompactSupport c → (∀ x ∉ K, finitePolynomialField b c x = 0) →
      |referenceIntegratedFullCovectorCurvature g L lam b c| / sphereNormalization 3 k ≤
        A*(k:ℝ)^2*((∫ x : R3, referenceDensityFamily g L (lam,x)*fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) / sphereNormalization 3 k) := by
  obtain ⟨A,hA,hbound⟩ := exists_referenceIntegratedFullCovectorCurvature_uniform_bound (ι:=ι) g hg L hL K hK
  refine ⟨A,hA,?_⟩
  intro hF lam hlam k hk b hb c hc hcompact hzero
  have h := div_le_div_of_nonneg_right (hbound hF lam hlam k hk b hb c hc hcompact hzero)
    (sphereNormalization_pos (n:=3) (by norm_num : 0 < 3) k).le
  simpa only [mul_div_assoc] using h

end OAI.AnisotropicCalderon.IntegratedFischerIdentities
