import Calderon.FiniteCovariantCurvature
import Calderon.ContractedFischerAdjunction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.WeightedIndexedCurvature
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew
  MovingFrameConnection FischerConnectionTransport WeightedFischerSquare
  SmoothMetricFrame FrameCurvaturePolynomial FiniteCovariantCurvature
  PolynomialSlotCompatibility FullCovectorCurvature IndexedCovariantCurvature
  ContractedFischerAdjunction

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative

attribute [local irreducible] finitePolynomialField finitePolynomialFieldDerivative
  referenceFrameAngularPolynomial referenceCovariantPolynomialDerivative

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finitePolynomialField_coeff_smul (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (a : R3 → ℝ) (x : R3) :
    finitePolynomialField b (fun y => a y • c y) x = a x • finitePolynomialField b c x := by
  simp only [finitePolynomialField,Pi.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum]

lemma referenceCovariantPolynomialDerivative_coeff_smul (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (a : R3 → ℝ)
    (x V : R3) (hc : DifferentiableAt ℝ c x) (ha : DifferentiableAt ℝ a x) :
    referenceCovariantPolynomialDerivative g L lam b (fun y => a y • c y) x V =
      C (a x) * referenceCovariantPolynomialDerivative g L lam b c x V +
      C (fderiv ℝ a x V) * finitePolynomialField b c x := by
  have hd : finitePolynomialFieldDerivative b (fun y => a y • c y) x V =
      a x • finitePolynomialFieldDerivative b c x V +
      (fderiv ℝ a x V) • finitePolynomialField b c x := by
    simp only [finitePolynomialFieldDerivative,finitePolynomialField,fderiv_fun_smul ha hc,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      add_smul,smul_smul,Finset.sum_add_distrib,Finset.smul_sum]
  rw [referenceCovariantPolynomialDerivative,hd,finitePolynomialField_coeff_smul,
    referenceFrameAngularPolynomial_smul,← smul_eq_C_mul,← smul_eq_C_mul,
    referenceCovariantPolynomialDerivative,smul_add]
  abel

def joinedPolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) : ι ⊕ κ → MvPolynomial (Fin 3) ℝ := Sum.elim b d

def joinedCoefficientFamily (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (x : R3) : ι ⊕ κ → ℝ := Sum.elim (c x) (z x)

lemma contDiff_joinedCoefficientFamily (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (joinedCoefficientFamily c z) := by
  apply contDiff_pi.mpr
  intro a
  cases a with
  | inl i => exact contDiff_pi.mp hc i
  | inr j => exact contDiff_pi.mp hz j

lemma finitePolynomialField_joined (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    finitePolynomialField (joinedPolynomialFamily b d) (joinedCoefficientFamily c z) x =
      finitePolynomialField b c x+finitePolynomialField d z x := by
  simp only [finitePolynomialField,Fintype.sum_sum_type,joinedPolynomialFamily,
    joinedCoefficientFamily,Sum.elim_inl,Sum.elim_inr]

lemma referenceCovariantPolynomialDerivative_joined (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (x V : R3) :
    referenceCovariantPolynomialDerivative g L lam (joinedPolynomialFamily b d)
      (joinedCoefficientFamily c z) x V =
    referenceCovariantPolynomialDerivative g L lam b c x V+
      referenceCovariantPolynomialDerivative g L lam d z x V := by
  have hjoin := (contDiff_joinedCoefficientFamily c z hc hz).differentiable (by simp) x
  have hleft (a : ι) : (fderiv ℝ (joinedCoefficientFamily c z) x V) (.inl a) =
      (fderiv ℝ c x V) a := by
    have h := congrArg (fun T : R3 →L[ℝ] ℝ => T V) (fderiv_apply hjoin (.inl a))
    change fderiv ℝ (fun y => c y a) x V = _ at h
    rw [fderiv_apply (hc.differentiable (by simp) x) a] at h
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using h.symm
  have hright (a : κ) : (fderiv ℝ (joinedCoefficientFamily c z) x V) (.inr a) =
      (fderiv ℝ z x V) a := by
    have h := congrArg (fun T : R3 →L[ℝ] ℝ => T V) (fderiv_apply hjoin (.inr a))
    change fderiv ℝ (fun y => z y a) x V = _ at h
    rw [fderiv_apply (hz.differentiable (by simp) x) a] at h
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using h.symm
  have hd : finitePolynomialFieldDerivative (joinedPolynomialFamily b d)
      (joinedCoefficientFamily c z) x V =
      finitePolynomialFieldDerivative b c x V+finitePolynomialFieldDerivative d z x V := by
    simp only [finitePolynomialFieldDerivative,Fintype.sum_sum_type,
      joinedPolynomialFamily,Sum.elim_inl,Sum.elim_inr,hleft,hright]
  simp only [referenceCovariantPolynomialDerivative]
  change finitePolynomialFieldDerivative (joinedPolynomialFamily b d)
      (joinedCoefficientFamily c z) x V + referenceFrameAngularPolynomial g L lam x V
        (finitePolynomialField (joinedPolynomialFamily b d) (joinedCoefficientFamily c z) x) =
    (finitePolynomialFieldDerivative b c x V+referenceFrameAngularPolynomial g L lam x V (finitePolynomialField b c x)) +
    (finitePolynomialFieldDerivative d z x V+referenceFrameAngularPolynomial g L lam x V (finitePolynomialField d z x))
  rw [hd,finitePolynomialField_joined,referenceFrameAngularPolynomial_add]
  abel

def weightedDerivativePolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ) :
    (ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι → MvPolynomial (Fin 3) ℝ :=
  joinedPolynomialFamily (covariantDerivativePolynomialFamily b) b

def weightedDerivativeCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) (V : R3 → R3) :
    R3 → ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι) → ℝ :=
  joinedCoefficientFamily (fun x => t • covariantDerivativeCoefficientFamily g L lam c V x)
    (fun x => (k*fderiv ℝ f x (V x)) • c x)

lemma contDiff_weightedDerivativeCoefficientFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) (V : R3 → R3)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (weightedDerivativeCoefficientFamily g L lam c f k t V) := by
  apply contDiff_joinedCoefficientFamily
  · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => t)).smul
      (contDiff_covariantDerivativeCoefficientFamily g hg L lam c V hc hV)
  · exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => k)).mul
      ((hf.fderiv_right (m := ∞) (by simp)).clm_apply hV)).smul hc

lemma referenceWeightedPolynomialDerivative_eq_finite (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (V : R3 → R3) (x : R3) :
    referenceWeightedPolynomialDerivative g L lam b c f k t x (V x) =
      finitePolynomialField (weightedDerivativePolynomialFamily b)
        (weightedDerivativeCoefficientFamily g L lam c f k t V) x := by
  rw [weightedDerivativePolynomialFamily,weightedDerivativeCoefficientFamily,
    finitePolynomialField_joined,finitePolynomialField_coeff_smul,finitePolynomialField_coeff_smul,
    ← referenceCovariantPolynomialDerivative_eq_finite_augmented]
  simp only [referenceWeightedPolynomialDerivative,smul_eq_C_mul]

def referenceWeightedIndexedPolynomialHessian (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s t : ℝ) (x : R3) (i j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceWeightedPolynomialDerivative g L lam (weightedDerivativePolynomialFamily b)
    (weightedDerivativeCoefficientFamily g L lam c f k t
      (fun y => referenceMetricGramFrame g L (lam,y) j)) f k s x
    (referenceMetricGramFrame g L (lam,x) i) -
  C s * ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a j) *
    referenceWeightedPolynomialDerivative g L lam b c f k t x (referenceMetricGramFrame g L (lam,x) a)

lemma referenceFrameCovariantDerivative_eq_sum (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x V : R3) (j : Fin 3) :
    fderiv ℝ (fun y => referenceMetricGramFrame g L (lam,y) j) x V+
      referenceConnectionFamily g L (lam,x) V (referenceMetricGramFrame g L (lam,x) j) =
    ∑ a : Fin 3, referenceFrameConnectionCoefficient g L lam x V a j •
      referenceMetricGramFrame g L (lam,x) a := by
  simpa only [covariantFrameDerivative,referenceFrameConnectionCoefficient] using covariantFrameDerivative_eq_sum
    (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
    (fun y => referenceConnectionFamily g L (lam,y))
    (fun y => referenceMetricGramFrame g L (lam,y)) x V
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) j

lemma referenceFrameDerivative_df_eq_hessian_add_connection (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : R3) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ f y (referenceMetricGramFrame g L (lam,y) j)) x
      (referenceMetricGramFrame g L (lam,x) i) =
    coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
      (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j) +
    ∑ a : Fin 3, referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a j *
      fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) a) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  have he : DifferentiableAt ℝ (fun y => referenceMetricGramFrame g L (lam,y) j) x :=
    (contDiff_referenceMetricGramFrame_slice g hg L lam j).differentiable (by simp) x
  have hrec := congrArg (fun v : R3 => fderiv ℝ f x v)
    (referenceFrameCovariantDerivative_eq_sum g hg L lam x (referenceMetricGramFrame g L (lam,x) i) j)
  rw [fderiv_clm_apply hdf he]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    coordinateHessian,map_add,map_sum,map_smul,smul_eq_mul] at *
  linarith

lemma reference_coordinateHessian_symm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x V W : R3) :
    coordinateHessian f (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x V W =
    coordinateHessian f (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x W V := by
  simp only [coordinateHessian]
  rw [hf.contDiffAt.isSymmSndFDerivAt (by simp) V W,
    referenceConnectionFamily_symmetric g hg L lam x V W]

lemma referenceCovariantPolynomialDerivative_weighted_finite (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j : Fin 3) :
    referenceCovariantPolynomialDerivative g L lam (weightedDerivativePolynomialFamily b)
      (weightedDerivativeCoefficientFamily g L lam c f k t
        (fun y => referenceMetricGramFrame g L (lam,y) j)) x
      (referenceMetricGramFrame g L (lam,x) i) =
    C t * referenceCovariantPolynomialDerivative g L lam (covariantDerivativePolynomialFamily b)
      (covariantDerivativeCoefficientFamily g L lam c (fun y => referenceMetricGramFrame g L (lam,y) j))
      x (referenceMetricGramFrame g L (lam,x) i) +
    C (k*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) j)) *
      referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i) +
    C (k * (coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j) +
      ∑ a : Fin 3, referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) i) a j *
        fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) a))) * finitePolynomialField b c x := by
  have he := contDiff_referenceMetricGramFrame_slice g hg L lam j
  have hq := contDiff_covariantDerivativeCoefficientFamily g hg L lam c
    (fun y => referenceMetricGramFrame g L (lam,y) j) hc he
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (referenceMetricGramFrame g L (lam,y) j)) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply he
  have hw : ContDiff ℝ ∞ (fun y => k*fderiv ℝ f y (referenceMetricGramFrame g L (lam,y) j)) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => k)).mul hdf
  have htc : ContDiff ℝ ∞ (fun y => t • covariantDerivativeCoefficientFamily g L lam c
      (fun z => referenceMetricGramFrame g L (lam,z) j) y) := by
    apply contDiff_pi.mpr
    intro a
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => t)).mul (contDiff_pi.mp hq a)
  have hwc : ContDiff ℝ ∞ (fun y =>
      (k*fderiv ℝ f y (referenceMetricGramFrame g L (lam,y) j)) • c y) := by
    apply contDiff_pi.mpr
    intro a
    exact hw.mul (contDiff_pi.mp hc a)
  rw [weightedDerivativePolynomialFamily,weightedDerivativeCoefficientFamily,
    referenceCovariantPolynomialDerivative_joined g L lam
      (covariantDerivativePolynomialFamily b) b
      (fun y => t • covariantDerivativeCoefficientFamily g L lam c
        (fun z => referenceMetricGramFrame g L (lam,z) j) y)
      (fun y => (k*fderiv ℝ f y (referenceMetricGramFrame g L (lam,y) j)) • c y) htc hwc,
    referenceCovariantPolynomialDerivative_coeff_smul g L lam _ _ _ _ _
      (hq.differentiable (by simp) x) (differentiableAt_const t),
    referenceCovariantPolynomialDerivative_coeff_smul g L lam _ _ _ _ _
      (hc.differentiable (by simp) x) (hw.differentiable (by simp) x)]
  rw [fderiv_const_mul (hdf.differentiable (by simp) x) k]
  rw [(hasFDerivAt_const t x).fderiv]
  simp only [fderiv_const,ContinuousLinearMap.zero_apply,map_zero,zero_mul,add_zero,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [referenceFrameDerivative_df_eq_hessian_add_connection g hg L lam f hf]
  abel

lemma referenceWeightedIndexedPolynomialHessian_expansion (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j : Fin 3) :
    referenceWeightedIndexedPolynomialHessian g L lam b c f k s t x i j =
    C (s*t) * referenceIndexedPolynomialHessian g L lam b c x i j +
    C (s*k*coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
      (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j)) * finitePolynomialField b c x +
    C (s*k*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) j)) *
      referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i) +
    C (t*k*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i)) *
      referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) j) +
    C (k^2*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i)*
      fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) j)) * finitePolynomialField b c x := by
  rw [referenceWeightedIndexedPolynomialHessian,referenceWeightedPolynomialDerivative,
    referenceCovariantPolynomialDerivative_weighted_finite g hg L lam b c f k t hc hf,
    ← referenceWeightedPolynomialDerivative_eq_finite]
  simp only [referenceIndexedPolynomialHessian,referenceWeightedPolynomialDerivative,
    Fin.sum_univ_three,map_mul,map_add,map_pow]
  ring

theorem referenceWeightedIndexedPolynomialHessian_mixed_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j : Fin 3) :
    referenceWeightedIndexedPolynomialHessian g L lam b c f k (-1) 1 x j i -
      referenceWeightedIndexedPolynomialHessian g L lam b c f k 1 (-1) x i j =
    referenceHorizontalCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (finitePolynomialField b c x) -
    C (2*k*coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
      (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j)) * finitePolynomialField b c x := by
  rw [referenceWeightedIndexedPolynomialHessian_expansion g hg L lam b c f k (-1) 1 hc hf,
    referenceWeightedIndexedPolynomialHessian_expansion g hg L lam b c f k 1 (-1) hc hf,
    reference_coordinateHessian_symm g hg L lam f hf x
      (referenceMetricGramFrame g L (lam,x) j) (referenceMetricGramFrame g L (lam,x) i),
    ← referenceIndexedPolynomialHessian_antisymm g hg L lam b c hc x i j]
  simp only [map_mul,map_neg,map_one,map_ofNat]
  ring

lemma hasCompactSupport_covariantDerivativeCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (V : R3 → R3) (hc : HasCompactSupport c) :
    HasCompactSupport (covariantDerivativeCoefficientFamily g L lam c V) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  funext a
  rcases a with a | ⟨i,j,a⟩
  · simp only [covariantDerivativeCoefficientFamily,hd0,ContinuousLinearMap.zero_apply,Pi.zero_apply]
  · simp only [covariantDerivativeCoefficientFamily,hc0,Pi.zero_apply,mul_zero]

lemma hasCompactSupport_weightedDerivativeCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) (V : R3 → R3) (hc : HasCompactSupport c) :
    HasCompactSupport (weightedDerivativeCoefficientFamily g L lam c f k t V) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  funext a
  rcases a with a | a
  · rcases a with a | ⟨i,j,a⟩ <;>
      simp only [weightedDerivativeCoefficientFamily,joinedCoefficientFamily,Sum.elim_inl,
        Pi.smul_apply,covariantDerivativeCoefficientFamily,hd0,hc0,
        ContinuousLinearMap.zero_apply,Pi.zero_apply,smul_zero,mul_zero]
  · simp only [weightedDerivativeCoefficientFamily,joinedCoefficientFamily,Sum.elim_inr,
      Pi.smul_apply,hc0,Pi.zero_apply,smul_zero]

lemma referenceWeightedCovectorPolynomialDerivative_partial (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x V : R3) (l : Fin 3) :
    referenceWeightedCovectorPolynomialDerivative g L lam (fun a t => pderiv t (b a)) c f k s x V l =
      pderiv l (referenceWeightedPolynomialDerivative g L lam b c f k s x V) := by
  simp only [referenceWeightedCovectorPolynomialDerivative,referenceWeightedPolynomialDerivative,
    referenceCovectorPolynomialDerivative_partial,finitePolynomialField_partial,map_add,pderiv_C_mul]

def referenceWeightedLoweredCovectorIndexedHessian (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s t : ℝ) (x : R3) (i j l : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceWeightedCovectorPolynomialDerivative g L lam
    (fun a h => pderiv h (weightedDerivativePolynomialFamily b a))
    (weightedDerivativeCoefficientFamily g L lam c f k t
      (fun y => referenceMetricGramFrame g L (lam,y) j)) f k s x
    (referenceMetricGramFrame g L (lam,x) i) l -
  C s * ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a j) *
    referenceWeightedCovectorPolynomialDerivative g L lam (fun a h => pderiv h (b a)) c f k t x
      (referenceMetricGramFrame g L (lam,x) a) l

lemma referenceWeightedLoweredCovectorIndexedHessian_eq_partial (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s t : ℝ) (x : R3) (i j l : Fin 3) :
    referenceWeightedLoweredCovectorIndexedHessian g L lam b c f k s t x i j l =
      pderiv l (referenceWeightedIndexedPolynomialHessian g L lam b c f k s t x i j) := by
  simp only [referenceWeightedLoweredCovectorIndexedHessian,
    referenceWeightedCovectorPolynomialDerivative_partial,referenceWeightedIndexedPolynomialHessian,
    map_sub,map_sum,pderiv_C_mul]

theorem referenceWeightedLoweredCovectorIndexedHessian_mixed_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j l : Fin 3) :
    referenceWeightedLoweredCovectorIndexedHessian g L lam b c f k (-1) 1 x j i l -
      referenceWeightedLoweredCovectorIndexedHessian g L lam b c f k 1 (-1) x i j l =
    referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (fun a => pderiv a (finitePolynomialField b c x)) l -
    C (2*k*coordinateHessian f (fun V W => referenceConnectionFamily g L (lam,x) V W) x
      (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j)) *
      pderiv l (finitePolynomialField b c x) := by
  rw [referenceWeightedLoweredCovectorIndexedHessian_eq_partial,
    referenceWeightedLoweredCovectorIndexedHessian_eq_partial,← map_sub,
    referenceWeightedIndexedPolynomialHessian_mixed_commutator g hg L lam b c f k hc hf]
  simp only [map_sub,pderiv_C_mul,referenceCovectorCurvaturePolynomial_partial]

end OAI.AnisotropicCalderon.WeightedIndexedCurvature
