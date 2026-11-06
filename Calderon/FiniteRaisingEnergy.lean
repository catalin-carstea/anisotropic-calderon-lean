import Calderon.IntegratedFischerIdentities

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FiniteRaisingEnergy
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  WeightedFischerSquare SmoothMetricFrame FischerConnectionTransport
  WeightedIndexedCurvature FiniteTensorRealization IntegratedFischerIdentities
  ReferenceDensityBounds PolynomialSlotCompatibility

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric finitePolynomialField
  referenceCovariantPolynomialDerivative

variable {ι : Type*} [Fintype ι]

def referenceWeightedFramePolynomialField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x : R3) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i)

def referenceRaisedPolynomialField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (m : ℕ) (x : R3) : MvPolynomial (Fin 3) ℝ :=
  sphereRaising m (referenceWeightedFramePolynomialField g L lam b c f (m+1) 1 x)

def referenceLoweredPolynomialField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (m : ℕ) (x : R3) : MvPolynomial (Fin 3) ℝ :=
  polynomialDivergence (referenceWeightedFramePolynomialField g L lam b c f (m+1) (-1) x)

def referenceRaisingEnergy (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (m : ℕ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    ‖polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x)‖^2

def referenceLoweringEnergy (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (m : ℕ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x) *
    ‖polynomialSphereL2 (referenceLoweredPolynomialField g L lam b c f m x)‖^2

lemma sphereRaising_sum_family {σ : Type*} [Fintype σ] (m : ℕ)
    (q : σ → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    sphereRaising m (fun i => ∑ a : σ, q a i) = ∑ a : σ, sphereRaising m (q a) := by
  simp only [sphereRaising,harmonicRaising,polynomialRaising,polynomialDivergence,
    Fin.sum_univ_three,map_sum]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

lemma sphereRaising_C_mul_family (m : ℕ) (q : Fin 3 → MvPolynomial (Fin 3) ℝ) (r : ℝ) :
    sphereRaising m (fun i => C r*q i) = C r*sphereRaising m q := by
  simp only [sphereRaising,harmonicRaising,polynomialRaising,polynomialDivergence,
    Fin.sum_univ_three,pderiv_C_mul]
  ring

lemma sphereRaising_finitePolynomialField (m : ℕ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) :
    sphereRaising m (fun i => finitePolynomialField (fun a => b a i) c x) =
      finitePolynomialField (fun a => sphereRaising m (b a)) c x := by
  simp only [finitePolynomialField,smul_eq_C_mul]
  rw [sphereRaising_sum_family]
  simp_rw [sphereRaising_C_mul_family]

lemma referenceWeightedFramePolynomialField_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (s : ℝ) (x : R3) (i : Fin 3) :
    referenceWeightedFramePolynomialField g L lam b c f (m+1) s x i ∈ harmonicHomogeneous (m+1) :=
  by
    simpa only [referenceWeightedFramePolynomialField,Nat.cast_add,Nat.cast_one] using
      referenceWeightedPolynomialDerivative_harmonicHomogeneous g hg L lam (m+1) (by omega)
        b hb c f s x (referenceMetricGramFrame g L (lam,x) i)

lemma referenceRaisedPolynomialField_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (x : R3) :
    referenceRaisedPolynomialField g L lam b c f m x ∈ harmonicHomogeneous (m+2) :=
  sphereRaising_harmonicHomogeneous m _
    (referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f 1 x)

lemma referenceLoweredPolynomialField_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (x : R3) :
    referenceLoweredPolynomialField g L lam b c f m x ∈ harmonicHomogeneous m :=
  polynomialDivergence_harmonicHomogeneous m _
    (referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f (-1) x)

def referenceRaisingPolynomialFamily (m : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) :
    (Fin 3 × ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι)) → MvPolynomial (Fin 3) ℝ :=
  fun a => sphereRaising m (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a)

lemma referenceRaisedPolynomialField_eq_finite (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (m : ℕ) (x : R3) : referenceRaisedPolynomialField g L lam b c f m x =
      finitePolynomialField (referenceRaisingPolynomialFamily m b)
        (referenceLoweredWeightedTensorCoefficientFamily g L lam c f (m+1) 1) x := by
  unfold referenceRaisedPolynomialField referenceRaisingPolynomialFamily
  rw [← sphereRaising_finitePolynomialField]
  congr 1
  funext i
  exact (finitePolynomialField_referenceWeighted_indexed g L lam b c f (m+1) 1 x i).symm

lemma referenceLoweredPolynomialField_eq_trace (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (m : ℕ) (x : R3) : referenceLoweredPolynomialField g L lam b c f m x =
      referenceLoweredWeightedTraceField g L lam b c f (m+1) (-1) x := by
  simp only [referenceLoweredPolynomialField,polynomialDivergence,referenceWeightedFramePolynomialField,
    referenceLoweredWeightedTraceField,referenceLoweredWeightedTensorField,
    referenceWeightedCovectorPolynomialDerivative_partial]

lemma integrable_referenceRaisingEnergy (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ‖polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x)‖^2) := by
  simp_rw [polynomialSphereL2_norm_sq hF (m+2) _
    (referenceRaisedPolynomialField_harmonicHomogeneous g hg L lam m b hb c f _),
    normalizedFischerSquare,normalizedFischerInner,referenceRaisedPolynomialField_eq_finite]
  simp only [Fintype.card_fin,← mul_div_assoc]
  exact (integrable_referenceDensity_fischerPair g hg L lam _ _ _ _
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f (m+1) 1 hc hf)
    (contDiff_referenceLoweredWeightedTensorCoefficientFamily g hg L lam c f (m+1) 1 hc hf)
    (hasCompactSupport_referenceLoweredWeightedTensorCoefficientFamily g L lam c f (m+1) 1 hcompact)).div_const _

lemma integrable_referenceLoweringEnergy (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ‖polynomialSphereL2 (referenceLoweredPolynomialField g L lam b c f m x)‖^2) := by
  simp_rw [polynomialSphereL2_norm_sq hF m _
    (referenceLoweredPolynomialField_harmonicHomogeneous g hg L lam m b hb c f _),
    normalizedFischerSquare,normalizedFischerInner,referenceLoweredPolynomialField_eq_trace]
  simp only [Fintype.card_fin,← mul_div_assoc]
  exact (integrable_referenceLoweredWeightedTrace_square g hg L lam b c f (m+1) (-1) hc hf hcompact).div_const _

lemma polynomialDivergence_referenceWeightedFramePolynomialField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x : R3) : polynomialDivergence (referenceWeightedFramePolynomialField g L lam b c f k s x) =
      referenceLoweredWeightedTraceField g L lam b c f k s x := by
  simp only [polynomialDivergence,referenceWeightedFramePolynomialField,
    referenceLoweredWeightedTraceField,referenceLoweredWeightedTensorField,
    referenceWeightedCovectorPolynomialDerivative_partial]

def referenceFockNumerator (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (m : ℕ) (x : R3) : ℝ :=
  (3+2*((m:ℝ)+1)) * (referenceWeightedFrameEnergy g L lam b c f ((m:ℝ)+1) 1 x +
    (∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x i j)
        (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x j i)) -
    (4/(4*(m:ℝ)+6))*fischerInner (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) 1 x)
      (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) 1 x)) -
  (3+2*(m:ℝ))*fischerInner (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) (-1) x)
    (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) (-1) x)

theorem referenceRaised_lowered_fock_difference_pointwise (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (x : R3) :
    ‖polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x)‖^2 -
      ‖polynomialSphereL2 (referenceLoweredPolynomialField g L lam b c f m x)‖^2 =
    referenceFockNumerator g L lam b c f m x / sphereNormalization 3 (m+1) := by
  have h := sphere_fock_difference hF m
    (referenceWeightedFramePolynomialField g L lam b c f (m+1) 1 x)
    (referenceWeightedFramePolynomialField g L lam b c f (m+1) (-1) x)
    (referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f 1 x)
    (referenceWeightedFramePolynomialField_harmonicHomogeneous g hg L lam m b hb c f (-1) x)
  simpa only [referenceRaisedPolynomialField,referenceLoweredPolynomialField,referenceFockNumerator,
    polynomialDivergence_referenceWeightedFramePolynomialField,referenceWeightedFrameEnergy,
    referenceWeightedFramePolynomialField,referenceLoweredWeightedTensorField,
    referenceWeightedCovectorPolynomialDerivative_partial,show (2:ℝ)*3=6 by norm_num] using h

lemma integrable_referenceFockNumerator (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (m : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*referenceFockNumerator g L lam b c f m x) := by
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hX := integrable_referenceWeightedFrameEnergy g hg L lam _ hr.continuous b c f ((m:ℝ)+1) 1 hc hf hcompact
  have hC : Integrable (fun x => referenceDensityFamily g L (lam,x)*∑ i : Fin 3, ∑ j : Fin 3,
      fischerInner (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x i j)
        (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x j i)) := by
    simp only [Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceLoweredWeightedTensor_pair g hg L lam b c f ((m:ℝ)+1) 1 1 hc hf hcompact i j j i))
  have hp := integrable_referenceLoweredWeightedTrace_square g hg L lam b c f ((m:ℝ)+1) 1 hc hf hcompact
  have hm := integrable_referenceLoweredWeightedTrace_square g hg L lam b c f ((m:ℝ)+1) (-1) hc hf hcompact
  convert (((hX.add hC).sub (hp.const_mul (4/(4*(m:ℝ)+6)))).const_mul (3+2*((m:ℝ)+1))).sub
    (hm.const_mul (3+2*(m:ℝ))) using 1
  funext x
  simp only [Pi.sub_apply,Pi.add_apply,referenceFockNumerator]
  ring

theorem referenceRaisingEnergy_sub_loweringEnergy_integral (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    referenceRaisingEnergy g L lam b c f m-referenceLoweringEnergy g L lam b c f m =
      (∫ x : R3, referenceDensityFamily g L (lam,x)*referenceFockNumerator g L lam b c f m x) /
        sphereNormalization 3 (m+1) := by
  rw [referenceRaisingEnergy,referenceLoweringEnergy,
    ← integral_sub (integrable_referenceRaisingEnergy hF g hg L lam m b hb c f hc hf hcompact)
      (integrable_referenceLoweringEnergy hF g hg L lam m b hb c f hc hf hcompact)]
  have he : (fun x : R3 => referenceDensityFamily g L (lam,x)*
      ‖polynomialSphereL2 (referenceRaisedPolynomialField g L lam b c f m x)‖^2 -
      referenceDensityFamily g L (lam,x)*‖polynomialSphereL2 (referenceLoweredPolynomialField g L lam b c f m x)‖^2) =
      fun x => (referenceDensityFamily g L (lam,x)*referenceFockNumerator g L lam b c f m x) /
        sphereNormalization 3 (m+1) := by
    funext x
    rw [← mul_sub,referenceRaised_lowered_fock_difference_pointwise hF g hg L lam m b hb c f x]
    ring
  rw [he,integral_div]

theorem integral_referenceFockNumerator (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (m : ℕ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*referenceFockNumerator g L lam b c f m x) =
    (3+2*((m:ℝ)+1)) * ((∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f ((m:ℝ)+1) 1 x) +
      referenceLoweredWeightedCrossEnergy g L lam b c f ((m:ℝ)+1) 1 -
      (4/(4*(m:ℝ)+6))*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) 1) -
    (3+2*(m:ℝ))*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) (-1) := by
  let X : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f ((m:ℝ)+1) 1 x
  let Cc : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*∑ i : Fin 3, ∑ j : Fin 3,
    fischerInner (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x i j)
      (referenceLoweredWeightedTensorField g L lam b c f ((m:ℝ)+1) 1 x j i)
  let Sp : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*fischerInner
    (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) 1 x)
    (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) 1 x)
  let Sm : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)*fischerInner
    (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) (-1) x)
    (referenceLoweredWeightedTraceField g L lam b c f ((m:ℝ)+1) (-1) x)
  have hr : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (lam,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hX : Integrable X := integrable_referenceWeightedFrameEnergy g hg L lam _ hr.continuous b c f ((m:ℝ)+1) 1 hc hf hcompact
  have hC : Integrable Cc := by
    simp only [Cc,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceLoweredWeightedTensor_pair g hg L lam b c f ((m:ℝ)+1) 1 1 hc hf hcompact i j j i))
  have hSp : Integrable Sp := integrable_referenceLoweredWeightedTrace_square g hg L lam b c f ((m:ℝ)+1) 1 hc hf hcompact
  have hSm : Integrable Sm := integrable_referenceLoweredWeightedTrace_square g hg L lam b c f ((m:ℝ)+1) (-1) hc hf hcompact
  let XS : R3 → ℝ := fun x => (X+Cc) x-(4/(4*(m:ℝ)+6))*Sp x
  have hXS : Integrable XS := (hX.add hC).sub (hSp.const_mul (4/(4*(m:ℝ)+6)))
  have hiXS : (∫ x : R3, XS x) = (∫ x, X x)+(∫ x, Cc x)-(4/(4*(m:ℝ)+6))*(∫ x, Sp x) := by
    change (∫ x : R3, (X+Cc) x-(4/(4*(m:ℝ)+6))*Sp x) = _
    rw [integral_sub (hX.add hC) (hSp.const_mul _)]
    change (∫ x : R3, X x+Cc x)-(∫ x : R3, (4/(4*(m:ℝ)+6))*Sp x) = _
    rw [integral_add hX hC,integral_const_mul]
  have hp : (fun x : R3 => referenceDensityFamily g L (lam,x)*referenceFockNumerator g L lam b c f m x) =
      fun x => (3+2*((m:ℝ)+1))*XS x-(3+2*(m:ℝ))*Sm x := by
    funext x
    simp only [referenceFockNumerator,XS,Pi.add_apply,X,Cc,Sp,Sm]
    ring
  rw [hp,integral_sub (hXS.const_mul _) (hSm.const_mul _),integral_const_mul,integral_const_mul,hiXS]
  rfl

theorem referenceRaisingEnergy_sub_loweringEnergy (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    referenceRaisingEnergy g L lam b c f m-referenceLoweringEnergy g L lam b c f m =
    ((3+2*((m:ℝ)+1)) * ((∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f ((m:ℝ)+1) 1 x) +
      referenceLoweredWeightedCrossEnergy g L lam b c f ((m:ℝ)+1) 1 -
      (4/(4*(m:ℝ)+6))*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) 1) -
    (3+2*(m:ℝ))*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) (-1)) / sphereNormalization 3 (m+1) := by
  rw [referenceRaisingEnergy_sub_loweringEnergy_integral hF g hg L lam m b hb c f hc hf hcompact,
    integral_referenceFockNumerator g hg L lam m b c f hc hf hcompact]

theorem referenceRaisingEnergy_sub_loweringEnergy_reduced (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (m : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a, b a ∈ harmonicHomogeneous (m+1))
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    referenceRaisingEnergy g L lam b c f m-referenceLoweringEnergy g L lam b c f m =
    ((3+2*((m:ℝ)+1)) * ((∫ x : R3, referenceDensityFamily g L (lam,x)*referenceWeightedFrameEnergy g L lam b c f ((m:ℝ)+1) 1 x) -
      (4/(4*(m:ℝ)+6))*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) 1 -
      referenceLoweredHessianEnergy g L lam b c f ((m:ℝ)+1)) +
    2*referenceLoweredWeightedTraceSquare g L lam b c f ((m:ℝ)+1) (-1) +
    (3+2*((m:ℝ)+1))*referenceIntegratedFullCovectorCurvature g L lam b c) / sphereNormalization 3 (m+1) := by
  rw [referenceRaisingEnergy_sub_loweringEnergy hF g hg L lam m b hb c f hc hf hcompact,
    referenceLoweredWeighted_first_integrated_identity g hg L lam b c f ((m:ℝ)+1) hc hf hcompact]
  ring

theorem referenceLoweredWeightedTraceSquare_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ) :
    0 ≤ referenceLoweredWeightedTraceSquare g L lam b c f k s :=
  integral_nonneg (fun x => mul_nonneg (referenceDensityFamily_pos g hg L (lam,x)).le
    (fischerInner_self_nonneg _))

end OAI.AnisotropicCalderon.FiniteRaisingEnergy
