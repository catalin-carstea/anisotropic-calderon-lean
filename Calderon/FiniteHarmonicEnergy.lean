import Calderon.FiniteProfileNormComparison

set_option autoImplicit false
universe u v
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FiniteHarmonicEnergy
open RadiusProfile SphereHarmonic AngularPolynomial ConformalDepth MetricOperator
  SmoothMetricFrame FrameCurvaturePolynomial MetricFiberMeasure MetricFiberFischer
  MetricFiberCovectorTransport FischerConnectionTransport FiniteRaisingEnergy
  FiniteProfileNormComparison ReferenceDensityBounds MovingFrameConnection HorizontalCurvature
variable {σ : Type*} [Fintype σ]

lemma polynomialSphereL2_sum_norm_sq (hO : OrthogonalSphereHarmonics)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a, q a ∈ harmonicHomogeneous (d a)) :
    ‖polynomialSphereL2 (∑ a, q a)‖^2 = ∑ a, ‖polynomialSphereL2 (q a)‖^2 := by
  classical
  rw [map_sum,← real_inner_self_eq_norm_sq,sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  rw [inner_sum]
  calc
    _ = ⟪polynomialSphereL2 (q a),polynomialSphereL2 (q a)⟫_ℝ := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        exact hO (d a) (d b) (fun h => hba (hd h).symm) _
          (polynomialSphereL2_mem _ _ (hq a)) _ (polynomialSphereL2_mem _ _ (hq b))
      · simp
    _ = _ := real_inner_self_eq_norm_sq _

lemma polynomialSphereL2_scaled_sum_norm_sq (hO : OrthogonalSphereHarmonics)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a, q a ∈ harmonicHomogeneous (d a)) (r : σ → ℝ) :
    ‖polynomialSphereL2 (∑ a, r a • q a)‖^2 = ∑ a, (r a)^2*‖polynomialSphereL2 (q a)‖^2 := by
  rw [polynomialSphereL2_sum_norm_sq hO d hd _
    (fun a => (harmonicHomogeneous (d a)).smul_mem (r a) (hq a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma metricFramePolynomial_sum_square (hO : OrthogonalSphereHarmonics)
    (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a, q a ∈ harmonicHomogeneous (d a)) (r : σ → ℝ) :
    (∫ v : R3, (metricFramePolynomial M e (∑ a, r a • q a) v)^2 ∂metricFrameProbability M e he) =
      ∑ a, (r a)^2*(∫ v : R3, (metricFramePolynomial M e (q a) v)^2 ∂metricFrameProbability M e he) := by
  simp only [pow_two,metricFramePolynomial_fiber_integral_pair,real_inner_self_eq_norm_sq]
  simpa only [pow_two] using polynomialSphereL2_scaled_sum_norm_sq hO d hd q hq r

lemma metricFrameCovectorPair_scaled_sum (hO : OrthogonalSphereHarmonics)
    (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a i, q a i ∈ harmonicHomogeneous (d a)) (r : σ → ℝ) :
    metricFrameCovectorPair M e he (fun i => ∑ a, r a • q a i) (fun i => ∑ a, r a • q a i) =
      ∑ a, (r a)^2*metricFrameCovectorPair M e he (q a) (q a) := by
  simp only [metricFrameCovectorPair_eq_sum,← pow_two]
  simp_rw [metricFramePolynomial_sum_square hO M e he d hd _ (fun a => hq a _) r]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

lemma referenceFiberPolynomialSquare_scaled_sum (hO : OrthogonalSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a, q a ∈ harmonicHomogeneous (d a)) (r : σ → ℝ) :
    referenceFiberPolynomialSquare g hg L lam x (∑ a, r a • q a) =
      ∑ a, (r a)^2*referenceFiberPolynomialSquare g hg L lam x (q a) :=
  metricFramePolynomial_sum_square hO _ _ _ d hd q hq r

lemma referenceFiberCovectorPair_scaled_sum (hO : OrthogonalSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a i, q a i ∈ harmonicHomogeneous (d a)) (r : σ → ℝ) :
    referenceFiberCovectorPair g hg L lam x (fun i => ∑ a, r a • q a i) (fun i => ∑ a, r a • q a i) =
      ∑ a, (r a)^2*referenceFiberCovectorPair g hg L lam x (q a) (q a) :=
  metricFrameCovectorPair_scaled_sum hO _ _ _ d hd q hq r

lemma referenceFiberPolynomialSquare_norm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (q : MvPolynomial (Fin 3) ℝ) :
    referenceFiberPolynomialSquare g hg L lam x q = ‖polynomialSphereL2 q‖^2 := by
  simp only [referenceFiberPolynomialSquare,pow_two,metricFramePolynomial_fiber_integral_pair,
    real_inner_self_eq_norm_sq]

lemma integral_referenceFiberPolynomialSquare_sum (hO : OrthogonalSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (d : σ → ℕ) (hd : Function.Injective d) (q : σ → R3 → MvPolynomial (Fin 3) ℝ)
    (hq : ∀ a x, q a x ∈ harmonicHomogeneous (d a))
    (hL1 : ∀ a, Integrable (fun x => referenceDensityFamily g L (lam,x)*‖polynomialSphereL2 (q a x)‖^2)) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      referenceFiberPolynomialSquare g hg L lam x (∑ a, q a x)) ∧
    (∫ x : R3, referenceDensityFamily g L (lam,x)*
      referenceFiberPolynomialSquare g hg L lam x (∑ a, q a x)) =
      ∑ a, ∫ x : R3, referenceDensityFamily g L (lam,x)*‖polynomialSphereL2 (q a x)‖^2 := by
  have heq (x : R3) : referenceDensityFamily g L (lam,x)*
      referenceFiberPolynomialSquare g hg L lam x (∑ a, q a x) =
      ∑ a, referenceDensityFamily g L (lam,x)*‖polynomialSphereL2 (q a x)‖^2 := by
    rw [referenceFiberPolynomialSquare_norm,polynomialSphereL2_sum_norm_sq hO d hd _ (fun a => hq a x),Finset.mul_sum]
  have hsum := integrable_finset_sum Finset.univ (fun a _ => hL1 a)
  refine ⟨hsum.congr (Filter.Eventually.of_forall (fun x => (heq x).symm)),?_⟩
  simp_rw [heq]
  exact integral_finsetSum _ (fun a _ => hL1 a)

variable {ι : Type u} [Fintype ι]

def finiteReferenceSection (g : MatrixField) (L lam : ℝ)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) : R3 × R3 → ℝ :=
  fun z => ∑ a, evaluatedReferencePolynomialField g L lam (b a) (c a) z

theorem fderiv_finiteReferenceSection_horizontal (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ)
    (hc : ∀ a, ContDiff ℝ ∞ (c a)) (x v X : R3) :
    fderiv ℝ (finiteReferenceSection g L lam b c) (x,v)
      (X,-referenceConnectionFamily g L (lam,x) X v) =
      metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x))
        (∑ a, referenceCovariantPolynomialDerivative g L lam (b a) (c a) x X) v := by
  unfold finiteReferenceSection
  rw [fderiv_fun_sum (fun a _ =>
    (contDiff_evaluatedReferencePolynomialField g hg L lam (b a) (c a) (hc a)).differentiable (by simp) (x,v))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam _ _ (hc _) x v X]
  have hcoords : metricFrameCoordinates (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) v =
      fun i => ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x v,
        referenceMetricGramFrame g L (lam,x) i⟫_ℝ := by
    funext i
    exact metricFrameCoordinates_apply _ _ v i
  simp only [referenceMovingFramePolynomial,movingFramePolynomial,metricFramePolynomial,map_sum]
  rw [hcoords]
  rfl

lemma harmonic_sum_sphere_zero_imp_components (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (d : σ → ℕ) (hd : Function.Injective d)
    (q : σ → MvPolynomial (Fin 3) ℝ) (hq : ∀ a, q a ∈ harmonicHomogeneous (d a))
    (hzero : ∀ theta : UnitSphere, (∑ a, q a).eval (theta.val : Fin 3 → ℝ) = 0) :
    ∀ a, q a = 0 := by
  have hs : polynomialSphere (∑ a, q a) = 0 := by ext theta; exact hzero theta
  have hL : polynomialSphereL2 (∑ a, q a) = 0 := by
    change (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (∑ a, q a)) = 0
    rw [hs,map_zero]
  have hsum : (∑ a, ‖polynomialSphereL2 (q a)‖^2) = 0 := by
    rw [← polynomialSphereL2_sum_norm_sq hO d hd q hq,hL,norm_zero]
    norm_num
  intro a
  have hle : ‖polynomialSphereL2 (q a)‖^2 ≤ 0 := by
    calc
      _ ≤ ∑ b, ‖polynomialSphereL2 (q b)‖^2 :=
        Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => sq_nonneg _) (Finset.mem_univ a)
      _ = 0 := hsum
  have hz : ‖polynomialSphereL2 (q a)‖^2 = 0 := le_antisymm hle (sq_nonneg _)
  exact (polynomialSphereL2_eq_zero_iff hF (d a) (q a) (hq a)).mp
    (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

def finiteReferenceProfileEnergyDensity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (m : σ → ℕ)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) (x : R3) : ℝ :=
  let U := fun a => finitePolynomialField (b a) (c a) x
  let Q := fun a i => referenceCovariantPolynomialDerivative g L lam (b a) (c a) x
    (referenceMetricGramFrame g L (lam,x) i)
  let w := fun a => 1+((m a+1:ℕ):ℝ)
  let beta := referenceProfileNorm g lam δ R p L x
  referenceFiberCovectorPair g hg L lam x (fun i => ∑ a, Q a i) (fun i => ∑ a, Q a i) +
    beta^2*referenceFiberPolynomialSquare g hg L lam x (∑ a, w a • U a) +
    beta⁻¹*referenceFiberCovectorPair g hg L lam x
      (fun i => ∑ a, Real.sqrt (w a) • Q a i) (fun i => ∑ a, Real.sqrt (w a) • Q a i) +
    beta*referenceFiberPolynomialSquare g hg L lam x (∑ a, (w a*Real.sqrt (w a)) • U a)

def finiteReferenceProfileEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (m : σ → ℕ)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*finiteReferenceProfileEnergyDensity g hg lam δ R L p m b c x

lemma finiteReferenceProfileEnergyDensity_eq_sum (hO : OrthogonalSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p : ℕ)
    (m : σ → ℕ) (hm : Function.Injective m)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a j, b a j ∈ harmonicHomogeneous (m a+1))
    (c : σ → R3 → ι → ℝ) (x : R3) :
    finiteReferenceProfileEnergyDensity g hg lam δ R L p m b c x =
      ∑ a, referenceProfileModeEnergyDensity g hg lam δ R L p (m a+1) (b a) (c a) x := by
  let U := fun a => finitePolynomialField (b a) (c a) x
  let Q := fun a i => referenceCovariantPolynomialDerivative g L lam (b a) (c a) x
    (referenceMetricGramFrame g L (lam,x) i)
  let w := fun a => 1+((m a+1:ℕ):ℝ)
  let beta := referenceProfileNorm g lam δ R p L x
  have hd : Function.Injective (fun a => m a+1) := by
    intro a b h
    exact hm (Nat.add_right_cancel h)
  have hU : ∀ a, U a ∈ harmonicHomogeneous (m a+1) := fun a => finitePolynomialField_harmonicHomogeneous _ _ (hb a) _ x
  have hQ : ∀ a i, Q a i ∈ harmonicHomogeneous (m a+1) := fun a i =>
    referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam (m a+1) (by omega)
      (b a) (hb a) (c a) x (referenceMetricGramFrame g L (lam,x) i)
  have hG := referenceFiberCovectorPair_scaled_sum hO g hg L lam x (fun a => m a+1) hd Q hQ (fun _ => 1)
  simp only [one_smul,one_pow,one_mul] at hG
  have hhalf := referenceFiberCovectorPair_scaled_sum hO g hg L lam x (fun a => m a+1) hd Q hQ (fun a => Real.sqrt (w a))
  have hV := referenceFiberPolynomialSquare_scaled_sum hO g hg L lam x (fun a => m a+1) hd U hU w
  have hthree := referenceFiberPolynomialSquare_scaled_sum hO g hg L lam x (fun a => m a+1) hd U hU (fun a => w a*Real.sqrt (w a))
  have hsqrt (a : σ) : (Real.sqrt (w a))^2 = w a := Real.sq_sqrt (by dsimp only [w]; positivity)
  change referenceFiberCovectorPair g hg L lam x (fun i => ∑ a, Q a i) (fun i => ∑ a, Q a i) +
    beta^2*referenceFiberPolynomialSquare g hg L lam x (∑ a, w a • U a) +
    beta⁻¹*referenceFiberCovectorPair g hg L lam x (fun i => ∑ a, Real.sqrt (w a) • Q a i) (fun i => ∑ a, Real.sqrt (w a) • Q a i) +
    beta*referenceFiberPolynomialSquare g hg L lam x (∑ a, (w a*Real.sqrt (w a)) • U a) = _
  rw [hG,hV,hhalf,hthree]
  simp_rw [mul_pow,hsqrt]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [referenceProfileModeEnergyDensity,U,Q,w,beta]
  ring

theorem finiteReferenceProfileEnergy_integrable_and_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam δ R L : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (hL : 0 < L) (hp : 1 ≤ p)
    (m : σ → ℕ) (hm : Function.Injective m)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a j, b a j ∈ harmonicHomogeneous (m a+1))
    (c : σ → R3 → ι → ℝ) (hc : ∀ a, ContDiff ℝ ∞ (c a))
    (hcompact : ∀ a, HasCompactSupport (c a)) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*finiteReferenceProfileEnergyDensity g hg lam δ R L p m b c x) ∧
    finiteReferenceProfileEnergy g hg lam δ R L p m b c =
      ∑ a, referenceProfileModeEnergy g hg lam δ R L p (m a+1) (b a) (c a) := by
  have hmode (a : σ) := (referenceProfileModeEnergy_integrable_and_eq hF g hg lam δ R L p (m a+1)
    hδ hR hL hp (by omega) (b a) (hb a) (c a) (hc a) (hcompact a)).1
  have heq (x : R3) : referenceDensityFamily g L (lam,x)*finiteReferenceProfileEnergyDensity g hg lam δ R L p m b c x =
      ∑ a, referenceDensityFamily g L (lam,x)*referenceProfileModeEnergyDensity g hg lam δ R L p (m a+1) (b a) (c a) x := by
    rw [finiteReferenceProfileEnergyDensity_eq_sum hO g hg lam δ R L p m hm b hb c x,Finset.mul_sum]
  have hsum := integrable_finsetSum Finset.univ (fun a _ => hmode a)
  refine ⟨hsum.congr (Filter.Eventually.of_forall (fun x => (heq x).symm)),?_⟩
  unfold finiteReferenceProfileEnergy
  simp_rw [heq]
  exact integral_finsetSum _ (fun a _ => hmode a)

def finiteReferenceRaisingEnergy (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (m : σ → ℕ) (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) (f : R3 → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*referenceFiberPolynomialSquare g hg L lam x
    (∑ a, referenceRaisedPolynomialField g L lam (b a) (c a) f (m a) x)

def finiteReferenceLoweringEnergy (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (m : σ → ℕ) (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) (f : R3 → ℝ) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*referenceFiberPolynomialSquare g hg L lam x
    (∑ a, referenceLoweredPolynomialField g L lam (b a) (c a) f (m a) x)

theorem finiteReferenceRaisingEnergy_integrable_and_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (m : σ → ℕ) (hm : Function.Injective m)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a j, b a j ∈ harmonicHomogeneous (m a+1))
    (c : σ → R3 → ι → ℝ) (f : R3 → ℝ) (hc : ∀ a, ContDiff ℝ ∞ (c a))
    (hf : ContDiff ℝ ∞ f) (hcompact : ∀ a, HasCompactSupport (c a)) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*referenceFiberPolynomialSquare g hg L lam x
      (∑ a, referenceRaisedPolynomialField g L lam (b a) (c a) f (m a) x)) ∧
    finiteReferenceRaisingEnergy g hg L lam m b c f =
      ∑ a, referenceRaisingEnergy g L lam (b a) (c a) f (m a) := by
  have hd : Function.Injective (fun a => m a+2) := by
    intro a b h
    exact hm (Nat.add_right_cancel h)
  exact integral_referenceFiberPolynomialSquare_sum hO g hg L lam (fun a => m a+2) hd
    (fun a x => referenceRaisedPolynomialField g L lam (b a) (c a) f (m a) x)
    (fun a x => referenceRaisedPolynomialField_harmonicHomogeneous g hg L lam (m a) (b a) (hb a) (c a) f x)
    (fun a => integrable_referenceRaisingEnergy hF g hg L lam (m a) (b a) (hb a) (c a) f (hc a) hf (hcompact a))

theorem finiteReferenceLoweringEnergy_integrable_and_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (m : σ → ℕ) (hm : Function.Injective m)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ a j, b a j ∈ harmonicHomogeneous (m a+1))
    (c : σ → R3 → ι → ℝ) (f : R3 → ℝ) (hc : ∀ a, ContDiff ℝ ∞ (c a))
    (hf : ContDiff ℝ ∞ f) (hcompact : ∀ a, HasCompactSupport (c a)) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*referenceFiberPolynomialSquare g hg L lam x
      (∑ a, referenceLoweredPolynomialField g L lam (b a) (c a) f (m a) x)) ∧
    finiteReferenceLoweringEnergy g hg L lam m b c f =
      ∑ a, referenceLoweringEnergy g L lam (b a) (c a) f (m a) := by
  exact integral_referenceFiberPolynomialSquare_sum hO g hg L lam m hm
    (fun a x => referenceLoweredPolynomialField g L lam (b a) (c a) f (m a) x)
    (fun a x => referenceLoweredPolynomialField_harmonicHomogeneous g hg L lam (m a) (b a) (hb a) (c a) f x)
    (fun a => integrable_referenceLoweringEnergy hF g hg L lam (m a) (b a) (hb a) (c a) f (hc a) hf (hcompact a))

lemma finiteReferenceSection_eq_metricFramePolynomial (g : MatrixField) (L lam : ℝ)
    (b : σ → ι → MvPolynomial (Fin 3) ℝ) (c : σ → R3 → ι → ℝ) (x v : R3) :
    finiteReferenceSection g L lam b c (x,v) =
      metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) (∑ a, finitePolynomialField (b a) (c a) x) v := by
  have hcoords : metricFrameCoordinates (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) v =
      fun i => ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x v,
        referenceMetricGramFrame g L (lam,x) i⟫_ℝ := by
    funext i
    exact metricFrameCoordinates_apply _ _ v i
  simp only [finiteReferenceSection,evaluatedReferencePolynomialField,referenceMovingFramePolynomial,
    movingFramePolynomial,metricFramePolynomial,finitePolynomialField,movingFrameCoordinate,
    map_sum,map_smul,smul_eq_C_mul,map_mul,eval_C]
  rw [hcoords]

theorem exists_finiteReferenceProfileEnergy_uniform_coercivity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L cRaise : ℝ, 0 < L ∧ 0 < cRaise ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
          referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x^2 ≤ ε) ∧
        ∀ (ζ : Type v) [Fintype ζ] (τ : Type u) [Fintype τ],
          ∀ hF : SphereFischerInner, ∀ hO : OrthogonalSphereHarmonics,
          ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ m : ζ → ℕ, Function.Injective m →
          ∀ b : ζ → τ → MvPolynomial (Fin 3) ℝ, (∀ a j, b a j ∈ harmonicHomogeneous (m a+1)) →
          ∀ c : ζ → R3 → τ → ℝ, (∀ a, ContDiff ℝ ∞ (c a)) → (∀ a, HasCompactSupport (c a)) →
          (∀ x ∉ K, ∀ v ∈ metricUnitFiber (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x),
            finiteReferenceSection g L lam b c (x,v) = 0) →
          cRaise*finiteReferenceProfileEnergy g hg lam δ R L p m b c ≤
            finiteReferenceRaisingEnergy g hg L lam m b c (referenceLogRadius δ R p L) -
              finiteReferenceLoweringEnergy g hg L lam m b c (referenceLogRadius δ R p L) := by
  obtain ⟨L,C,hL,hC,hall⟩ := exists_referenceProfileModeEnergy_uniform_coercivity.{u} g hg K hK
  refine ⟨L,C,hL,hC,?_⟩
  intro ε hε
  obtain ⟨p,hp,R,hR,hsmall,hone⟩ := hall ε hε
  refine ⟨p,hp,R,hR,hsmall,?_⟩
  intro ζ instζ τ instτ hF hO lam hlam δ hδ hδ1 m hm b hb c hc hcompact hzero
  have hcomponent : ∀ a x, x ∉ K → finitePolynomialField (b a) (c a) x = 0 := by
    intro a x hx
    apply harmonic_sum_sphere_zero_imp_components hF hO (fun a => m a+1)
      (fun a b h => hm (Nat.add_right_cancel h)) (fun a => finitePolynomialField (b a) (c a) x)
      (fun a => finitePolynomialField_harmonicHomogeneous _ _ (hb a) _ x) ?_ a
    intro theta
    have hh := hzero x hx _ (metricFrameSphereMap_mem_metricUnitFiber _ _
      (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) theta)
    rw [finiteReferenceSection_eq_metricFramePolynomial,metricFrameSphereMap,metricFramePolynomial_synthesis] at hh
    exact hh
  have hf : ContDiff ℝ ∞ (referenceLogRadius δ R p L) := contDiff_log_referenceRadius δ R p L hδ hR
  rw [(finiteReferenceProfileEnergy_integrable_and_eq hF hO g hg lam δ R L p hδ hR hL
      (by omega) m hm b hb c hc hcompact).2,
    (finiteReferenceRaisingEnergy_integrable_and_eq hF hO g hg L lam m hm b hb c (referenceLogRadius δ R p L) hc hf hcompact).2,
    (finiteReferenceLoweringEnergy_integrable_and_eq hF hO g hg L lam m hm b hb c (referenceLogRadius δ R p L) hc hf hcompact).2,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun a _ => hone τ hF lam hlam δ hδ hδ1 (m a) (b a) (hb a)
    (c a) (hc a) (hcompact a) (fun x hx => hcomponent a x hx))

end OAI.AnisotropicCalderon.FiniteHarmonicEnergy
