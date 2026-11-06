import Calderon.ActualReferenceDDNormalizedCoefficient

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceDDGeometryBounds
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds MetricOperator ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile

/- Actual fixed geometry/profile constants selected before shrink/h/lam.
   Raw angular graphs retained upstream; five coefficient derivatives/fullU/E/F remain separate. -/

def referenceDDFrameAngularConnectionJoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L : ℝ) (a : Fin 3) (z : ℝ × R3) : SphereL2 →L[ℝ] SphereL2 :=
  normalizedReferenceAngularConnection hO hD g L z.1 z.2 (referenceMetricGramFrame g L z a)

lemma contDiff_referenceDDFrameAngularConnectionJoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (a : Fin 3) :
    ContDiff ℝ ∞ (referenceDDFrameAngularConnectionJoint hO hD g L a) := by
  have hc (i j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceFrameConnectionCoefficient g L z.1 z.2 (referenceMetricGramFrame g L z a) i j) := by
    have he : (fun z : ℝ × R3 => referenceFrameConnectionCoefficient g L z.1 z.2
        (referenceMetricGramFrame g L z a) i j) =
        fun z => referenceFrameConnectionJoint g L (fun w => referenceMetricGramFrame g L w a) z i j := by
      funext z
      exact (referenceFrameConnectionJoint_eq g hg L
        (fun w : ℝ × R3 => referenceMetricGramFrame g L w a) z i j).symm
    rw [he]
    exact contDiff_referenceFrameConnectionJoint g hg L
      (fun w : ℝ × R3 => referenceMetricGramFrame g L w a)
      (contDiff_referenceMetricGramFrame g hg L a) i j
  unfold referenceDDFrameAngularConnectionJoint normalizedReferenceAngularConnection
  exact (ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hc i j).smul contDiff_const).const_smul (1/2 : ℝ)

def referenceDDFrameAngularConnectionDerivativeJoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L : ℝ) (a b : Fin 3) (z : ℝ × R3) : SphereL2 →L[ℝ] SphereL2 :=
  fderiv ℝ (referenceDDFrameAngularConnectionJoint hO hD g L b) z (0,referenceMetricGramFrame g L z a)

lemma contDiff_referenceDDFrameAngularConnectionDerivativeJoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (a b : Fin 3) :
    ContDiff ℝ ∞ (referenceDDFrameAngularConnectionDerivativeJoint hO hD g L a b) := by
  unfold referenceDDFrameAngularConnectionDerivativeJoint
  exact ((contDiff_referenceDDFrameAngularConnectionJoint hO hD g hg L b).fderiv_right
    (m := ∞) (by simp)).clm_apply
      (contDiff_const.prodMk (contDiff_referenceMetricGramFrame g hg L a))

lemma referenceDDFrameAngularConnectionDerivativeJoint_eq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (lam : ℝ) (x : R3) (a b : Fin 3) :
    referenceDDFrameAngularConnectionDerivativeJoint hO hD g L a b (lam,x) =
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => normalizedReferenceAngularConnection hO hD g L lam y
          (referenceMetricGramFrame g L (lam,y) b)) x := by
  have hp : HasFDerivAt (fun y : R3 => (lam,y))
      (ContinuousLinearMap.inr ℝ ℝ R3) x := hasFDerivAt_prodMk_right lam x
  have hJ := ((contDiff_referenceDDFrameAngularConnectionJoint hO hD g hg L b).differentiable
    (by simp) (lam,x)).hasFDerivAt.comp x hp
  have ht := congrArg (fun T : R3 →L[ℝ] SphereL2 →L[ℝ] SphereL2 =>
    T (referenceMetricGramFrame g L (lam,x) a)) hJ.fderiv
  simpa only [Function.comp_def,referenceDDFrameAngularConnectionJoint,
    referenceDDFrameAngularConnectionDerivativeJoint,directionalFDeriv,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using ht.symm

lemma contDiff_referenceDDFrameDerivativeJoint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (a b : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      fderiv ℝ (fun w => referenceMetricGramFrame g L w b) z (0,referenceMetricGramFrame g L z a)) := by
  exact ((contDiff_referenceMetricGramFrame g hg L b).fderiv_right
    (m := ∞) (by simp)).clm_apply
      (contDiff_const.prodMk (contDiff_referenceMetricGramFrame g hg L a))

lemma contDiff_referenceDDGammaFrameEntryJoint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (a b j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceConnectionFamily g L z (referenceMetricGramFrame g L z a)
        (referenceMetricGramFrame g L z b) j) := by
  exact (contDiff_piLp_apply (p := 2) (i := j)).comp
    (((contDiff_referenceConnectionFamily g hg L).clm_apply
      (contDiff_referenceMetricGramFrame g hg L a)).clm_apply
      (contDiff_referenceMetricGramFrame g hg L b))

theorem exists_referenceDD_fixed_geometry_uniform_bounds
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      (∀ a, ‖referenceMetricGramFrame g L (lam,x) a‖ ≤ M) ∧
      (∀ a b, ‖directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => referenceMetricGramFrame g L (lam,y) b) x‖ ≤ M) ∧
      (∀ a b j, |referenceConnectionFamily g L (lam,x)
        (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) j| ≤ M) ∧
      (∀ a, ‖normalizedReferenceAngularConnection hO hD g L lam x
        (referenceMetricGramFrame g L (lam,x) a)‖ ≤ M) ∧
      (∀ a b, ‖directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => normalizedReferenceAngularConnection hO hD g L lam y
          (referenceMetricGramFrame g L (lam,y) b)) x‖ ≤ M) ∧
      (∀ a c b, |referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) c b| ≤ M) ∧
      (∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M) ∧
      (∀ a j, |referenceMetricGramFrame g L (lam,x) a j| ≤ M) := by
  obtain ⟨M0,hM0,h0⟩ := exists_uniform_bound_finite_family
    (fun a : Fin 3 => fun z : ℝ × R3 => ‖referenceMetricGramFrame g L z a‖)
    (fun a => (contDiff_referenceMetricGramFrame g hg L a).continuous.norm) K hK
  obtain ⟨M1,hM1,h1⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 =>
      ‖fderiv ℝ (fun w => referenceMetricGramFrame g L w t.2) z (0,referenceMetricGramFrame g L z t.1)‖)
    (fun t => (contDiff_referenceDDFrameDerivativeJoint g hg L t.1 t.2).continuous.norm) K hK
  obtain ⟨M2,hM2,h2⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 =>
      referenceConnectionFamily g L z (referenceMetricGramFrame g L z t.1)
        (referenceMetricGramFrame g L z t.2.1) t.2.2)
    (fun t => (contDiff_referenceDDGammaFrameEntryJoint g hg L t.1 t.2.1 t.2.2).continuous) K hK
  obtain ⟨M3,hM3,h3⟩ := exists_uniform_bound_finite_family
    (fun a : Fin 3 => fun z : ℝ × R3 => ‖referenceDDFrameAngularConnectionJoint hO hD g L a z‖)
    (fun a => (contDiff_referenceDDFrameAngularConnectionJoint hO hD g hg L a).continuous.norm) K hK
  obtain ⟨M4,hM4,h4⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 => ‖referenceDDFrameAngularConnectionDerivativeJoint hO hD g L t.1 t.2 z‖)
    (fun t => (contDiff_referenceDDFrameAngularConnectionDerivativeJoint hO hD g hg L t.1 t.2).continuous.norm) K hK
  obtain ⟨M5,hM5,h5⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  let M : ℝ := M0+M1+M2+M3+M4+M5
  have h0M : M0 ≤ M := by dsimp [M]; linarith
  have h1M : M1 ≤ M := by dsimp [M]; linarith
  have h2M : M2 ≤ M := by dsimp [M]; linarith
  have h3M : M3 ≤ M := by dsimp [M]; linarith
  have h4M : M4 ≤ M := by dsimp [M]; linarith
  have h5M : M5 ≤ M := by dsimp [M]; linarith
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro lam hlam x hx
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a
    have ht := (h0 lam hlam x hx a).trans h0M
    simpa only [abs_of_nonneg (norm_nonneg _)] using ht
  · intro a b
    have ht := (h1 lam hlam x hx (a,b)).trans h1M
    rw [← fderiv_referenceGramFrame_slice_apply g hg L (lam,x) b
      (referenceMetricGramFrame g L (lam,x) a)] at ht
    simpa only [directionalFDeriv,abs_of_nonneg (norm_nonneg _)] using ht
  · intro a b j
    exact (h2 lam hlam x hx (a,b,j)).trans h2M
  · intro a
    have ht := (h3 lam hlam x hx a).trans h3M
    simpa only [referenceDDFrameAngularConnectionJoint,abs_of_nonneg (norm_nonneg _)] using ht
  · intro a b
    have ht := (h4 lam hlam x hx (a,b)).trans h4M
    rw [referenceDDFrameAngularConnectionDerivativeJoint_eq hO hD g hg L lam x a b] at ht
    simpa only [abs_of_nonneg (norm_nonneg _)] using ht
  · intro a c b
    exact ((h5 lam hlam x hx).2.2.2 a c b).trans h5M
  · intro i a
    exact ((h5 lam hlam x hx).2.1 i a).trans h5M
  · intro a j
    have ht := ((h5 lam hlam x hx).1 a j).trans h5M
    simpa only [frameEntry] using ht

lemma referenceFrameDerivative_directional_product
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : Fin 3) (x : R3) :
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (referenceFrameDerivative g L lam b f) x =
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (fderiv ℝ f) x
        (referenceMetricGramFrame g L (lam,x) b) +
      fderiv ℝ f x (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => referenceMetricGramFrame g L (lam,y) b) x) := by
  unfold referenceFrameDerivative
  exact directionalFDeriv_clm_apply _ (fderiv ℝ f)
    (fun y => referenceMetricGramFrame g L (lam,y) b)
    (hf.fderiv_right (m := ∞) (by simp))
    (contDiff_referenceMetricGramFrame_slice g hg L lam b) x

theorem exists_referenceDD_logRadius_frame_uniform_bounds
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ F : ℝ, 1 ≤ F ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta →
      (∀ a, |referenceFrameDerivative g L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F * beta) ∧
      (∀ a b, |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x| ≤ F * beta^2) := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_bounds hO hD g hg L K hK
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound g hg L hL K hK 1 (by omega)
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound g hg L hL K hK 2 (by omega)
  let F : ℝ := 1+J1*M+J2*M^2
  have hM0 : 0 ≤ M := by linarith
  have hJM : 0 ≤ J1*M := mul_nonneg hJ1.le hM0
  have hJM2 : 0 ≤ J2*M^2 := mul_nonneg hJ2.le (sq_nonneg _)
  refine ⟨F,by dsimp [F]; linarith,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  have hf : ContDiff ℝ ∞ f := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hbeta : 0 ≤ beta := by linarith
  have hbeta2 : beta ≤ beta^2 := by nlinarith
  have hdf : ‖fderiv ℝ f x‖ ≤ J1*beta := by
    simpa only [norm_iteratedFDeriv_one,pow_one,f] using hjet1 lam hlam δ hδ hδ1 R hR p hp x hx
  have hddf : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ J2*beta^2 := by
    have he : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      rw [← norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
    rw [he]
    exact hjet2 lam hlam δ hδ hδ1 R hR p hp x hx
  have hG := hgeom lam hlam x hx
  refine ⟨?_,?_⟩
  · intro a
    have ht : |referenceFrameDerivative g L lam a f x| ≤ J1*beta*M := by
      unfold referenceFrameDerivative
      have hn := (fderiv ℝ f x).le_opNorm (referenceMetricGramFrame g L (lam,x) a)
      have hm := mul_le_mul hdf (hG.1 a) (norm_nonneg _) (mul_nonneg hJ1.le hbeta)
      calc
        _ ≤ ‖fderiv ℝ f x‖ * ‖referenceMetricGramFrame g L (lam,x) a‖ := by
          simpa only [Real.norm_eq_abs] using hn
        _ ≤ J1*beta*M := hm
    change |referenceFrameDerivative g L lam a f x| ≤ F*beta
    exact ht.trans (by dsimp [F]; nlinarith)
  · intro a b
    have hterm1 : |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (fderiv ℝ f) x
        (referenceMetricGramFrame g L (lam,x) b)| ≤ J2*beta^2*M*M := by
      have hn := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ f) x)
        (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b)
      have hm1 := mul_le_mul hddf (hG.1 a) (norm_nonneg _) (mul_nonneg hJ2.le (sq_nonneg beta))
      have hm2 := mul_le_mul hm1 (hG.1 b) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hJ2.le (sq_nonneg beta)) hM0)
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖referenceMetricGramFrame g L (lam,x) a‖ *
          ‖referenceMetricGramFrame g L (lam,x) b‖ := by
          simpa only [directionalFDeriv,Real.norm_eq_abs] using hn
        _ ≤ J2*beta^2*M*M := hm2
    have hterm2 : |fderiv ℝ f x (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
        (fun y => referenceMetricGramFrame g L (lam,y) b) x)| ≤ J1*beta*M := by
      have hn := (fderiv ℝ f x).le_opNorm
        (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
          (fun y => referenceMetricGramFrame g L (lam,y) b) x)
      have hm := mul_le_mul hdf (hG.2.1 a b) (norm_nonneg _) (mul_nonneg hJ1.le hbeta)
      calc
        _ ≤ ‖fderiv ℝ f x‖ * ‖directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
          (fun y => referenceMetricGramFrame g L (lam,y) b) x‖ := by
          simpa only [Real.norm_eq_abs] using hn
        _ ≤ J1*beta*M := hm
    change |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (referenceFrameDerivative g L lam b f) x| ≤ F*beta^2
    rw [referenceFrameDerivative_directional_product g hg L lam f hf a b x]
    calc
      _ ≤ |directionalFDeriv (referenceMetricGramFrame g L (lam,x) a) (fderiv ℝ f) x
        (referenceMetricGramFrame g L (lam,x) b)| +
        |fderiv ℝ f x (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
          (fun y => referenceMetricGramFrame g L (lam,y) b) x)| := abs_add_le _ _
      _ ≤ J2*beta^2*M*M+J1*beta*M := add_le_add hterm1 hterm2
      _ ≤ F*beta^2 := by
        dsimp [F]
        have hwt := mul_le_mul_of_nonneg_left hbeta2 hJM
        nlinarith [sq_nonneg beta]

lemma physicalMixedQFrameCoefficient_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (h : MatrixField)
    (x : R3) (M : ℝ) (hM : 0 ≤ M)
    (htheta : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M)
    (hh : ∀ i j, |h x i j| ≤ 1) (a b : Fin 3) :
    |physicalMixedQFrameCoefficient g L lam h a b x| ≤ 1 + 9 * M^2 := by
  have ht (i j : Fin 3) : |h x i j * referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)| ≤ M^2 := by
    rw [abs_mul,abs_mul]
    have h1 := mul_le_mul (hh i j) (htheta i a) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have h2 := mul_le_mul h1 (htheta j b) (abs_nonneg _) (mul_nonneg (by norm_num : (0:ℝ)≤1) hM)
    convert h2 using 1 <;> ring
  have hs : |physicalMixedFrameCoefficient g L lam h a b x| ≤ 9*M^2 := by
    have ht1 := abs_sum_three_le
      (fun i => ∑ j : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x))
      (3*M^2) (fun i => abs_sum_three_le _ (M^2) (ht i))
    simpa only [physicalMixedFrameCoefficient,show (3:ℝ)*(3*M^2)=9*M^2 by ring] using ht1
  rw [physicalMixedQFrameCoefficient_decomposition g hg L lam h a b x]
  have hd : |if a=b then (1:ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hd hs)

lemma referenceRadius_mul_beta_le_eps_div
    (δ R L : ℝ) (p : ℕ) (x : R3) (hδ : 0 < δ) (hR : 0 < R)
    (beta eps : ℝ) (hbeta : 1 ≤ beta)
    (hsmall : referenceRadius δ R p L x * beta^2 ≤ eps) :
    referenceRadius δ R p L x * beta ≤ eps / beta := by
  have hb : 0 < beta := by linarith
  apply (le_div_iff₀ hb).mpr
  convert hsmall using 1 <;> ring

lemma weighted_h_zero_le_one
    (δ R L : ℝ) (p : ℕ) (x : R3) (hδ : 0 < δ) (hR : 0 < R)
    (beta eps : ℝ) (hbeta : 1 ≤ beta) (heps : eps ≤ 1)
    (hsmall : referenceRadius δ R p L x * beta^2 ≤ eps)
    (h : MatrixField) (hh : ∀ i j, |h x i j| ≤ eps * referenceRadius δ R p L x) :
    ∀ i j, |h x i j| ≤ 1 := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hb : 1 ≤ beta^2 := by nlinarith
  have hr1 : referenceRadius δ R p L x ≤ 1 := by nlinarith
  have hprod : eps*referenceRadius δ R p L x ≤ 1 := by
    have ht := mul_le_mul heps hr1 hr.le (by norm_num : (0:ℝ)≤1)
    simpa only [one_mul] using ht
  intro i j
  exact (hh i j).trans hprod

end OAI.AnisotropicCalderon.ActualReferenceDDGeometryBounds
