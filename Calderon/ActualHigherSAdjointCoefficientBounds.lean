import Calderon.ActualHigherSAdjointCoefficientExtraction
import Calderon.ActualHigherSZeroCoefficientBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointCoefficientBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  WeightedFrameGreen
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/- Cached standard instances only: each body is the pre-existing inferred
canonical instance; no norm convention or bound is replaced. -/
@[instance_reducible] private def adjointCoeffInnerNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def adjointCoeffInnerModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def adjointCoeffParameterNormed :
    NormedAddCommGroup ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) := inferInstance
@[instance_reducible] private def adjointCoeffParameterModule :
    NormedSpace ℝ ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) := inferInstance
attribute [local instance] adjointCoeffInnerNormed adjointCoeffInnerModule
  adjointCoeffParameterNormed adjointCoeffParameterModule

private lemma compact_family_bound {α E ι : Type*} [TopologicalSpace α]
    [SeminormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : ι, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : ι => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : ι, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : ι, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : ι, |C j| := Finset.single_le_sum (f := fun j : ι => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : ι, |C j| := by linarith

/-- Exact derivative of the original fixed-q slice, from the joint derivative. -/
lemma fderiv_fixed_parameter_apply (f : ℝ × R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (x v : R3) :
    fderiv ℝ (fun y : R3 => f (q,y)) x v = fderiv ℝ f (q,x) (0,v) := by
  have ht : HasFDerivAt (fun y : R3 => (q,y)) (ContinuousLinearMap.inr ℝ ℝ R3) x :=
    (hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)
  have h := ((hf.differentiable (by simp) (q,x)).hasFDerivAt.comp x ht).fderiv
  exact congrArg (fun A : R3 →L[ℝ] ℝ => A v) h

/-- Joint regularity of the ACTUAL density-weighted frame divergence. -/
theorem contDiff_joint_referenceWeightedFrameDivergence (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun t : ℝ × R3 => referenceWeightedFrameDivergence g L t.1 i t.2) := by
  have hmu := contDiff_referenceDensityFamily g hg L
  have hX := contDiff_referenceMetricGramFrame g hg L i
  let f : Fin 3 → (ℝ × R3) → ℝ := fun j t =>
    referenceDensityFamily g L t * referenceMetricGramFrame g L t i j
  have hf (j : Fin 3) : ContDiff ℝ ∞ (f j) := by
    have hj : ContDiff ℝ ∞ (fun t : ℝ × R3 => referenceMetricGramFrame g L t i j) := by
      first
      | exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hX
      | exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := j)).comp hX
      | exact (contDiff_piLp (𝕜 := ℝ) 2).1 hX j
    exact hmu.mul hj
  have he : (fun t : ℝ × R3 => referenceWeightedFrameDivergence g L t.1 i t.2) =
      fun t => ∑ j : Fin 3, fderiv ℝ (f j) t (0,coordinateDirection j) := by
    funext t
    change (∑ j : Fin 3, fderiv ℝ (fun y : R3 => f j (t.1,y)) t.2 (coordinateDirection j)) = _
    exact Finset.sum_congr rfl (fun j _ => fderiv_fixed_parameter_apply (f j) (hf j) t.1 t.2 _)
  rw [he]
  exact ContDiff.sum (fun j _ => ((contDiff_infty_iff_fderiv.1 (hf j)).2.clm_apply contDiff_const))

/-- One geometry constant before every profile and q, for the ORIGINAL density quotient. -/
theorem exists_normalized_frame_divergence_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      |referenceWeightedFrameDivergence g L q i x / referenceDensityFamily g L (q,x)| ≤ C := by
  have hcompact : IsCompact (Set.prod (Icc (0 : ℝ) 1) K) := isCompact_Icc.prod hK
  have hc (i : Fin 3) : Continuous (fun t : ℝ × R3 =>
      referenceWeightedFrameDivergence g L t.1 i t.2 / referenceDensityFamily g L t) :=
    (contDiff_joint_referenceWeightedFrameDivergence g hg L i).continuous.div
      (contDiff_referenceDensityFamily g hg L).continuous
      (fun t => ne_of_gt (referenceDensityFamily_pos g hg L t))
  obtain ⟨C,hC,hb⟩ := compact_family_bound (Set.prod (Icc (0 : ℝ) 1) K) hcompact
    (fun i : Fin 3 => fun t : ℝ × R3 =>
      referenceWeightedFrameDivergence g L t.1 i t.2 / referenceDensityFamily g L t)
    (fun i => (hc i).continuousOn)
  refine ⟨C,hC,?_⟩
  intro q hq x hx i
  simpa only [Real.norm_eq_abs] using hb i (q,x) ⟨hq,hx⟩

/-- Exact scalar product rule behind both density corrections. -/
lemma normalized_density_coefficient_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) (R Q : R3 → ℝ) (x : R3)
    (hR : DifferentiableAt ℝ R x) (hQ : DifferentiableAt ℝ Q x) :
    ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i (fun y => (R y)^2*Q y) x /
      referenceDensityFamily g L (q,x) =
    (R x)^2*Q x*(referenceWeightedFrameDivergence g L q i x / referenceDensityFamily g L (q,x)) +
      2*R x*Q x*fderiv ℝ R x (referenceMetricGramFrame g L (q,x) i) +
      (R x)^2*fderiv ℝ Q x (referenceMetricGramFrame g L (q,x) i) := by
  have hd := ((hR.hasFDerivAt.mul hR.hasFDerivAt).mul hQ.hasFDerivAt).fderiv
  have hfEq : (R * R * Q) = (fun y : R3 => R y*R y*Q y) := by funext y; rfl
  rw [hfEq] at hd
  have he : fderiv ℝ (fun y => (R y)^2*Q y) x (referenceMetricGramFrame g L (q,x) i) =
      (R x)^2*fderiv ℝ Q x (referenceMetricGramFrame g L (q,x) i) +
        2*R x*Q x*fderiv ℝ R x (referenceMetricGramFrame g L (q,x) i) := by
    calc
      _ = (R x*R x)*fderiv ℝ Q x (referenceMetricGramFrame g L (q,x) i) +
        Q x*(R x*fderiv ℝ R x (referenceMetricGramFrame g L (q,x) i)+
          R x*fderiv ℝ R x (referenceMetricGramFrame g L (q,x) i)) := by
        simpa only [pow_two,Pi.mul_apply,add_apply,smul_apply,smul_eq_mul] using
          congrArg (fun A : R3 →L[ℝ] ℝ => A (referenceMetricGramFrame g L (q,x) i)) hd
      _ = _ := by ring
  unfold ActualHigherSSecondAdjoint.densityDerivativeCoefficient
  rw [he]
  field_simp [ne_of_gt (referenceDensityFamily_pos g hg L (q,x))] <;> ring

private lemma abs_normalized_correction_le (r Q d a b CQ CD CA CB : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCQ : 0 ≤ CQ) (hCD : 0 ≤ CD)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hQ : |Q| ≤ CQ) (hD : |d| ≤ CD) (hA : |a| ≤ CA) (hB : |b| ≤ CB) :
    |r^2*Q*d + 2*r*Q*a + r^2*b| ≤ (CQ*CD+2*CQ*CA+CB)*r := by
  have hrr : r^2 ≤ r := by nlinarith
  have h1 : |r^2*Q*d| ≤ r^2*(CQ*CD) := by
    calc
      _ = r^2*(|Q| * |d|) := by simp [abs_mul,abs_of_nonneg (sq_nonneg r),mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hQ hD (abs_nonneg _) hCQ) (sq_nonneg r)
  have h2 : |2*r*Q*a| ≤ 2*r*(CQ*CA) := by
    calc
      _ = 2*r*(|Q| * |a|) := by simp [abs_mul,abs_of_nonneg hr,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hQ hA (abs_nonneg _) hCQ)
        (mul_nonneg (by norm_num) hr)
  have h3 : |r^2*b| ≤ r^2*CB := by
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg r)] using
      mul_le_mul_of_nonneg_left hB (sq_nonneg r)
  calc
    _ ≤ |r^2*Q*d+2*r*Q*a|+|r^2*b| := abs_add_le _ _
    _ ≤ |r^2*Q*d|+|2*r*Q*a|+|r^2*b| := add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ r^2*(CQ*CD)+2*r*(CQ*CA)+r^2*CB := add_le_add (add_le_add h1 h2) h3
    _ ≤ r*(CQ*CD)+2*r*(CQ*CA)+r*CB :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hrr (mul_nonneg hCQ hCD)) (le_refl _))
        (mul_le_mul_of_nonneg_right hrr hCB)
    _ = _ := by ring

/-- Both actual coefficient-density corrections are uniformly O(R), on one compact
geometry set before all profiles. In fact every frame direction k is covered. -/
theorem exists_density_derivative_uniform_radius_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (y0 : R3) (ρ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
      referenceRadius δr Ar p L x ≤ 1 → ‖fderiv ℝ (referenceRadius δr Ar p L) x‖ ≤ 1 →
      ∀ i j k : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q k
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x /
          referenceDensityFamily g L (q,x)| ≤ K*referenceRadius δr Ar p L x := by
  classical
  let Kx := closedBall y0 ρ
  let Kqx := Set.prod (Icc (0 : ℝ) 1) Kx
  have hKx : IsCompact Kx := isCompact_closedBall y0 ρ
  have hKqx : IsCompact Kqx := isCompact_Icc.prod hKx
  have hQfull := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound g L y0 ρ hg g2 hg2
  rcases hQfull with ⟨CQ,hCQ,hQc⟩
  have hDivFull := exists_normalized_frame_divergence_uniform_bound g hg L Kx hKx
  rcases hDivFull with ⟨CD,hCD,hDiv⟩
  have hXfull := compact_family_bound Kqx hKqx
    (fun i : Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  rcases hXfull with ⟨CX,hCX,hXc⟩
  let Q : (Fin 3 × Fin 3) → (ℝ × R3) → ℝ := fun ij t =>
    referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 ij.1 ij.2
  have hQ (ij : Fin 3 × Fin 3) : ContDiff ℝ ∞ (Q ij) :=
    contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L ij.1 ij.2
  have hQ1full := compact_family_bound Kqx hKqx
    (fun ij : Fin 3 × Fin 3 => fderiv ℝ (Q ij))
    (fun ij => (contDiff_infty_iff_fderiv.1 (hQ ij)).2.continuous.continuousOn)
  rcases hQ1full with ⟨CQ1,hCQ1,hQ1c⟩
  have hCQ0 : 0 ≤ CQ := le_trans zero_le_one hCQ
  have hCD0 : 0 ≤ CD := le_trans zero_le_one hCD
  have hCX0 : 0 ≤ CX := le_trans zero_le_one hCX
  have hCQ10 : 0 ≤ CQ1 := le_trans zero_le_one hCQ1
  let K := CQ*CD+2*CQ*CX+CQ1*CX
  have hK0 : 0 ≤ K := add_nonneg
    (add_nonneg (mul_nonneg hCQ0 hCD0) (mul_nonneg (mul_nonneg (by norm_num) hCQ0) hCX0))
    (mul_nonneg hCQ10 hCX0)
  refine ⟨K,hK0,?_⟩
  intro δr Ar p hδr hAr q hq x hx hr1 hdR i j k
  let R := referenceRadius δr Ar p L
  have hr0 : 0 ≤ R x := le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hXi (k : Fin 3) : ‖referenceMetricGramFrame g L (q,x) k‖ ≤ CX := hXc k (q,x) ⟨hq,hx⟩
  have hDr (k : Fin 3) : |fderiv ℝ R x (referenceMetricGramFrame g L (q,x) k)| ≤ CX := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ R x‖ * ‖referenceMetricGramFrame g L (q,x) k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*CX := mul_le_mul hdR (hXi k) (norm_nonneg _) zero_le_one
      _ = CX := one_mul _
  have hDq (i j k : Fin 3) :
      |fderiv ℝ (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
        (referenceMetricGramFrame g L (q,x) k)| ≤ CQ1*CX := by
    change |fderiv ℝ (fun y : R3 => Q (i,j) (q,y)) x (referenceMetricGramFrame g L (q,x) k)| ≤ CQ1*CX
    rw [fderiv_fixed_parameter_apply (Q (i,j)) (hQ (i,j)),← Real.norm_eq_abs]
    have hvec : ‖((0 : ℝ),referenceMetricGramFrame g L (q,x) k)‖ ≤ CX := by simpa using hXi k
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hQ1c (i,j) (q,x) ⟨hq,hx⟩) hvec (norm_nonneg _) hCQ10)
  have hRs := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hQs : ContDiff ℝ ∞ (fun y : R3 => Q (i,j) (q,y)) :=
    (hQ (i,j)).comp (contDiff_const.prodMk contDiff_id)
  have he := normalized_density_coefficient_eq g hg L q k R (fun y : R3 => Q (i,j) (q,y)) x
    (hRs.differentiable (by simp) x) (hQs.differentiable (by simp) x)
  change |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q k
    (fun y : R3 => (R y)^2*Q (i,j) (q,y)) x / referenceDensityFamily g L (q,x)| ≤ K*R x
  rw [he]
  exact abs_normalized_correction_le (R x) (Q (i,j) (q,x))
    (referenceWeightedFrameDivergence g L q k x / referenceDensityFamily g L (q,x))
    (fderiv ℝ R x (referenceMetricGramFrame g L (q,x) k))
    (fderiv ℝ (fun y : R3 => Q (i,j) (q,y)) x (referenceMetricGramFrame g L (q,x) k))
    CQ CD CX (CQ1*CX) hr0 hr1 hCQ0 hCD0 hCX0 (mul_nonneg hCQ10 hCX0)
    ((hQc q hq x hx i j).1) (hDiv q hq x hx k) (hDr k) (hDq i j k)

private lemma norm_comp_le {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : F →L[ℝ] V) (B : E →L[ℝ] F) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b) : ‖A.comp B‖ ≤ a*b :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) ha0)

private lemma norm_smul_le_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : E) (A B : ℝ) (hA : 0 ≤ A) (hr : |r| ≤ A) (hv : ‖v‖ ≤ B) :
    ‖r • v‖ ≤ A*B := by
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hr hv (norm_nonneg _) hA

private lemma norm_sum_three_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin 3 → ℝ) (v : Fin 3 → E) (A B : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i, |a i| ≤ A) (hv : ∀ i, ‖v i‖ ≤ B) : ‖∑ i : Fin 3, a i • v i‖ ≤ 3*A*B := by
  calc
    _ ≤ ∑ i : Fin 3, ‖a i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, A*B := Finset.sum_le_sum
      (fun i _ => norm_smul_le_of_le (a i) (v i) A B hA (ha i) (hv i))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma norm_double_sum_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → Fin 3 → E) (A B : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i j, |a i j| ≤ A) (hv : ∀ i j, ‖v i j‖ ≤ B) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, a i j • v i j‖ ≤ 9*A*B := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, a i j • v i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 3*A*B := Finset.sum_le_sum
      (fun i _ => norm_sum_three_smul_le (a i) (v i) A B hA (ha i) (hv i))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma norm_seven_terms_le {E : Type*} [SeminormedAddCommGroup E]
    (a b c d e f h : E) :
    ‖-a+b-c-d+e+f-h‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖+‖h‖ := by
  have h1 : ‖-a+b‖ ≤ ‖a‖+‖b‖ := by simpa only [norm_neg] using norm_add_le (-a) b
  have h2 := (norm_sub_le (-a+b) c).trans (add_le_add h1 (le_refl ‖c‖))
  have h3 := (norm_sub_le (-a+b-c) d).trans (add_le_add h2 (le_refl ‖d‖))
  have h4 := (norm_add_le (-a+b-c-d) e).trans (add_le_add h3 (le_refl ‖e‖))
  have h5 := (norm_add_le (-a+b-c-d+e) f).trans (add_le_add h4 (le_refl ‖f‖))
  exact (norm_sub_le (-a+b-c-d+e+f) h).trans (add_le_add h5 (le_refl ‖h‖))

private lemma norm_weighted_zero_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O B : E →L[ℝ] F) (f M β : ℝ) (hM : 1 ≤ M) (hβ : 1 ≤ β)
    (hO : ‖O‖ ≤ M) (hB : ‖B‖ ≤ M) (hf : |f| ≤ M*β) :
    ‖O+f • B‖ ≤ 2*M^2*β := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hβ0 : 0 ≤ β := le_trans zero_le_one hβ
  have hMM : M ≤ M^2 := by nlinarith
  have hMMβ : M ≤ M^2*β := hMM.trans (by nlinarith [sq_nonneg M])
  have hs := norm_smul_le_of_le f B (M*β) M (mul_nonneg hM0 hβ0) hf hB
  exact (norm_add_le _ _).trans (by nlinarith [hs])

/-- Seven original adjoint Second zero-row groups; the coefficients 2f and physical
zero mode are retained. This is typed norm algebra, independent of geometry bodies. -/
lemma norm_adjoint_second_shape_le {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (J : F →L[ℝ] V)
    (D WH Bhi : E →L[ℝ] F) (El WL Blo : F →L[ℝ] V)
    (Ei Ej : E →L[ℝ] F) (Ek : Fin 3 → E →L[ℝ] F)
    (fi fj : ℝ) (Γ : Fin 3 → ℝ) (M β : ℝ) (hM : 1 ≤ M) (hβ : 1 ≤ β)
    (hJ : ‖J‖ ≤ M) (hD : ‖D‖ ≤ M) (hWH : ‖WH‖ ≤ 2*M^2*β)
    (hBhi : ‖Bhi‖ ≤ M) (hEl : ‖El‖ ≤ M) (hWL : ‖WL‖ ≤ 2*M^2*β)
    (hBlo : ‖Blo‖ ≤ M) (hEi : ‖Ei‖ ≤ M) (hEj : ‖Ej‖ ≤ M)
    (hEk : ∀ k, ‖Ek k‖ ≤ M) (hfi : |fi| ≤ M*β) (hfj : |fj| ≤ M*β)
    (hΓ : ∀ k, |Γ k| ≤ M) :
    ‖-(El.comp WH) + (2*fi) • El.comp Bhi - J.comp D - WL.comp Ei +
      (2*fj) • Blo.comp Ei + fi • J.comp Ej - ∑ k : Fin 3, Γ k • J.comp (Ek k)‖ ≤
      13*M^3*β := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hβ0 : 0 ≤ β := le_trans zero_le_one hβ
  have h2Mβ : 0 ≤ 2*M*β := mul_nonneg (mul_nonneg (by norm_num) hM0) hβ0
  have hf2 (f : ℝ) (hf : |f| ≤ M*β) : |2*f| ≤ 2*M*β := by
    rw [abs_mul]; norm_num
    nlinarith [hf]
  have hA := norm_comp_le El WH M (2*M^2*β) hM0 hEl hWH
  have hB := norm_smul_le_of_le (2*fi) (El.comp Bhi) (2*M*β) (M*M) h2Mβ (hf2 fi hfi)
    (norm_comp_le El Bhi M M hM0 hEl hBhi)
  have hC := norm_comp_le J D M M hM0 hJ hD
  have hD0 := norm_comp_le WL Ei (2*M^2*β) M
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hβ0) hWL hEi
  have hE := norm_smul_le_of_le (2*fj) (Blo.comp Ei) (2*M*β) (M*M) h2Mβ (hf2 fj hfj)
    (norm_comp_le Blo Ei M M hM0 hBlo hEi)
  have hF := norm_smul_le_of_le fi (J.comp Ej) (M*β) (M*M) (mul_nonneg hM0 hβ0) hfi
    (norm_comp_le J Ej M M hM0 hJ hEj)
  have hG := norm_sum_three_smul_le Γ (fun k => J.comp (Ek k)) M (M*M) hM0 hΓ
    (fun k => norm_comp_le J (Ek k) M M hM0 hJ (hEk k))
  have hMM : M*M ≤ M^3*β := by
    have h1 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hM)]
    have h2 : M^3 ≤ M^3*β := by nlinarith [pow_nonneg hM0 3]
    nlinarith
  have hMb : M^3 ≤ M^3*β := by nlinarith [pow_nonneg hM0 3]
  exact (norm_seven_terms_le _ _ _ _ _ _ _).trans (by nlinarith [hA,hB,hC,hD0,hE,hF,hG])

private lemma norm_double_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (v : Fin 3 → Fin 3 → E) (A : ℝ) (hv : ∀ i j, ‖v i j‖ ≤ A) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, v i j‖ ≤ 9*A := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, v i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖v i j‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, A :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hv i j))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

private lemma norm_scaled_five_terms_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 ≤ r) (S D T A B : E) (s d t a b : ℝ)
    (hS : ‖S‖ ≤ s) (hD : ‖D‖ ≤ d) (hT : ‖T‖ ≤ t) (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖((r^2 • S-D)+r^2 • T)+r • A+r^3 • B‖ ≤ r^2*s+d+r^2*t+r*a+r^3*b := by
  have eS : ‖r^2 • S‖ ≤ r^2*s := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg r)
  have eT : ‖r^2 • T‖ ≤ r^2*t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left hT (sq_nonneg r)
  have eA : ‖r • A‖ ≤ r*a := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hA hr
  have eB : ‖r^3 • B‖ ≤ r^3*b := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr 3)]
    exact mul_le_mul_of_nonneg_left hB (pow_nonneg hr 3)
  have b1 := norm_sub_le (r^2 • S) D
  have b2 := norm_add_le (r^2 • S-D) (r^2 • T)
  have b3 := norm_add_le ((r^2 • S-D)+r^2 • T) (r • A)
  have b4 := norm_add_le (((r^2 • S-D)+r^2 • T)+r • A) (r^3 • B)
  linarith

attribute [local irreducible] sphereSobolevInclusionL

/-- Complete adjoint zero coefficient bound; all density, Second, angular and
quadratic terms retained, without symmetry of Q. -/
lemma norm_adjointZeroCoefficient_le (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (M β : ℝ) (hM : 1 ≤ M) (hβ : 1 ≤ β) (hr0 : 0 ≤ r) (hrβ : r*β^2 ≤ 1)
    (hJ : ‖(JL : Half →L[ℝ] Neg)‖ ≤ M) (hQ : ∀ i j, |Q i j| ≤ M)
    (hb : ∀ i, |b i| ≤ M) (hd1 : ∀ i j, |d1 i j| ≤ M*r) (hd2 : ∀ i j, |d2 i j| ≤ M*r)
    (hZ : ∀ i j, ‖Z i j‖ ≤ 13*M^3*β) (hEh : ∀ i, ‖Eh i‖ ≤ M)
    (hEl : ∀ i, ‖El i‖ ≤ M) (hAlo : ∀ i, ‖Alo i‖ ≤ M) (hAhi : ∀ i, ‖Ahi i‖ ≤ M) :
    ‖ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2 Z Eh El Alo Ahi‖ ≤
      256*M^4*r := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMr0 : 0 ≤ M*r := mul_nonneg hM0 hr0
  have hbb : β ≤ β^2 := by nlinarith
  have hrb : r*β ≤ 1 := (mul_le_mul_of_nonneg_left hbb hr0).trans hrβ
  have hr1 : r ≤ 1 := (le_mul_of_one_le_right hr0 hβ).trans hrb
  have h1 := norm_double_sum_smul_le Q Z M (13*M^3*β) hM0 hQ hZ
  have h2 := norm_double_sum_le
    (fun i j => d1 i j • (JL : Half →L[ℝ] Neg).comp (Eh j) +
      d2 i j • (JL : Half →L[ℝ] Neg).comp (Eh i))
    ((M*r)*(M*M)+(M*r)*(M*M)) (fun i j => (norm_add_le
      (d1 i j • (JL : Half →L[ℝ] Neg).comp (Eh j))
      (d2 i j • (JL : Half →L[ℝ] Neg).comp (Eh i))).trans (add_le_add
      (norm_smul_le_of_le (d1 i j) ((JL : Half →L[ℝ] Neg).comp (Eh j)) (M*r) (M*M) hMr0 (hd1 i j)
        (norm_comp_le _ _ M M hM0 hJ (hEh j)))
      (norm_smul_le_of_le (d2 i j) ((JL : Half →L[ℝ] Neg).comp (Eh i)) (M*r) (M*M) hMr0 (hd2 i j)
        (norm_comp_le _ _ M M hM0 hJ (hEh i)))))
  have h3 := norm_sum_three_smul_le b (fun i => (JL : Half →L[ℝ] Neg).comp (Eh i)) M (M*M) hM0 hb
    (fun i => norm_comp_le _ _ M M hM0 hJ (hEh i))
  have h4 := norm_double_sum_smul_le Q (fun i j => (El j).comp (Ahi i)+(Alo j).comp (Eh i))
    M (M*M+M*M) hM0 hQ (fun i j => (norm_add_le ((El j).comp (Ahi i)) ((Alo j).comp (Eh i))).trans (add_le_add
      (norm_comp_le _ _ M M hM0 (hEl j) (hAhi i)) (norm_comp_le _ _ M M hM0 (hAlo j) (hEh i))))
  have h5 := norm_double_sum_smul_le Q (fun i j => (El j).comp (Eh i)) M (M*M) hM0 hQ
    (fun i j => norm_comp_le _ _ M M hM0 (hEl j) (hEh i))
  have hz : ‖ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2 Z Eh El Alo Ahi‖ ≤
      r^2*(9*M*(13*M^3*β)) + 9*((M*r)*(M*M)+(M*r)*(M*M)) +
        r^2*(3*M*(M*M)) + r*(9*M*(M*M+M*M)) + r^3*(9*M*(M*M)) :=
    norm_scaled_five_terms_le r hr0
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j)
      (∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • (JL : Half →L[ℝ] Neg).comp (Eh j) +
        d2 i j • (JL : Half →L[ℝ] Neg).comp (Eh i)))
      (∑ i : Fin 3, b i • (JL : Half →L[ℝ] Neg).comp (Eh i))
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((El j).comp (Ahi i)+(Alo j).comp (Eh i)))
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j).comp (Eh i)) _ _ _ _ _ h1 h2 h3 h4 h5
  have r2β : r^2*β ≤ r := by
    calc
      r^2*β = r*(r*β) := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left hrb hr0
      _ = r := mul_one r
  have r2 : r^2 ≤ r := by nlinarith
  have r3 : r^3 ≤ r := by
    calc
      r^3 = r*r^2 := by ring
      _ ≤ r*1 := mul_le_mul_of_nonneg_left (r2.trans hr1) hr0
      _ = r := mul_one r
  have hM3 : 0 ≤ M^3 := pow_nonneg hM0 3
  have hM4 : 0 ≤ M^4 := pow_nonneg hM0 4
  have k1 := mul_le_mul_of_nonneg_left r2β hM4
  have k2 := mul_le_mul_of_nonneg_left r2 hM3
  have k3 := mul_le_mul_of_nonneg_left r3 hM3
  have m34 : M^3 ≤ M^4 := by
    calc
      M^3 ≤ M^3*M := le_mul_of_one_le_right hM3 hM
      _ = M^4 := by ring
  have k4 := mul_le_mul_of_nonneg_right m34 hr0
  exact hz.trans (by nlinarith [k1,k2,k3,k4,mul_nonneg hM4 hr0])
/- Generic sum and chain bounds reuse the checked G (Opus/Root) proof patterns; adjoint-specific arguments below are Root. -/
/-- Norm of the angular-map shape `½ Σ_ab c_ab T_ab`. -/
private lemma norm_half_double_sum_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : Fin 3 → Fin 3 → ℝ) (T : Fin 3 → Fin 3 → E →L[ℝ] F) (A V : ℝ) (hA : 0 ≤ A)
    (hc : ∀ a b, |c a b| ≤ A) (hT : ∀ a b, ‖T a b‖ ≤ V) :
    ‖(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤ 9*A*V := by
  have h := norm_double_sum_smul_le c T A V hA hc hT
  have hh : ‖(1/2 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> norm_num
  rw [norm_smul]
  calc
    ‖(1/2 : ℝ)‖ * ‖∑ a : Fin 3, ∑ b : Fin 3, c a b • T a b‖ ≤ 1*(9*A*V) :=
      mul_le_mul hh h (norm_nonneg _) zero_le_one
    _ = 9*A*V := one_mul _

private lemma norm_le_sum_norm {E : Type*} [SeminormedAddCommGroup E] (f : Fin 3 → E) (j : Fin 3) :
    ‖f j‖ ≤ ∑ k : Fin 3, ‖f k‖ :=
  Finset.single_le_sum (f := fun k : Fin 3 => ‖f k‖) (fun k _ => norm_nonneg _) (Finset.mem_univ j)

private lemma norm_le_double_sum_norm {E : Type*} [SeminormedAddCommGroup E]
    (f : Fin 3 → Fin 3 → E) (a b : Fin 3) :
    ‖f a b‖ ≤ ∑ a' : Fin 3, ∑ b' : Fin 3, ‖f a' b'‖ :=
  (norm_le_sum_norm (f a) b).trans
    (Finset.single_le_sum (f := fun a' : Fin 3 => ∑ b' : Fin 3, ‖f a' b'‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ a))

/-- Typed chain-rule norm calculation, without expanding concrete coefficient bodies. -/
private lemma norm_fderiv_comp_apply_le {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : F → V) (t : E → F) (x : E) (v : E) (A B D : ℝ)
    (hf : DifferentiableAt ℝ f (t x)) (ht : DifferentiableAt ℝ t x)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdf : ‖fderiv ℝ f (t x)‖ ≤ A) (hdt : ‖fderiv ℝ t x‖ ≤ B)
    (hv : ‖v‖ ≤ D) : ‖fderiv ℝ (f ∘ t) x v‖ ≤ (A*B)*D := by
  rw [fderiv_comp x hf ht]
  have hop : ‖(fderiv ℝ f (t x)).comp (fderiv ℝ t x)‖ ≤ A*B :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hdf hdt (norm_nonneg _) hA)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hop hv (norm_nonneg _) (mul_nonneg hA hB))

private lemma radius_le_one_of_small (r β : ℝ) (hr0 : 0 ≤ r) (hβ : 1 ≤ β)
    (hsmall : r*β^2 ≤ 1) : r ≤ 1 := by
  have hbb : β ≤ β^2 := by nlinarith
  have hrb := (mul_le_mul_of_nonneg_left hbb hr0).trans hsmall
  exact (le_mul_of_one_le_right hr0 hβ).trans hrb

private lemma six_mul_sq_le_big_pow (M : ℝ) (hM : 1 ≤ M) : 6*M*M ≤ 256*M^4 := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have h23 : M^2 ≤ M^3 := by
    calc
      M^2 ≤ M^2*M := le_mul_of_one_le_right (sq_nonneg M) hM
      _ = M^3 := by ring
  have h34 : M^3 ≤ M^4 := by
    calc
      M^3 ≤ M^3*M := le_mul_of_one_le_right (pow_nonneg hM0 3) hM
      _ = M^4 := by ring
  have h24 := h23.trans h34
  nlinarith [pow_nonneg hM0 4]

/-- A finite family of real constants has one positive dominating constant. -/
private lemma exists_dominating_real_family {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : ι, a i ≤ M := by
  classical
  have hs : 0 ≤ ∑ i : ι, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : ι, |a i|,by linarith,?_⟩
  intro i
  calc
    a i ≤ |a i| := le_abs_self _
    _ ≤ ∑ j : ι, |a j| := Finset.single_le_sum (f := fun j : ι => |a j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : ι, |a j| := by linarith

section Actual
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => ActualGeneratorEPairedGainedEndpoints.reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => ActualGeneratorEPairedGainedEndpoints.reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
local notation "PH" => ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => ActualHigherSAdjointCoefficientExtraction.reverseProfileLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] ActualGeneratorEPairedGainedEndpoints.reverseEHigh ActualGeneratorEPairedGainedEndpoints.reverseELow
 referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
 referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint

/-- Actual retained reverse value and AMBIENT first-jet caps, chosen before profiles. -/
theorem exists_retained_reverse_uniform_caps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ CH CE CH1 : ℝ, 1 ≤ CH ∧ 1 ≤ CE ∧ 1 ≤ CH1 ∧
      (∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH j t‖ ≤ CH) ∧
      (∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ‖EL j t‖ ≤ CE) ∧
      (∀ j : Fin 3, ∀ t ∈ ParamRoom δ, ‖fderiv ℝ (EH j) t‖ ≤ CH1) := by
  have hKP : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hELFull := compact_family_bound (ParamRoom δ) hKP (fun j : Fin 3 => EL j)
    (fun j t ht => (Cm.rev.germLow j t ht).continuousAt.continuousWithinAt)
  rcases hELFull with ⟨CE,hCE,hELc⟩
  have hEHFull := compact_family_bound (ParamRoom δ) hKP (fun j : Fin 3 => EH j)
    (fun j t ht => (Cm.rev.germHigh j t ht).continuousAt.continuousWithinAt)
  rcases hEHFull with ⟨CH,hCH,hEHc⟩
  have hdEHFull := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun j : Fin 3 => EH j) (ParamRoom δ) hKP
    (fun j t ht => Cm.rev.germHigh j t ht) 1
  rcases hdEHFull with ⟨CH1raw,hCH1raw,hdEHraw⟩
  refine ⟨CH,CE,1+CH1raw,hCH,hCE,by linarith,hEHc,hELc,?_⟩
  intro j t ht
  have h := hdEHraw 1 (le_refl _) t ht j
  rw [norm_iteratedFDeriv_one] at h
  exact h.trans (by linarith)

/-- Actual reverse profile chain-rule bound in a small concrete proof boundary.
All norm caps are the finite constants already derived on the original room. -/
lemma norm_fderiv_reverseProfileHigh_apply_le (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (x X : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CH1 CT CX : ℝ) (hCH10 : 0 ≤ CH1) (hCT0 : 0 ≤ CT)
    (hdEHc : ∀ k : Fin 3, ∀ t ∈ ParamRoom δ, ‖fderiv ℝ (EH k) t‖ ≤ CH1)
    (hT1 : ‖fderiv ℝ (Tq δr Ar p q) x‖ ≤ CT) (hX : ‖X‖ ≤ CX) :
    ‖fderiv ℝ (PH δr Ar p q j) x X‖ ≤ (CH1*CT)*CX := by
  have hEd : DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x) :=
    (Cm.rev.germHigh j _ hx).differentiableAt (by simp)
  have hDfx : ‖fderiv ℝ (EH j) ((Tq δr Ar p q) x)‖ ≤ CH1 := hdEHc j _ hx
  have hTc := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q
  have hTd : DifferentiableAt ℝ (Tq δr Ar p q) x := hTc.differentiable (by simp) x
  change ‖fderiv ℝ ((EH j) ∘ (Tq δr Ar p q)) x X‖ ≤ (CH1*CT)*CX
  exact norm_fderiv_comp_apply_le
    (E := R3) (F := ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ))) (V := Hi →L[ℝ] Half)
    (EH j) (Tq δr Ar p q) x X CH1 CT CX hEd hTd hCH10 hCT0 hDfx hT1 hX

set_option diagnostics true in
/-- Retained-data intermediate: ONE `K` for fixed admissible `g2`, chosen before
`δr,Ar,p,q,x`; every zero-base term (derivative, connection, angular, drift,
quadratic) is bounded by `K·R(x)`. -/
theorem exists_actual_adjoint_zero_coefficient_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x * (actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      ‖CZ g2 δr Ar p q x‖ ≤ K * referenceRadius δr Ar p L x := by
  classical
  -- (1) compact sets, all fixed before every profile
  have hKx : IsCompact (closedBall y0 ρ) := isCompact_closedBall y0 ρ
  have hKP : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hKQ : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) := isCompact_Icc.prod hKx
  -- (2) existing parameter-jet cap
  have hJetFull := exists_reference_radius_parameter_uniform_jet_bounds g hg L hL
    (closedBall y0 ρ) hKx
  rcases hJetFull with ⟨CT,hCT0,hCT⟩
  -- (3) existing log-radius first jet
  have hLogFull := exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg
    (closedBall y0 ρ) hKx L hL
  rcases hLogFull with ⟨J1,J2,hJ10,_hJ20,hJ1⟩
  -- (4) existing horizontal geometry: connection coefficients
  have hGeoFull := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds g hg L
    (closedBall y0 ρ) hKx
  rcases hGeoFull with ⟨MG,hMG,hGeo⟩
  -- (5-6) reuse the separately checked original reverse value/ambient-jet caps
  have hCapsFull := exists_retained_reverse_uniform_caps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm
  rcases hCapsFull with ⟨CH,CE,CH1,hCH,hCE,hCH1,hEHc,hELc,hdEHc⟩
  -- (7) frame vectors
  have hXFull := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) hKQ
    (fun i : Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  rcases hXFull with ⟨CX,hCX,hXc⟩
  -- (8) after g2: drift and principal coefficients
  have hbFull := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) hKQ
    (fun i : Fin 3 => fun t : ℝ × R3 => normalizedSecondDriftFrameJoint g g2 L i t)
    (fun i => (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.continuousOn)
  rcases hbFull with ⟨Cb,hCb,hbc⟩
  have hQFull := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    g L y0 ρ hg g2 hg2
  rcases hQFull with ⟨CQ,hCQ,hQc⟩
  have hDensityFull := exists_density_derivative_uniform_radius_bound g hg g2 hg2 L y0 ρ
  rcases hDensityFull with ⟨KD,hKD0,hDensity⟩
  -- (9) fixed bounded operators
  let Ahi : Fin 3 → Hi →L[ℝ] Half := loweringHigh hF hO hD
  let Alo : Fin 3 → Half →L[ℝ] Neg := loweringLow hF hO hD
  let operatorBudget : Fin 7 → ℝ := ![
    ‖(JL : Half →L[ℝ] Neg)‖,
    ‖(sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)‖,
    ‖(sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)‖,
    ∑ j : Fin 3, ‖Ahi j‖, ∑ j : Fin 3, ‖Alo j‖,
    ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (3/2 : ℝ) a' b'‖,
    ∑ a' : Fin 3, ∑ b' : Fin 3, ‖sphereSobolevRotationL (1/2 : ℝ) a' b'‖]
  have hOperatorBudget := exists_dominating_real_family operatorBudget
  rcases hOperatorBudget with ⟨NC,hNC,hNdom⟩
  have hNC0 : 0 ≤ NC := le_trans zero_le_one hNC
  have hJN : ‖(JL : Half →L[ℝ] Neg)‖ ≤ NC := hNdom 0
  have hBhN : ‖(sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)‖ ≤ NC := hNdom 1
  have hBlN : ‖(sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)‖ ≤ NC := hNdom 2
  have hAhN (j : Fin 3) : ‖Ahi j‖ ≤ NC := (norm_le_sum_norm Ahi j).trans (hNdom 3)
  have hAlN (j : Fin 3) : ‖Alo j‖ ≤ NC := (norm_le_sum_norm Alo j).trans (hNdom 4)
  have hRhN (a' b' : Fin 3) : ‖sphereSobolevRotationL (3/2 : ℝ) a' b'‖ ≤ NC :=
    (norm_le_double_sum_norm (fun a b => sphereSobolevRotationL (3/2 : ℝ) a b) a' b').trans (hNdom 5)
  have hRlN (a' b' : Fin 3) : ‖sphereSobolevRotationL (1/2 : ℝ) a' b'‖ ≤ NC :=
    (norm_le_double_sum_norm (fun a b => sphereSobolevRotationL (1/2 : ℝ) a b) a' b').trans (hNdom 6)
  -- (10) the single dominating constant, fixed before every profile
  have hMG0 : 0 ≤ MG := le_trans zero_le_one hMG
  have hCT0' : 0 ≤ CT := le_of_lt hCT0
  have hJ10' : 0 ≤ J1 := le_of_lt hJ10
  have hCX0 : 0 ≤ CX := le_trans zero_le_one hCX
  have hCH10 : 0 ≤ CH1 := le_trans zero_le_one hCH1
  let budget : Fin 10 → ℝ := ![CQ,Cb,CH,CE,NC,9*MG*NC,MG,CH1*CT*CX,J1*CX,KD]
  have hBudget := exists_dominating_real_family budget
  rcases hBudget with ⟨M,hM,hDom⟩
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hQM : CQ ≤ M := hDom 0
  have hbM : Cb ≤ M := hDom 1
  have hHM : CH ≤ M := hDom 2
  have hEM : CE ≤ M := hDom 3
  have hNM : NC ≤ M := hDom 4
  have hOM : 9*MG*NC ≤ M := hDom 5
  have hGM : MG ≤ M := hDom 6
  have hDM : CH1*CT*CX ≤ M := hDom 7
  have hfM : J1*CX ≤ M := hDom 8
  have hKDM : KD ≤ M := hDom 9
  refine ⟨256*M^4,mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) (pow_nonneg hM0 4),?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ hsmall
  -- profile data
  have hxK : x ∈ closedBall y0 ρ := hx.1.2.1
  have hqx : (q,x) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ := ⟨hq,hxK⟩
  have hr0 : 0 ≤ referenceRadius δr Ar p L x := le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)
  have hβ0 : 0 ≤ actualReferenceBeta g L q δr Ar p x := le_trans zero_le_one hβ
  have hdR : ‖fderiv ℝ (referenceRadius δr Ar p L) x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.2
  -- parameter jet: ‖d t_R(x)‖ ≤ CT
  have hjet := hCT q hq δr hδr hδr1 Ar hAr p hp x hxK hβ hsmall hdR
  have hjet1 : ‖iteratedFDeriv ℝ 1 (Tq δr Ar p q) x‖ ≤ CT := hjet.2.1
  have hT1 : ‖fderiv ℝ (Tq δr Ar p q) x‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one]; exact hjet1
  -- geometry at (q,x)
  have hG := hGeo q hq x hxK
  have hΓ (i k j : Fin 3) : |referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j| ≤ M := (hG.2.2.2 i k j).trans hGM
  have hXn (i : Fin 3) : ‖referenceMetricGramFrame g L (q,x) i‖ ≤ CX := hXc i (q,x) hqx
  have hOhi (i : Fin 3) : ‖referenceHighHorizontalAngularL g L q x i‖ ≤ M := by
    have h : ‖referenceHighHorizontalAngularL g L q x i‖ ≤ 9*MG*NC := by
      unfold referenceHighHorizontalAngularL
      exact norm_half_double_sum_le
        (fun a' b' => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a' b')
        (fun a' b' => sphereSobolevRotationL (3/2 : ℝ) a' b') MG NC hMG0
        (fun a' b' => hG.2.2.2 i a' b') hRhN
    exact h.trans hOM
  have hOlo (i : Fin 3) : ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ M := by
    have h : ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ 9*MG*NC := by
      unfold referenceLowerHorizontalAngularL
      exact norm_half_double_sum_le
        (fun a' b' => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a' b')
        (fun a' b' => sphereSobolevRotationL (1/2 : ℝ) a' b') MG NC hMG0
        (fun a' b' => hG.2.2.2 i a' b') hRlN
    exact h.trans hOM
  -- frame log derivative: |f_i| ≤ J1·CX·β ≤ M β
  have hlog : ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖ ≤
      J1 * actualReferenceBeta g L q δr Ar p x :=
    (hJ1 q hq δr hδr hδr1 Ar hAr p hp x hxK).1
  have hf (k : Fin 3) : |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x k| ≤
      M * actualReferenceBeta g L q δr Ar p x := by
    have he : referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x k =
        fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x
          (referenceMetricGramFrame g L (q,x) k) := by
      unfold referenceRadiusHorizontalLogDerivative
      rw [ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x k]
    rw [he,← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖ *
          ‖referenceMetricGramFrame g L (q,x) k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (J1 * actualReferenceBeta g L q δr Ar p x) * CX :=
        mul_le_mul hlog (hXn k) (norm_nonneg _) (mul_nonneg hJ10' hβ0)
      _ = (J1*CX) * actualReferenceBeta g L q δr Ar p x := by ring
      _ ≤ M * actualReferenceBeta g L q δr Ar p x := mul_le_mul_of_nonneg_right hfM hβ0
  -- actual profile operators
  have hPHn (k : Fin 3) : ‖PH δr Ar p q k x‖ ≤ M :=
    (hEHc k _ hx).trans hHM
  have hPLn (i : Fin 3) : ‖PL δr Ar p q x i‖ ≤ M :=
    (hELc i _ hx).trans hEM
  -- differentiated profile along X_i, by the chain rule
  have hDn (i j : Fin 3) :
      ‖fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i)‖ ≤ M :=
    (norm_fderiv_reverseProfileHigh_apply_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm δr Ar p hδr hAr q j x (referenceMetricGramFrame g L (q,x) i) hx
      CH1 CT CX hCH10 hCT0' hdEHc hT1 (hXn i)).trans hDM
  have hQn (i j : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M :=
    ((hQc q hq x hxK i j).1).trans hQM
  have hbn (i : Fin 3) : |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M := by
    have h := hbc i (q,x) hqx
    rw [Real.norm_eq_abs] at h
    exact h.trans hbM
  have hWH (i : Fin 3) :
      ‖ActualHigherSCoefficientExtraction.weightedHighZero g L q (referenceRadius δr Ar p L) x i‖ ≤
        2*M^2*actualReferenceBeta g L q δr Ar p x :=
    norm_weighted_zero_le (referenceHighHorizontalAngularL g L q x i)
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)
      M (actualReferenceBeta g L q δr Ar p x) hM hβ (hOhi i) (hBhN.trans hNM) (hf i)
  have hWL (i : Fin 3) :
      ‖ActualHigherSCoefficientExtraction.weightedLowerZero g L q (referenceRadius δr Ar p L) x i‖ ≤
        2*M^2*actualReferenceBeta g L q δr Ar p x :=
    norm_weighted_zero_le (referenceLowerHorizontalAngularL g L q x i)
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)
      M (actualReferenceBeta g L q δr Ar p x) hM hβ (hOlo i) (hBlN.trans hNM) (hf i)
  have hZ (i j : Fin 3) :
      ‖ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q (referenceRadius δr Ar p L)
        (PH δr Ar p q) (PL δr Ar p q x) x i j‖ ≤ 13*M^3*actualReferenceBeta g L q δr Ar p x :=
    norm_adjoint_second_shape_le (JL : Half →L[ℝ] Neg)
      (fderiv ℝ (PH δr Ar p q i) x (referenceMetricGramFrame g L (q,x) j))
      (ActualHigherSCoefficientExtraction.weightedHighZero g L q (referenceRadius δr Ar p L) x i)
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
      (PL δr Ar p q x j)
      (ActualHigherSCoefficientExtraction.weightedLowerZero g L q (referenceRadius δr Ar p L) x j)
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
      (PH δr Ar p q i x) (PH δr Ar p q j x) (fun k => PH δr Ar p q k x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x j)
      (fun k => referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j)
      M (actualReferenceBeta g L q δr Ar p x) hM hβ
      (hJN.trans hNM) (hDn j i) (hWH i) (hBhN.trans hNM) (hPLn j) (hWL j)
      (hBlN.trans hNM) (hPHn i) (hPHn j) hPHn (hf i) (hf j) (fun k => hΓ i k j)
  have hr1 : referenceRadius δr Ar p L x ≤ 1 :=
    radius_le_one_of_small _ _ hr0 hβ hsmall
  let d1 := fun i j : Fin 3 => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
    (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x / referenceDensityFamily g L (q,x)
  let d2 := fun i j : Fin 3 => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j
    (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x / referenceDensityFamily g L (q,x)
  have hd1 (i j : Fin 3) : |d1 i j| ≤ M*referenceRadius δr Ar p L x :=
    (hDensity δr Ar p hδr hAr q hq x hxK hr1 hdR i j i).trans
      (mul_le_mul_of_nonneg_right hKDM hr0)
  have hd2 (i j : Fin 3) : |d2 i j| ≤ M*referenceRadius δr Ar p L x :=
    (hDensity δr Ar p hδr hAr q hq x hxK hr1 hdR i j j).trans
      (mul_le_mul_of_nonneg_right hKDM hr0)
  have hZero : ‖CZ g2 δr Ar p q x‖ ≤ 256*M^4*referenceRadius δr Ar p L x :=
    norm_adjointZeroCoefficient_le (referenceRadius δr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)) d1 d2
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q (referenceRadius δr Ar p L)
        (PH δr Ar p q) (PL δr Ar p q x) x)
      (fun i => PH δr Ar p q i x) (PL δr Ar p q x) Alo Ahi
      M (actualReferenceBeta g L q δr Ar p x) hM hβ hr0 hsmall
      (hJN.trans hNM) hQn hbn hd1 hd2 hZ hPHn hPLn
      (fun i => (hAlN i).trans hNM) (fun i => (hAhN i).trans hNM)
  exact hZero

/-- Actual reverse first coefficient cap, independently of the derivative/zero proof. -/
theorem exists_actual_adjoint_first_coefficient_uniform_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
      ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ → ∀ m : Fin 3,
      ‖ActualHigherSAdjointCoefficientExtraction.higherSAdjointFirstFrameCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 δr Ar p q x m‖ ≤
          K*(referenceRadius δr Ar p L x)^2 := by
  have hc := exists_retained_reverse_uniform_caps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm
  rcases hc with ⟨CH,CE,CH1,hCH,hCE,hCH1,hEHc,hELc,hdEHc⟩
  have hQfull := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound g L y0 ρ hg g2 hg2
  rcases hQfull with ⟨CQ,hCQ,hQc⟩
  have hCQ0 : 0 ≤ CQ := le_trans zero_le_one hCQ
  have hCE0 : 0 ≤ CE := le_trans zero_le_one hCE
  refine ⟨6*CQ*CE,mul_nonneg (mul_nonneg (by norm_num) hCQ0) hCE0,?_⟩
  intro δr Ar p q hq x hx m
  have hPL (j : Fin 3) : ‖PL δr Ar p q x j‖ ≤ CE := hELc j _ hx
  have hQ (i j : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ :=
    (hQc q hq x hx.1.2.1 i j).1
  have h := ActualHigherSCoefficientBounds.norm_firstFrameCoefficient_le (referenceRadius δr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x) (PL δr Ar p q x) CQ CE hCQ0 hQ hPL m
  change ‖-(ActualHigherSCoefficientExtraction.firstFrameCoefficient (referenceRadius δr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x) (PL δr Ar p q x) m)‖ ≤ _
  exact (norm_neg _).le.trans h

/-- Both exact actual coefficient caps with one profile-independent constant. -/
theorem exists_actual_adjoint_coefficient_uniform_bounds (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x * (actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      (∀ m : Fin 3, ‖ActualHigherSAdjointCoefficientExtraction.higherSAdjointFirstFrameCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 δr Ar p q x m‖ ≤
          K * (referenceRadius δr Ar p L x)^2) ∧
      ‖CZ g2 δr Ar p q x‖ ≤ K * referenceRadius δr Ar p L x := by
  have hz := exists_actual_adjoint_zero_coefficient_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hL g2 hg2
  rcases hz with ⟨KZ,hKZ,hZero⟩
  have hb := exists_actual_adjoint_first_coefficient_uniform_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2
  rcases hb with ⟨KB,hKB,hFirst⟩
  have hKBsum : KB ≤ KB+KZ := by linarith
  have hKZsum : KZ ≤ KB+KZ := by linarith
  refine ⟨KB+KZ,add_nonneg hKB hKZ,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ hsmall
  refine ⟨?_,?_⟩
  · intro m
    exact (hFirst δr Ar p q hq x hx m).trans
      (mul_le_mul_of_nonneg_right hKBsum (sq_nonneg (referenceRadius δr Ar p L x)))
  · exact (hZero δr Ar p hδr hδr1 hAr hp q hq x hx hβ hsmall).trans
      (mul_le_mul_of_nonneg_right hKZsum (le_of_lt (referenceRadius_pos δr Ar p L x hδr hAr)))

/-- Actual retained radius before g2, with both first/zero coefficient bounds and
constants before every profile. Original guard and witness are preserved. -/
theorem exists_retained_actual_adjoint_coefficient_bounds (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, Jac z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x * (actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      (∀ m : Fin 3, ‖ActualHigherSAdjointCoefficientExtraction.higherSAdjointFirstFrameCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 δr Ar p q x m‖ ≤
          K * (referenceRadius δr Ar p L x)^2) ∧
      ‖CZ g2 δr Ar p q x‖ ≤ K * referenceRadius δr Ar p L x := by
  have hFull := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,Cm,hJac⟩
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_adjoint_coefficient_uniform_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hL g2 hg2

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointCoefficientBounds
