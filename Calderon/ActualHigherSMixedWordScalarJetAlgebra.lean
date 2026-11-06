import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.CompactSmoothJetBounds
import Calderon.ActualHigherSZeroCoefficientBounds

/-! Scalar jet algebra for the mixed cubic estimate. The uniform caps are produced
elsewhere. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
open EnergyBridge ConnectionError ConformalDepth ReferenceWeightedApproximation
  ActualHigherSQuadraticZeroWords ActualNormalizedSecondMetricDrift SmoothMetricFrame MovingFrameConnection

/-- A local scalar first-jet estimate, used only to bound the coefficients. -/
structure ScalarPointJet (f : R3 → ℝ) (x : R3) (A B : ℝ) : Prop where
  differentiable : DifferentiableAt ℝ f x
  value : |f x| ≤ A
  derivative : ‖fderiv ℝ f x‖ ≤ B

lemma ScalarPointJet.value_nonneg {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) : 0 ≤ A := (abs_nonneg _).trans h.value
lemma ScalarPointJet.derivative_nonneg {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) : 0 ≤ B := (norm_nonneg _).trans h.derivative

lemma ScalarPointJet.mono {f : R3 → ℝ} {x : R3} {A B C D : ℝ}
    (h : ScalarPointJet f x A B) (hAC : A ≤ C) (hBD : B ≤ D) : ScalarPointJet f x C D :=
  ⟨h.differentiable, h.value.trans hAC, h.derivative.trans hBD⟩

lemma ScalarPointJet.mul {f g : R3 → ℝ} {x : R3} {A B C D : ℝ}
    (hf : ScalarPointJet f x A B) (hg : ScalarPointJet g x C D) :
    ScalarPointJet (fun y => f y*g y) x (A*C) (A*D+C*B) := by
  refine ⟨hf.differentiable.mul hg.differentiable, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul hf.value hg.value (abs_nonneg _) hf.value_nonneg
  · rw [fderiv_fun_mul hf.differentiable hg.differentiable]
    calc
      _ ≤ ‖f x • fderiv ℝ g x‖+‖g x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| *‖fderiv ℝ g x‖+|g x| *‖fderiv ℝ f x‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ A*D+C*B := add_le_add
        (mul_le_mul hf.value hg.derivative (norm_nonneg _) hf.value_nonneg)
        (mul_le_mul hg.value hf.derivative (norm_nonneg _) hg.value_nonneg)

lemma ScalarPointJet.const_mul {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) (c : ℝ) :
    ScalarPointJet (fun y => c*f y) x (|c| *A) (|c| *B) := by
  refine ⟨h.differentiable.const_mul c, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h.value (abs_nonneg _)
  · rw [fderiv_const_mul h.differentiable c]
    simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left h.derivative (abs_nonneg c)

lemma ScalarPointJet.pow_two {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) : ScalarPointJet (fun y => f y^2) x (A^2) (2*A*B) := by
  have hh := h.mul h
  have hFun : (fun y => f y*f y) = (fun y => f y^2) := by funext y; ring
  rw [hFun] at hh
  have hA : A*A = A^2 := by ring
  have hB : A*B+A*B = 2*A*B := by ring
  simpa only [hA,hB] using hh

lemma ScalarPointJet.pow_three {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) : ScalarPointJet (fun y => f y^3) x (A^3) (3*A^2*B) := by
  have hh := h.pow_two.mul h
  have hFun : (fun y => f y^2*f y) = (fun y => f y^3) := by funext y; ring
  rw [hFun] at hh
  have hA : A^2*A = A^3 := by ring
  have hB : A^2*B+A*(2*A*B) = 3*A^2*B := by ring
  simpa only [hA, hB] using hh

lemma ScalarPointJet.div_two {f : R3 → ℝ} {x : R3} {A B : ℝ}
    (h : ScalarPointJet f x A B) : ScalarPointJet (fun y => f y/2) x A B := by
  have hh := h.const_mul (1/2 : ℝ)
  have hFun : (fun y => (1/2 : ℝ)*f y) = (fun y => f y/2) := by funext y; ring
  rw [hFun] at hh
  apply hh.mono
  · norm_num
    linarith only [h.value_nonneg]
  · norm_num
    linarith only [h.derivative_nonneg]

lemma norm_fderiv_apply_field_le (R : R3 → ℝ) (X : R3 → R3) (x : R3)
    (hR : DifferentiableAt ℝ (fderiv ℝ R) x) (hX : DifferentiableAt ℝ X x) :
    ‖fderiv ℝ (fun y => fderiv ℝ R y (X y)) x‖ ≤
      ‖fderiv ℝ R x‖*‖fderiv ℝ X x‖+‖fderiv ℝ (fderiv ℝ R) x‖*‖X x‖ := by
  rw [fderiv_clm_apply hR hX]
  calc
    _ ≤ ‖(fderiv ℝ R x).comp (fderiv ℝ X x)‖+
        ‖(fderiv ℝ (fderiv ℝ R) x).flip (X x)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ R x‖*‖fderiv ℝ X x‖+
        ‖(fderiv ℝ (fderiv ℝ R) x).flip‖*‖X x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ = _ := by rw [ContinuousLinearMap.opNorm_flip]

lemma scalarPointJet_derivative_frame (R : R3 → ℝ) (X : R3 → R3) (x : R3)
    (hR : ContDiff ℝ ∞ R) (hX : DifferentiableAt ℝ X x)
    (r beta M : ℝ) (hr : 0 ≤ r) (hb : 1 ≤ beta) (hM : 1 ≤ M)
    (hR1 : ‖fderiv ℝ R x‖ ≤ M*r*beta)
    (hR2 : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M*r*beta^2)
    (hX0 : ‖X x‖ ≤ M) (hX1 : ‖fderiv ℝ X x‖ ≤ M) :
    ScalarPointJet (fun y => fderiv ℝ R y (X y)) x (M^2*r*beta) (2*M^2*r*beta^2) := by
  have hR' : ContDiff ℝ ∞ (fderiv ℝ R) := hR.fderiv_right (by simp)
  have hdR : DifferentiableAt ℝ (fderiv ℝ R) x := hR'.differentiable (by simp) x
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  refine ⟨hdR.clm_apply hX, ?_, ?_⟩
  · calc
      _ ≤ ‖fderiv ℝ R x‖*‖X x‖ := by simpa only [Real.norm_eq_abs] using (fderiv ℝ R x).le_opNorm (X x)
      _ ≤ (M*r*beta)*M := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖fderiv ℝ R x‖*‖fderiv ℝ X x‖+‖fderiv ℝ (fderiv ℝ R) x‖*‖X x‖ :=
        norm_fderiv_apply_field_le R X x hdR hX
      _ ≤ (M*r*beta)*M+(M*r*beta^2)*M := by gcongr
      _ = M^2*r*beta+M^2*r*beta^2 := by ring
      _ ≤ M^2*r*beta^2+M^2*r*beta^2 := add_le_add
        (mul_le_mul_of_nonneg_left (by nlinarith : beta ≤ beta^2) (mul_nonneg (sq_nonneg M) hr)) le_rfl
      _ = _ := by ring

def clearedWordCoefficient (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ)
    (X : Fin 3 → R3 → R3) (Γ : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (z : ZeroWord) (x : R3) : ℝ :=
  let i := z.1.1
  let j := z.1.2
  match z.2 with
  | Sum.inl ab => (R x^2/2)*Q i j x*Γ i ab.1 ab.2 x
  | Sum.inr (Sum.inl ab) => (R x^2/2)*Q i j x*Γ j ab.1 ab.2 x
  | Sum.inr (Sum.inr m) =>
    if m = 0 then R x*Q i j x*(fderiv ℝ R x (X i x)) else
    if m = 1 then R x*Q i j x*(fderiv ℝ R x (X j x)) else
    if m = 2 then R x*Q i j x else
    if m = 3 then R x*Q i j x else R x^3*Q i j x

def scalarWordConstant (M : ℝ) : ℝ := 1+2*M+5*M^2+5*M^3+M^4

theorem scalarPointJet_clearedWordCoefficient
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ)
    (X : Fin 3 → R3 → R3) (Γ : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (x : R3) (beta M : ℝ)
    (hr : 0 ≤ R x) (hb : 1 ≤ beta) (hM : 1 ≤ M) (hs : R x*beta^2 ≤ 1)
    (hR1 : ‖fderiv ℝ R x‖ ≤ M*R x*beta)
    (hR2 : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M*R x*beta^2)
    (hQ : ∀ i j, ScalarPointJet (Q i j) x M M)
    (hΓ : ∀ i a b, ScalarPointJet (Γ i a b) x M M)
    (hX : ∀ i, DifferentiableAt ℝ (X i) x ∧ ‖X i x‖ ≤ M ∧ ‖fderiv ℝ (X i) x‖ ≤ M)
    (z : ZeroWord) :
    ScalarPointJet (clearedWordCoefficient R Q X Γ z) x
      (scalarWordConstant M*R x) (scalarWordConstant M*R x*beta) := by
  let r := R x
  let Cw := scalarWordConstant M
  have hr0 : 0 ≤ r := hr
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM20 : 0 ≤ M^2 := sq_nonneg M
  have hM30 : 0 ≤ M^3 := pow_nonneg hM0 3
  have hM40 : 0 ≤ M^4 := pow_nonneg hM0 4
  have hb2 : 1 ≤ beta^2 := by nlinarith [sq_nonneg (beta-1)]
  have hbb2 : beta ≤ beta^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hb) hb0
    nlinarith only [hprod]
  have hr1 : r ≤ 1 := (show r ≤ r*beta^2 from by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hr0).trans hs
  have hrb : r*beta ≤ 1 := (mul_le_mul_of_nonneg_left hbb2 hr0).trans hs
  have hr2r : r^2 ≤ r := by nlinarith
  have hr2rb : r^2 ≤ r*beta := hr2r.trans (by nlinarith)
  have hr2brb : r^2*beta ≤ r*beta := mul_le_mul_of_nonneg_right hr2r hb0
  have hr2br : r^2*beta ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hrb hr0]
  have hr2b2rb : r^2*beta^2 ≤ r*beta := by nlinarith [mul_le_mul_of_nonneg_left hrb (mul_nonneg hr0 hb0)]
  have hr3r : r^3 ≤ r := by nlinarith [mul_le_mul_of_nonneg_right hr2r hr0]
  have hr3rb : r^3 ≤ r*beta := hr3r.trans (by nlinarith)
  have hr3brb : r^3*beta ≤ r*beta := mul_le_mul_of_nonneg_right hr3r hb0
  have hCM : M ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCM2 : M^2 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCM3 : M^3 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCRot : 2*M^2+2*M^3 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCDeg : 3*M^3+M^4 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCRaise : M+M^2 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hCDouble : M+3*M^2 ≤ Cw := by dsimp [Cw, scalarWordConstant]; nlinarith
  have hRJ : ScalarPointJet R x r (M*r*beta) :=
    ⟨hR.differentiable (by simp) x, by
      change |R x| ≤ R x
      exact le_of_eq (abs_of_nonneg hr), hR1⟩
  have hV (i : Fin 3) : ScalarPointJet (fun y => fderiv ℝ R y (X i y)) x
      (M^2*r*beta) (2*M^2*r*beta^2) :=
    scalarPointJet_derivative_frame R (X i) x hR (hX i).1 r beta M hr0 hb hM hR1 hR2 (hX i).2.1 (hX i).2.2
  have hRot (i j k a b : Fin 3) : ScalarPointJet
      (fun y => (R y^2/2)*Q i j y*Γ k a b y) x (Cw*r) (Cw*r*beta) := by
    apply (((hRJ.pow_two.div_two).mul (hQ i j)).mul (hΓ k a b)).mono
    · calc
        _ = M^2*r^2 := by ring
        _ ≤ M^2*r := mul_le_mul_of_nonneg_left hr2r hM20
        _ ≤ Cw*r := mul_le_mul_of_nonneg_right hCM2 hr0
    · calc
        _ = 2*M^2*r^2+2*M^3*(r^2*beta) := by ring
        _ ≤ 2*M^2*(r*beta)+2*M^3*(r*beta) := add_le_add
          (mul_le_mul_of_nonneg_left hr2rb (by positivity))
          (mul_le_mul_of_nonneg_left hr2brb (by positivity))
        _ = (2*M^2+2*M^3)*(r*beta) := by ring
        _ ≤ Cw*(r*beta) := mul_le_mul_of_nonneg_right hCRot (mul_nonneg hr0 hb0)
        _ = Cw*r*beta := by ring
  have hDegree (i j k : Fin 3) : ScalarPointJet
      (fun y => R y*Q i j y*(fderiv ℝ R y (X k y))) x (Cw*r) (Cw*r*beta) := by
    apply ((hRJ.mul (hQ i j)).mul (hV k)).mono
    · calc
        _ = M^3*(r^2*beta) := by ring
        _ ≤ M^3*r := mul_le_mul_of_nonneg_left hr2br hM30
        _ ≤ Cw*r := mul_le_mul_of_nonneg_right hCM3 hr0
    · calc
        _ = 2*M^3*(r^2*beta^2)+M^3*(r^2*beta)+M^4*(r^2*beta^2) := by ring
        _ ≤ 2*M^3*(r*beta)+M^3*(r*beta)+M^4*(r*beta) :=
          add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hr2b2rb (by positivity))
            (mul_le_mul_of_nonneg_left hr2brb hM30))
            (mul_le_mul_of_nonneg_left hr2b2rb hM40)
        _ = (3*M^3+M^4)*(r*beta) := by ring
        _ ≤ Cw*(r*beta) := mul_le_mul_of_nonneg_right hCDeg (mul_nonneg hr0 hb0)
        _ = Cw*r*beta := by ring
  have hRaise (i j : Fin 3) : ScalarPointJet (fun y => R y*Q i j y) x (Cw*r) (Cw*r*beta) := by
    apply (hRJ.mul (hQ i j)).mono
    · calc
        _ = M*r := mul_comm _ _
        _ ≤ Cw*r := mul_le_mul_of_nonneg_right hCM hr0
    · calc
        _ = M*r+M^2*(r*beta) := by ring
        _ ≤ M*(r*beta)+M^2*(r*beta) := add_le_add
          (mul_le_mul_of_nonneg_left (by nlinarith : r ≤ r*beta) hM0) le_rfl
        _ = (M+M^2)*(r*beta) := by ring
        _ ≤ Cw*(r*beta) := mul_le_mul_of_nonneg_right hCRaise (mul_nonneg hr0 hb0)
        _ = Cw*r*beta := by ring
  have hDouble (i j : Fin 3) : ScalarPointJet (fun y => R y^3*Q i j y) x (Cw*r) (Cw*r*beta) := by
    apply (hRJ.pow_three.mul (hQ i j)).mono
    · calc
        _ = M*r^3 := mul_comm _ _
        _ ≤ M*r := mul_le_mul_of_nonneg_left hr3r hM0
        _ ≤ Cw*r := mul_le_mul_of_nonneg_right hCM hr0
    · calc
        _ = M*r^3+3*M^2*(r^3*beta) := by ring
        _ ≤ M*(r*beta)+3*M^2*(r*beta) := add_le_add
          (mul_le_mul_of_nonneg_left hr3rb hM0)
          (mul_le_mul_of_nonneg_left hr3brb (by positivity))
        _ = (M+3*M^2)*(r*beta) := by ring
        _ ≤ Cw*(r*beta) := mul_le_mul_of_nonneg_right hCDouble (mul_nonneg hr0 hb0)
        _ = Cw*r*beta := by ring
  rcases z with ⟨⟨i,j⟩, kind⟩
  cases kind with
  | inl ab => exact hRot i j i ab.1 ab.2
  | inr kind =>
    cases kind with
    | inl ab => exact hRot i j j ab.1 ab.2
    | inr m =>
      change ScalarPointJet (fun y =>
        if m = 0 then R y*Q i j y*(fderiv ℝ R y (X i y)) else
        if m = 1 then R y*Q i j y*(fderiv ℝ R y (X j y)) else
        if m = 2 then R y*Q i j y else
        if m = 3 then R y*Q i j y else R y^3*Q i j y) x _ _
      split_ifs
      · exact hDegree i j i
      · exact hDegree i j j
      · exact hRaise i j
      · exact hRaise i j
      · exact hDouble i j

theorem exists_finite_joint_first_caps {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ι → (ℝ × R3) → V) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (S : Set (ℝ × R3)) (hS : IsCompact S) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i z, z ∈ S → ‖f i z‖ ≤ M ∧ ‖fderiv ℝ (f i) z‖ ≤ M := by
  classical
  choose Ci hCi using fun i : ι => exists_compact_smooth_jet_bound_two (f i) (hf i) S hS
  let M := 1+∑ i : ι, Ci i
  have hSum : 0 ≤ ∑ i : ι, Ci i := Finset.sum_nonneg (fun i _ => (hCi i).1.le)
  refine ⟨M, by dsimp [M]; linarith, ?_⟩
  intro i z hz
  have hOne : Ci i ≤ M := (Finset.single_le_sum (fun j _ => (hCi j).1.le) (Finset.mem_univ i)).trans (by dsimp [M]; linarith)
  have h0 : ‖f i z‖ ≤ Ci i := by
    simpa only [norm_iteratedFDeriv_zero] using (hCi i).2 0 (by omega) z hz
  have h1 : ‖fderiv ℝ (f i) z‖ ≤ Ci i := by
    simpa only [norm_iteratedFDeriv_one] using (hCi i).2 1 (by omega) z hz
  exact ⟨h0.trans hOne, h1.trans hOne⟩

lemma norm_fderiv_fixed_slice_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × R3) → V) (hf : ContDiff ℝ ∞ f) (q : ℝ) (x : R3) :
    ‖fderiv ℝ (fun y : R3 => f (q,y)) x‖ ≤ ‖fderiv ℝ f (q,x)‖ := by
  let A : R3 →L[ℝ] ℝ × R3 := (0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)
  have hA : HasFDerivAt (fun y : R3 => (q,y)) A x :=
    (hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)
  have hF : HasFDerivAt (fun y : R3 => f (q,y)) ((fderiv ℝ f (q,x)).comp A) x :=
    (hf.differentiable (by simp) (q,x)).hasFDerivAt.comp x hA
  rw [hF.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  calc
    _ ≤ ‖fderiv ℝ f (q,x)‖*‖A v‖ := (fderiv ℝ f (q,x)).le_opNorm (A v)
    _ = ‖fderiv ℝ f (q,x)‖*‖v‖ := by
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, Prod.norm_mk,
        norm_zero, max_eq_right (norm_nonneg v)]

lemma radius_mul_horizontalLogDerivative_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (hpos : ∀ y, 0 < R y)
    (i : Fin 3) (x : R3) :
    R x*referenceRadiusHorizontalLogDerivative g L q R x i =
      fderiv ℝ R x (referenceMetricGramFrame g L (q,x) i) := by
  have hLog := ((hR.differentiable (by simp) x).hasFDerivAt.log (ne_of_gt (hpos x))).fderiv
  unfold referenceRadiusHorizontalLogDerivative
  rw [ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x i, hLog]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hpos x)), one_mul]

lemma actualWordCoefficient_eq_cleared (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (z : ZeroWord) :
    (fun x => actualWordCoefficient g L g2 dr Ar p q x z) =
      clearedWordCoefficient (referenceRadius dr Ar p L)
        (fun i j x => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
        (fun i x => referenceMetricGramFrame g L (q,x) i)
        (fun i a b x => referenceFrameConnectionCoefficient g L q x
          (referenceMetricGramFrame g L (q,x) i) a b) z := by
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hpos (x : R3) : 0 < referenceRadius dr Ar p L x := referenceRadius_pos dr Ar p L x hdr hAr
  have hf (i : Fin 3) (x : R3) := radius_mul_horizontalLogDerivative_eq g hg L q
    (referenceRadius dr Ar p L) hR hpos i x
  funext x
  rcases z with ⟨⟨i,j⟩, kind⟩
  cases kind with
  | inl ab =>
    simp only [actualWordCoefficient, wordCoefficient, clearedWordCoefficient,
      ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
      ActualHigherSZeroCoefficientFactorisation.parameterGramFrame, ActualHigherSFormation.higherSParam]
  | inr kind =>
    cases kind with
    | inl ab =>
      simp only [actualWordCoefficient, wordCoefficient, clearedWordCoefficient,
        ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
        ActualHigherSZeroCoefficientFactorisation.parameterGramFrame, ActualHigherSFormation.higherSParam]
    | inr m =>
      simp only [actualWordCoefficient, wordCoefficient, clearedWordCoefficient]
      split_ifs
      · calc
          _ = referenceRadius dr Ar p L x*referenceDensityPrincipalFrameCoefficient g g2 L q x i j*
              (referenceRadius dr Ar p L x*referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i) := by ring
          _ = _ := congrArg (fun y : ℝ => referenceRadius dr Ar p L x*referenceDensityPrincipalFrameCoefficient g g2 L q x i j*y) (hf i x)
      · calc
          _ = referenceRadius dr Ar p L x*referenceDensityPrincipalFrameCoefficient g g2 L q x i j*
              (referenceRadius dr Ar p L x*referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x j) := by ring
          _ = _ := congrArg (fun y : ℝ => referenceRadius dr Ar p L x*referenceDensityPrincipalFrameCoefficient g g2 L q x i j*y) (hf j x)
      · rfl
      · rfl
      · rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
