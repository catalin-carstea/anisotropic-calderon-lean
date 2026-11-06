import Calderon.ActualOriginalSDirectPhysicalForm
import Calderon.ActualSScalarCoefficientBounds
import Calderon.ActualOriginalDoubleEForm
import Calderon.ActualWeightedHorizontalActionBounds

/-! Original secondS/fullS physical form bounds. Uses `ActualOriginalSDirectPhysicalForm`
and `ActualSScalarCoefficientBounds` only through their stated APIs.

* §1 exact `densityDerivativeCoefficient` of the literal `secondCoefficient = R²Q_ij`
  (`= R²(Q div + μ(X_iQ + 2Q f_i))`) and the bound `≤ Cc μ R² β`, `Cc` before all profiles; no density
  lower bound, no inverse inclusion.
* §2 exact signed pointwise split of the literal `higherSSecondHalf` pairing and its integrated form.
* §3 integrated diagonal bound `|∫μ⟪F,KL secondS F⟫| ≤ K ∫ μ(R²‖U‖Σ‖IH dU X_i‖ + R²β‖U‖²)`.
* §4 full literal `nativeHigherSOut` bound with `(R + R²β + R³)‖U‖²`, ONE common room `δ, Cm`.
The one extra hypothesis is `Continuous (actualReferenceBeta g L q δr Ar p)`, needed only for
integrability of the requested majorant. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalFormBounds
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
  ActualHorizontalNormBridge ActualHigherSIntegratedPairing ActualHigherSPhysicalPairing
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 0. Generic real/inner estimates (no actual premise) -/

private lemma abs_add_le'' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  simpa only [Real.norm_eq_abs] using norm_add_le x y

private lemma abs_sub_le'' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le x y

private lemma abs_sum3_le (f : Fin 3 → ℝ) (M : ℝ) (h : ∀ i, |f i| ≤ M) :
    |∑ i : Fin 3, f i| ≤ 3 * M := by
  calc |∑ i : Fin 3, f i| ≤ ∑ i : Fin 3, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum (fun i _ => h i)
    _ = 3 * M := by simp only [Fin.sum_univ_three]; ring

private lemma abs_sum33_le (f : Fin 3 → Fin 3 → ℝ) (M : ℝ) (h : ∀ i j, |f i j| ≤ M) :
    |∑ i : Fin 3, ∑ j : Fin 3, f i j| ≤ 9 * M := by
  calc |∑ i : Fin 3, ∑ j : Fin 3, f i j| ≤ 3 * (3 * M) :=
        abs_sum3_le _ _ (fun i => abs_sum3_le _ _ (fun j => h i j))
    _ = 9 * M := by ring

/-- Absorption into the requested majorant using only `β ≥ 1`. -/
private lemma maj_absorb (μ R2 N s b A Bc X : ℝ) (hμ : 0 ≤ μ) (hR2 : 0 ≤ R2) (hN : 0 ≤ N)
    (hs : 0 ≤ s) (hb : 1 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ Bc)
    (hX : X ≤ μ * R2 * (A * (N * s) + Bc * b * (N * N))) :
    X ≤ (A + Bc) * (μ * (R2 * N * s + R2 * b * (N * N))) := by
  have h0 : 0 ≤ μ * R2 * (Bc * (N * s) + A * b * (N * N)) := by
    have : 0 ≤ b := zero_le_one.trans hb
    positivity
  nlinarith [h0]

/-- The constant-coefficient `N²` terms are dominated by `β N²`. -/
private lemma const_le_beta (c b N : ℝ) (hc : 0 ≤ c) (hb : 1 ≤ b) :
    c * (N * N) ≤ c * b * (N * N) := by
  have h1 : 0 ≤ c * (N * N) := mul_nonneg hc (mul_self_nonneg N)
  nlinarith [mul_nonneg h1 (sub_nonneg.2 hb)]

private lemma pp_zero_left' (v : Neg) : PP 0 v = 0 := by
  unfold sphereSobolevDualPairing
  exact inner_zero_left _

private lemma pp_zero_right' (u : Half) : PP u 0 = 0 := by
  unfold sphereSobolevDualPairing
  exact inner_zero_right u

private lemma norm_scalar_pairing_zero (a : ℝ) (u : Half) (v : Neg) (hu : u = 0)
    (m c : ℝ) (hm : m = 0) : ‖a * PP u v‖ ≤ c * m := by
  rw [hu, hm, pp_zero_left']
  simp

private lemma scalar_zero_form_bound (μ r N s b k ci ce cre cd cf cg cb cq : ℝ)
    (Q Y : Fin 3 → Fin 3 → ℝ) (G : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (f V drift : Fin 3 → ℝ)
    (hμ : 0 ≤ μ) (hN : 0 ≤ N) (hs : 0 ≤ s) (hb : 1 ≤ b)
    (hk : 0 ≤ k) (hci : 0 ≤ ci) (hce : 0 ≤ ce) (hcre : 0 ≤ cre)
    (hcd : 0 ≤ cd) (hcf : 0 ≤ cf) (hcg : 0 ≤ cg) (hcb : 0 ≤ cb) (hcq : 0 ≤ cq)
    (hQ : ∀ i j, |Q i j| ≤ cq)
    (hY : ∀ i j, |Y i j| ≤ k*cre*(N*s)+k*cre*cd*b*(N*N))
    (hf : ∀ i, |f i| ≤ cf*b) (hV : ∀ i, |V i| ≤ k*(ci*ce)*(N*N))
    (hG : ∀ i j z, |G i j z| ≤ cg) (hd : ∀ i, |drift i| ≤ cb) :
    ‖μ*(r^2*(∑ i : Fin 3, ∑ j : Fin 3, Q i j*
        (Y i j+f i*V j-∑ z : Fin 3, G i j z*V z))+
      r^2*(∑ i : Fin 3, drift i*V i))‖ ≤
      (9*cq*k*(cre*(1+cd)+cf*ci*ce+3*cg*ci*ce)+3*cb*k*ci*ce)*
        (μ*(r^2*N*s+r^2*b*(N*N))) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hrow : ∀ i j, |Q i j*(Y i j+f i*V j-∑ z : Fin 3, G i j z*V z)| ≤
      cq*(k*cre*(N*s)+(k*cre*cd+cf*(k*(ci*ce))+3*(cg*(k*(ci*ce))))*b*(N*N)) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul (hQ i j) ?_ (abs_nonneg _) hcq
    have t2 : |f i*V j| ≤ cf*(k*(ci*ce))*b*(N*N) := by
      rw [abs_mul]
      calc _ ≤ (cf*b)*(k*(ci*ce)*(N*N)) := mul_le_mul (hf i) (hV j) (abs_nonneg _) (by positivity)
           _ = _ := by ring
    have t3 : |∑ z : Fin 3, G i j z*V z| ≤ 3*(cg*(k*(ci*ce)))*b*(N*N) := by
      refine (abs_sum3_le _ (cg*(k*(ci*ce))*(N*N)) (fun z => ?_)).trans ?_
      · rw [abs_mul]
        calc _ ≤ cg*(k*(ci*ce)*(N*N)) := mul_le_mul (hG i j z) (hV z) (abs_nonneg _) hcg
             _ = _ := by ring
      · simpa only [mul_assoc] using const_le_beta (3*(cg*(k*(ci*ce)))) b N (by positivity) hb
    calc _ ≤ (|Y i j|+|f i*V j|)+|∑ z : Fin 3, G i j z*V z| :=
           (abs_sub_le'' _ _).trans (add_le_add (abs_add_le'' _ _) le_rfl)
         _ ≤ (k*cre*(N*s)+k*cre*cd*b*(N*N))+cf*(k*(ci*ce))*b*(N*N)+
             3*(cg*(k*(ci*ce)))*b*(N*N) := add_le_add (add_le_add (hY i j) t2) t3
         _ = _ := by ring
  have hdsum : |∑ i : Fin 3, drift i*V i| ≤ 3*(cb*(k*(ci*ce)))*b*(N*N) := by
    refine (abs_sum3_le _ (cb*(k*(ci*ce))*(N*N)) (fun i => ?_)).trans ?_
    · rw [abs_mul]
      calc _ ≤ cb*(k*(ci*ce)*(N*N)) := mul_le_mul (hd i) (hV i) (abs_nonneg _) hcb
           _ = _ := by ring
    · simpa only [mul_assoc] using const_le_beta (3*(cb*(k*(ci*ce)))) b N (by positivity) hb
  have hz : |r^2*(∑ i : Fin 3, ∑ j : Fin 3, Q i j*
        (Y i j+f i*V j-∑ z : Fin 3, G i j z*V z))+
      r^2*(∑ i : Fin 3, drift i*V i)| ≤
      r^2*((9*cq*k*cre)*(N*s)+
        (9*cq*(k*cre*cd+cf*(k*(ci*ce))+3*(cg*(k*(ci*ce))))+
          3*(cb*(k*(ci*ce))))*b*(N*N)) := by
    refine (abs_add_le'' _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc _ ≤ r^2*(9*(cq*(k*cre*(N*s)+
            (k*cre*cd+cf*(k*(ci*ce))+3*(cg*(k*(ci*ce))))*b*(N*N))))+
            r^2*(3*(cb*(k*(ci*ce)))*b*(N*N)) :=
           add_le_add (mul_le_mul_of_nonneg_left (abs_sum33_le _ _ hrow) (sq_nonneg r))
             (mul_le_mul_of_nonneg_left hdsum (sq_nonneg r))
         _ = _ := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hμ]
  have hX := mul_le_mul_of_nonneg_left hz hμ
  have hx : μ*|r^2*(∑ i : Fin 3, ∑ j : Fin 3, Q i j*
        (Y i j+f i*V j-∑ z : Fin 3, G i j z*V z))+
      r^2*(∑ i : Fin 3, drift i*V i)| ≤ μ*r^2*
        ((9*cq*k*cre)*(N*s)+(9*cq*(k*cre*cd+cf*(k*(ci*ce))+
          3*(cg*(k*(ci*ce))))+3*(cb*(k*(ci*ce))))*b*(N*N)) := by
    simpa only [mul_assoc] using hX
  have hm := maj_absorb _ _ _ _ _ _ _ _ hμ (sq_nonneg r) hN hs hb (by positivity) (by positivity) hx
  refine hm.trans (le_of_eq ?_)
  ring

private lemma abs_signed_three (a b c : ℝ) : |-a+2*b-c| ≤ |a|+2*|b|+|c| := by
  calc _ ≤ |-a+2*b|+|c| := abs_sub_le'' _ _
       _ ≤ (|-a|+|2*b|)+|c| := add_le_add (abs_add_le'' _ _) le_rfl
       _ = _ := by rw [abs_neg, abs_mul, abs_two]

private lemma combine_three_forms (P P1 P2 P3 M M1 M2 M3 : R3 → ℝ)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hP1 : Integrable P1) (hP2 : Integrable P2) (hP3 : Integrable P3)
    (hM1 : Integrable M1) (hM2 : Integrable M2) (hM3 : Integrable M3)
    (hP : ∀ x, P x = P1 x+P2 x+P3 x) (hM : ∀ x, M x = M1 x+M2 x+M3 x)
    (hn1 : ∀ x, 0 ≤ M1 x) (hn2 : ∀ x, 0 ≤ M2 x) (hn3 : ∀ x, 0 ≤ M3 x)
    (h1 : |∫ x, P1 x| ≤ a*∫ x, M1 x) (h2 : |∫ x, P2 x| ≤ b*∫ x, M2 x)
    (h3 : |∫ x, P3 x| ≤ c*∫ x, M3 x) :
    Integrable P ∧ Integrable M ∧ |∫ x, P x| ≤ (a+b+c)*∫ x, M x := by
  have hp : P = fun x => P1 x+P2 x+P3 x := funext hP
  have hm : M = fun x => M1 x+M2 x+M3 x := funext hM
  refine ⟨?_,?_,?_⟩
  · rw [hp]; exact (hP1.add hP2).add hP3
  · rw [hm]; exact (hM1.add hM2).add hM3
  · have hpI : (∫ x, P x) = (∫ x, P1 x)+(∫ x, P2 x)+(∫ x, P3 x) := by
      calc _ = (∫ x, (P1+P2) x)+(∫ x, P3 x) := by
             rw [hp]; exact integral_add (hP1.add hP2) hP3
           _ = _ := congrArg (fun r : ℝ => r+(∫ x, P3 x)) (integral_add hP1 hP2)
    have hmI : (∫ x, M x) = (∫ x, M1 x)+(∫ x, M2 x)+(∫ x, M3 x) := by
      calc _ = (∫ x, (M1+M2) x)+(∫ x, M3 x) := by
             rw [hm]; exact integral_add (hM1.add hM2) hM3
           _ = _ := congrArg (fun r : ℝ => r+(∫ x, M3 x)) (integral_add hM1 hM2)
    rw [hpI,hmI]
    have I1 : 0 ≤ ∫ x, M1 x := MeasureTheory.integral_nonneg hn1
    have I2 : 0 ≤ ∫ x, M2 x := MeasureTheory.integral_nonneg hn2
    have I3 : 0 ≤ ∫ x, M3 x := MeasureTheory.integral_nonneg hn3
    calc _ ≤ (|∫ x, P1 x|+|∫ x, P2 x|)+|∫ x, P3 x| :=
           (abs_add_le'' _ _).trans (add_le_add (abs_add_le'' _ _) le_rfl)
         _ ≤ a*(∫ x, M1 x)+b*(∫ x, M2 x)+c*(∫ x, M3 x) := add_le_add (add_le_add h1 h2) h3
         _ ≤ _ := by nlinarith [mul_nonneg ha I2,mul_nonneg ha I3,mul_nonneg hb I1,
           mul_nonneg hb I3,mul_nonneg hc I1,mul_nonneg hc I2]

private lemma full_majorant_split_real (μ r N s b : ℝ) :
    μ*(r^2*N*s+(r+r^2*b+r^3)*(N*N)) =
      μ*(r^2*N*s+r^2*b*(N*N))+μ*(r*(N*N))+μ*r^3*(N*N) := by ring

private lemma density_inner_sum_three {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (K : E →L[ℝ] G) (z : G)
    (μ : ℝ) (u v w : E) :
    μ*⟪z,K (u+v+w)⟫_ℝ = μ*⟪z,K u⟫_ℝ+μ*⟪z,K v⟫_ℝ+μ*⟪z,K w⟫_ℝ := by
  rw [map_add,map_add,inner_add_right,inner_add_right]
  ring

/-! ## 1. Actual density coefficient of the literal `secondCoefficient = R² Q_ij` -/

private lemma square_mul_fderiv (r Q : R3 → ℝ) (x v : R3)
    (hr : HasFDerivAt r (fderiv ℝ r x) x) (hQ : HasFDerivAt Q (fderiv ℝ Q x) x) :
    fderiv ℝ (fun y => (r y)^2 * Q y) x v =
      (r x)^2 * (fderiv ℝ Q x v) + 2 * r x * Q x * (fderiv ℝ r x v) := by
  change (fderiv ℝ ((fun y => (r y)^2) * Q) x) v = _
  rw [((hr.pow 2).mul hQ).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma density_distribute_second (μ Z : ℝ) (c d e : Fin 3 → Fin 3 → ℝ)
    (h : ∀ i j, d i j = e i j) :
    μ * ((∑ i : Fin 3, ∑ j : Fin 3, c i j * d i j) + Z) =
      (∑ i : Fin 3, ∑ j : Fin 3, μ * c i j * e i j) + μ * Z := by
  simp only [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i j]
  ring

private lemma integrable_zero_of_sum (P Z : R3 → ℝ) (A : Fin 3 → Fin 3 → R3 → ℝ)
    (hP : Integrable P) (hA : ∀ i j, Integrable (A i j))
    (he : ∀ x, P x = (∑ i : Fin 3, ∑ j : Fin 3, A i j x)+Z x) : Integrable Z := by
  have hs := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hA i j))
  apply (hP.sub hs).congr
  exact ae_of_all _ (fun x => by
    simp only [Pi.sub_apply, Finset.sum_apply]
    linarith only [he x])

private lemma integral_sum_decomposition (P Z : R3 → ℝ) (A : Fin 3 → Fin 3 → R3 → ℝ)
    (hA : ∀ i j, Integrable (A i j)) (hZ : Integrable Z)
    (he : ∀ x, P x = (∑ i : Fin 3, ∑ j : Fin 3, A i j x)+Z x) :
    (∫ x, P x) = (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, A i j x)+(∫ x, Z x) := by
  simp only [he]
  rw [integral_add (integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hA i j))) hZ,
    integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ => hA i j))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => integral_finset_sum Finset.univ (fun j _ => hA i j))

private lemma physical_second_algebra {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (K : E →L[ℝ] G) (z : G) (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (D A : Fin 3 → Fin 3 → E) (f : Fin 3 → ℝ) (v : Fin 3 → E)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ) :
    ⟪z, K (r^2 • (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j • (D i j + A i j + f i • v j - ∑ k : Fin 3, Γ i j k • v k)) +
      r^2 • (∑ i : Fin 3, b i • v i))⟫_ℝ =
      (∑ i : Fin 3, ∑ j : Fin 3, (r^2 * Q i j) * ⟪z, K (D i j)⟫_ℝ) +
        (r^2 * ∑ i : Fin 3, ∑ j : Fin 3, Q i j *
          (⟪z, K (A i j)⟫_ℝ + f i * ⟪z, K (v j)⟫_ℝ -
            ∑ k : Fin 3, Γ i j k * ⟪z, K (v k)⟫_ℝ) +
          r^2 * ∑ i : Fin 3, b i * ⟪z, K (v i)⟫_ℝ) := by
  simp only [map_add, map_sub, map_smul, map_sum, inner_add_right, inner_sub_right,
    real_inner_smul_right, inner_sum, Fin.sum_univ_three]
  ring

attribute [local irreducible] referenceRadius referenceDensityPrincipalFrameCoefficient
  referenceMetricGramFrame

/-- Exact product rule with the native identity `R f_i = dR(X_i)`. -/
theorem secondCoefficient_frame_fderiv (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L q δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (i j : Fin 3) (x : R3) :
    fderiv ℝ (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x
        (referenceMetricGramFrame g L (q,x) i) =
      (referenceRadius δr Ar p L x)^2 *
        (fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
            (referenceMetricGramFrame g L (q,x) i) +
          2 * referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i) := by
  have hR : ContDiff ℝ ∞ (referenceRadius δr Ar p L) :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hQ : ContDiff ℝ ∞ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (contDiff_const.prodMk contDiff_id)
  have hRd : HasFDerivAt (referenceRadius δr Ar p L) (fderiv ℝ (referenceRadius δr Ar p L) x) x :=
    (hR.differentiable (by simp) x).hasFDerivAt
  have hQd : HasFDerivAt (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
      (fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x) x :=
    (hQ.differentiable (by simp) x).hasFDerivAt
  have hRf0 := referenceRadius_mul_horizontalLogDerivative_eq_fderiv g L q
    (referenceRadius δr Ar p L) hR x (referenceRadius_pos δr Ar p L x hδr hAr).ne' i
  have hRf : fderiv ℝ (referenceRadius δr Ar p L) x (referenceMetricGramFrame g L (q,x) i) =
      referenceRadius δr Ar p L x *
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i := by
    have hx := congrArg (fderiv ℝ (referenceRadius δr Ar p L) x)
      (ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x i)
    exact hx.symm.trans hRf0.symm
  change fderiv ℝ (fun y => (referenceRadius δr Ar p L y)^2 *
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
      (referenceMetricGramFrame g L (q,x) i) = _
  have hd := square_mul_fderiv (referenceRadius δr Ar p L)
    (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
    (referenceMetricGramFrame g L (q,x) i) hRd hQd
  calc _ = _ := hd
       _ = _ := by rw [hRf]; ring

/-- Exact original density coefficient of `R² Q_ij`. -/
theorem densityDerivativeCoefficient_second_eq (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L q δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (i j : Fin 3) (x : R3) :
    ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x =
      (referenceRadius δr Ar p L x)^2 *
        (referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
            referenceWeightedFrameDivergence g L q i x +
          referenceDensityFamily g L (q,x) *
            (fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
                (referenceMetricGramFrame g L (q,x) i) +
              2 * referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
                referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i)) := by
  unfold ActualHigherSSecondAdjoint.densityDerivativeCoefficient
  rw [secondCoefficient_frame_fderiv g g2 hg hg2 L q δr Ar p hδr hAr i j x]
  unfold ActualHigherSSecondAdjoint.secondCoefficient
  ring

/-- `|densityDerivativeCoefficient_i(R²Q_ij)| ≤ Cc μ R² β`, `Cc` after fixed `g2`, before profiles. -/
theorem exists_second_density_coefficient_bound (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (y0 : R3) (ρ : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p →
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x → ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 *
          ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x := by
  obtain ⟨CQ, hCQ, hQF⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    (g := g) (L := L) (y0 := y0) (ρ := ρ) (hg := hg) g2 hg2
  obtain ⟨Cf, hCf, hf⟩ := ActualSScalarCoefficientBounds.exists_profile_horizontal_log_derivative_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cdiv, hCdiv, hdiv⟩ := ActualSScalarCoefficientBounds.exists_weighted_frame_divergence_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨CQ1, hCQ1, hdQ⟩ := ActualSScalarCoefficientBounds.exists_principal_horizontal_derivative_bound
    g g2 hg hg2 L (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  refine ⟨CQ * Cdiv + CQ1 + 2 * CQ * Cf, by positivity, ?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ i j
  rw [densityDerivativeCoefficient_second_eq g g2 hg hg2 L q δr Ar p hδr hAr i j x]
  have hQx := (hQF q hq x hx i j).1
  have hdx := hdiv q hq x hx i
  have hfx := hf δr Ar p hδr hδr1 hAr hp q hq x hx hβ i
  have hdQx := hdQ q hq x hx i i j
  have hμ := referenceDensityFamily_pos g hg L (q,x)
  set R2 := (referenceRadius δr Ar p L x)^2 with hR2
  set μ := referenceDensityFamily g L (q,x)
  set β := ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x
  set Qx := referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  set dv := referenceWeightedFrameDivergence g L q i x
  set dQ := fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
    (referenceMetricGramFrame g L (q,x) i)
  set fx := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i
  have hR20 : 0 ≤ R2 := sq_nonneg _
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have h1 : |Qx * dv| ≤ CQ * (Cdiv * μ) := by
    rw [abs_mul]; exact mul_le_mul hQx hdx (abs_nonneg _) hCQ0
  have h2 : |dQ + 2 * Qx * fx| ≤ CQ1 + 2 * CQ * (Cf * β) := by
    refine (abs_add_le'' _ _).trans (add_le_add hdQx ?_)
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQx (by norm_num)) hfx (abs_nonneg _) (by positivity)
  have h3 : |Qx * dv + μ * (dQ + 2 * Qx * fx)| ≤ CQ * (Cdiv * μ) + μ * (CQ1 + 2 * CQ * (Cf * β)) := by
    refine (abs_add_le'' _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left h2 hμ.le
  rw [abs_mul, abs_of_nonneg hR20]
  have hfin : R2 * (CQ * (Cdiv * μ) + μ * (CQ1 + 2 * CQ * (Cf * β))) ≤
      (CQ * Cdiv + CQ1 + 2 * CQ * Cf) * μ * R2 * β := by
    have hp0 : 0 ≤ R2 * μ * (CQ * Cdiv + CQ1) * (β - 1) := by
      have : 0 ≤ β - 1 := sub_nonneg.2 hβ
      positivity
    nlinarith [hp0]
  exact (mul_le_mul_of_nonneg_left h3 hR20).trans hfin

/-! ## 2. Actual setting -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "UD" => ActualHigherSFormation.higherSReferenceInput hO hD g L hg
local notation "SS" => ActualHigherSFormation.higherSSecondHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "FA" => ActualHigherSFormation.higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SH" => ActualHigherSFormation.nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "SO" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BETA" => ReferenceWeightedApproximation.actualReferenceBeta g L

private lemma abs_inner_KL_le (x y : Half) : |⟪KL x, KL y⟫_ℝ| ≤ ‖KL‖^2 * (‖x‖ * ‖y‖) := by
  calc |⟪KL x, KL y⟫_ℝ| ≤ ‖KL x‖ * ‖KL y‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖KL‖ * ‖x‖) * (‖KL‖ * ‖y‖) :=
        mul_le_mul ((KL).le_opNorm x) ((KL).le_opNorm y) (norm_nonneg _) (by positivity)
    _ = ‖KL‖^2 * (‖x‖ * ‖y‖) := by ring

private lemma norm_scalar_halfPairing (a : ℝ) (u v : Half) :
    ‖a * PP u (JL v)‖ = |a| * |⟪KL u, KL v⟫_ℝ| := by
  rw [Real.norm_eq_abs, abs_mul, halfPairing_eq_inner_sphereL2 hO hD]

private lemma norm_triple_halfPairing (a b c : ℝ) (u v : Half) (ha : 0 < a) :
    ‖a*b*c*PP u (JL v)‖ = a * |b| * |c| * |⟪KL u,KL v⟫_ℝ| := by
  rw [norm_scalar_halfPairing hO hD, abs_mul, abs_mul, abs_of_pos ha]

private lemma inner_from_caps {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (K : E →L[ℝ] G) (x y : E)
    (A B N : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hx : ‖x‖ ≤ A*N) (hy : ‖y‖ ≤ B*N) :
    |⟪K x,K y⟫_ℝ| ≤ ‖K‖^2*(A*B)*(N*N) := by
  calc _ ≤ ‖K x‖*‖K y‖ := abs_real_inner_le_norm _ _
       _ ≤ (‖K‖*(A*N))*(‖K‖*(B*N)) :=
         mul_le_mul ((K.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (by positivity)))
           ((K.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (by positivity)))
           (norm_nonneg _) (by positivity)
       _ = _ := by ring

private lemma inner_from_linear_caps {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (K : E →L[ℝ] G) (x y : E)
    (A D b N s : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hb : 0 ≤ b) (hN : 0 ≤ N) (hs : 0 ≤ s)
    (hx : ‖x‖ ≤ s+D*b*N) (hy : ‖y‖ ≤ A*N) :
    |⟪K x,K y⟫_ℝ| ≤ ‖K‖^2*A*(N*s)+‖K‖^2*A*D*b*(N*N) := by
  calc _ ≤ ‖K x‖*‖K y‖ := abs_real_inner_le_norm _ _
       _ ≤ (‖K‖*(s+D*b*N))*(‖K‖*(A*N)) :=
         mul_le_mul ((K.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (by positivity)))
           ((K.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (by positivity)))
           (norm_nonneg _) (by positivity)
       _ = _ := by ring

private lemma paramRoom_q_ball' (δr Ar : ℝ) (p : ℕ) (q δ : ℝ) (x : R3)
    (ht : (Tq δr Ar p q) x ∈ ParamRoom δ) : q ∈ Icc (0 : ℝ) 1 ∧ x ∈ closedBall y0 ρ := by
  have hc : ((q,(x,referenceRadius δr Ar p L x)) : Pphys) ∈ commonRoom y0 ρ δ := ht.1
  first
    | exact ⟨hc.1, hc.2.1⟩
    | (simp only [commonRoom, Set.mem_prod] at hc; exact ⟨hc.1, hc.2.1⟩)

/-- Requested majorant `μ(R²‖U‖Σ_i‖IH(dU X_i)‖ + R²β‖U‖²)`. -/
def secondMajorant (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (x : R3) : ℝ :=
  referenceDensityFamily g L (q,x) *
    ((referenceRadius δr Ar p L x)^2 * ‖Uin F0 x‖ *
        (∑ i : Fin 3, ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖) +
      (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x * (‖Uin F0 x‖ * ‖Uin F0 x‖))
local notation "MJ" => secondMajorant g L hO hD

/-- Requested full-S majorant `μ(R²‖U‖Σ‖IH dU X_i‖ + (R + R²β + R³)‖U‖²)`. -/
def fullMajorant (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (x : R3) : ℝ :=
  referenceDensityFamily g L (q,x) *
    ((referenceRadius δr Ar p L x)^2 * ‖Uin F0 x‖ *
        (∑ i : Fin 3, ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖) +
      (referenceRadius δr Ar p L x + (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x +
        (referenceRadius δr Ar p L x)^3) * (‖Uin F0 x‖ * ‖Uin F0 x‖))
local notation "FM" => fullMajorant g L hO hD

/-- Zero-order part of the literal secondS pairing after the E-UD pivot (all Γ, f, b retained). -/
def secondZeroGram (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : ℝ :=
  (referenceRadius δr Ar p L y)^2 * ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        (⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y j),
            KL (eH i ((Tq δr Ar p q) y) (Uin F0 y))⟫_ℝ +
          referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i *
            ⟪F0.val y, KL (IH (VF δr Ar p q hreg δ0 W F0 j y))⟫_ℝ -
          ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
              (referenceMetricGramFrame g L (q,y) i) k j *
            ⟪F0.val y, KL (IH (VF δr Ar p q hreg δ0 W F0 k y))⟫_ℝ) +
    (referenceRadius δr Ar p L y)^2 * ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) *
      ⟪F0.val y, KL (IH (VF δr Ar p q hreg δ0 W F0 i y))⟫_ℝ
local notation "ZG" => secondZeroGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh reverseEHigh sphereSobolevInclusionL
  sphereSobolevDualPairing sphereSobolevHalfToSphereL2L referenceHighWeightedHorizontalAction

/-! ## 3. Exact signed split of the literal secondS pairing -/

/-- GLOBAL pointwise split: D rows kept with the literal `secondCoefficient`, rest in `ZG`. -/
private lemma pointwise_second_literal_split (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (y : R3) :
    ⟪F0.val y, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 y)⟫_ℝ =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
          ⟪F0.val y, KL (referenceHighWeightedHorizontalAction g L q
            (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i)⟫_ℝ) +
        ZG hreg δ0 W g2 δr Ar p q F0 y := by
  have hEUD := fun i j => ActualOriginalSDirectPhysicalForm.pointwise_second_EUD_row g L y0 Φ B ε C ρ
    H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF i j y
  have hs := physical_second_algebra KL (F0.val y) (referenceRadius δr Ar p L y)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
    (fun i j => referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (VF δr Ar p q hreg δ0 W F0 j) y i)
    (fun i j => EH i ((Tq δr Ar p q) y) (UD δr Ar p hδr hAr q F0 j y))
    (fun i => referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i)
    (fun j => IH (VF δr Ar p q hreg δ0 W F0 j y))
    (fun i j k => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j)
    (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,y))
  simpa only [ActualHigherSFormation.higherSSecondHalf,
    ActualHigherSFormation.higherSSecondWordHalf, secondZeroGram,
    ActualHigherSSecondAdjoint.secondCoefficient, hEUD] using hs

theorem pointwise_second_split (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (y : R3) :
    referenceDensityFamily g L (q,y) * ⟪F0.val y, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 y)⟫_ℝ =
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityFamily g L (q,y) *
          ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
          PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
            (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))) +
        referenceDensityFamily g L (q,y) * ZG hreg δ0 W g2 δr Ar p q F0 y := by
  have hlit := pointwise_second_literal_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hTF y
  have hPF : ∀ v : Half, ⟪F0.val y, KL v⟫_ℝ = PP (IH (Uin F0 y)) (JL v) := fun v => by
    rw [halfPairing_eq_inner_sphereL2 hO hD]
    exact congrArg (fun z : SphereL2 => ⟪z, KL v⟫_ℝ)
      (halfToSphereL2_finiteCoreLift hO hD F0 y).symm
  exact (congrArg (fun z : ℝ => referenceDensityFamily g L (q,y) * z) hlit).trans
    (density_distribute_second (referenceDensityFamily g L (q,y))
      (ZG hreg δ0 W g2 δr Ar p q F0 y)
      (fun i j => ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y)
      (fun i j => ⟪F0.val y, KL (referenceHighWeightedHorizontalAction g L q
        (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i)⟫_ℝ)
      (fun i j => PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
        (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i)))
      (fun i j => hPF _))

/-! ## 4. Original secondS integrated bound (internal adapter with explicit caps) -/

/-- Adapter: every cap is a premise here and is discharged in the final theorem below. -/
private structure SecondFormPointwiseData (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p)) : Prop where
  hU0 : ∀ z ∉ TS F0, Uin F0 z = 0
  hV0 : ∀ j : Fin 3, ∀ z ∉ TS F0, VF δr Ar p q hreg δ0 W F0 j z = 0
  hFx : ∀ y, F0.val y = KL (IH (Uin F0 y))
  hEn : ∀ j : Fin 3, ∀ y, ‖IH (VF δr Ar p q hreg δ0 W F0 j y)‖ ≤ CE * ‖Uin F0 y‖
  hrn : ∀ i : Fin 3, ∀ y, ‖eH i ((Tq δr Ar p q) y) (Uin F0 y)‖ ≤ CrE * ‖Uin F0 y‖
  hIn : ∀ y, ‖IH (Uin F0 y)‖ ≤ ‖IH‖ * ‖Uin F0 y‖
  hBn : ∀ y, ‖BH (Uin F0 y)‖ ≤ ‖BH‖ * ‖Uin F0 y‖
  hDd : ∀ y ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y i‖ ≤
        (∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
          CD * BETA q δr Ar p y * ‖Uin F0 y‖
  hSa : ∀ y ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y| ≤
        (referenceRadius δr Ar p L y)^2 * CQ
  hMJ0 : ∀ y ∉ TS F0, MJ δr Ar p q F0 y = 0
  hMJnn : ∀ y, 0 ≤ MJ δr Ar p q F0 y

private lemma second_form_pointwise_data (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p)) :
    SecondFormPointwiseData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc := by
  -- actual regularity and support facts
  have hμc := continuous_density_slice g L q hg
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr : ∀ y, referenceRadius δr Ar p L y ≠ 0 := fun y => (referenceRadius_pos δr Ar p L y hδr hAr).ne'
  have hUc := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hU0 : ∀ z ∉ TS F0, Uin F0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hV0 : ∀ j : Fin 3, ∀ z ∉ TS F0, VF δr Ar p q hreg δ0 W F0 j z = 0 := fun j z hz =>
    ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j z hz
  have hVc := fun j => ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF j
  have hinc := fun j y => ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF j y
  have hP := halfPairing_eq_inner_sphereL2 hO hD
  have hFx : ∀ y, F0.val y = KL (IH (Uin F0 y)) := fun y =>
    (halfToSphereL2_finiteCoreLift hO hD F0 y).symm
  -- E caps globally (zero off the support)
  have hEn : ∀ j : Fin 3, ∀ y, ‖IH (VF δr Ar p q hreg δ0 W F0 j y)‖ ≤ CE * ‖Uin F0 y‖ := by
    intro j y
    rw [hinc j y]
    by_cases hy : y ∈ TS F0
    · exact ((EH j ((Tq δr Ar p q) y)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hE j _ (hTF y hy)).1 (norm_nonneg _))
    · simp [hU0 y hy]
  have hrn : ∀ i : Fin 3, ∀ y, ‖eH i ((Tq δr Ar p q) y) (Uin F0 y)‖ ≤ CrE * ‖Uin F0 y‖ := by
    intro i y
    by_cases hy : y ∈ TS F0
    · exact ((eH i ((Tq δr Ar p q) y)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hE i _ (hTF y hy)).2 (norm_nonneg _))
    · simp [hU0 y hy]
  have hIn : ∀ y, ‖IH (Uin F0 y)‖ ≤ ‖IH‖ * ‖Uin F0 y‖ := fun y => (IH).le_opNorm _
  have hBn : ∀ y, ‖BH (Uin F0 y)‖ ≤ ‖BH‖ * ‖Uin F0 y‖ := fun y => ContinuousLinearMap.le_opNorm BH _
  -- shorthand facts used on the support
  have hsd : ∀ y, ∀ i : Fin 3,
      ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) i))‖ ≤
        ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖ :=
    fun y i => Finset.single_le_sum
      (f := fun k : Fin 3 => ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖)
      (fun k _ => norm_nonneg _) (Finset.mem_univ i)
  have hDd : ∀ y ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y i‖ ≤
        (∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
          CD * BETA q δr Ar p y * ‖Uin F0 y‖ := fun y hy i =>
    (hDW y hy i).trans (add_le_add (hsd y i) le_rfl)
  have hSa : ∀ y ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y| ≤
        (referenceRadius δr Ar p L y)^2 * CQ := fun y hy i j => by
    unfold ActualHigherSSecondAdjoint.secondCoefficient
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hQ y hy i j) (sq_nonneg _)
  have hMJ0 : ∀ y ∉ TS F0, MJ δr Ar p q F0 y = 0 := fun y hy => by
    unfold secondMajorant; simp [hU0 y hy]
  have hMJnn : ∀ y, 0 ≤ MJ δr Ar p q F0 y := fun y => by
    unfold secondMajorant
    by_cases hy : y ∈ TS F0
    · have := hβ1 y hy
      have : 0 ≤ BETA q δr Ar p y := zero_le_one.trans this
      have := (referenceDensityFamily_pos g hg L (q,y)).le
      positivity
    · simp [hU0 y hy]
  exact ⟨hU0,hV0,hFx,hEn,hrn,hIn,hBn,hDd,hSa,hMJ0,hMJnn⟩

private structure SecondFormIntegralData (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p)) : Prop where
  hPi : Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ)
  hMJi : Integrable (MJ δr Ar p q F0)
  hIntEq : (∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ) =
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, referenceDensityFamily g L (q,y) *
          ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
          PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
            (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))) +
        ∫ y, referenceDensityFamily g L (q,y) * ZG hreg δ0 W g2 δr Ar p q F0 y

private lemma second_form_integral_data (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p)) :
    SecondFormIntegralData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc := by
  have hμc := continuous_density_slice g L q hg
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr : ∀ y, referenceRadius δr Ar p L y ≠ 0 := fun y => (referenceRadius_pos δr Ar p L y hδr hAr).ne'
  have hUc := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hU0 : ∀ z ∉ TS F0, Uin F0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hV0 : ∀ j : Fin 3, ∀ z ∉ TS F0, VF δr Ar p q hreg δ0 W F0 j z = 0 := fun j z hz =>
    ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W F0 j z hz
  have hVc := fun j => ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF j
  have hMJ0 : ∀ y ∉ TS F0, MJ δr Ar p q F0 y = 0 := fun y hy => by
    unfold secondMajorant; simp [hU0 y hy]
  have hMJi : Integrable (MJ δr Ar p q F0) := by
    have hX : ∀ k : Fin 3, Continuous (fun y => referenceMetricGramFrame g L (q,y) k) := fun k =>
      (contDiff_referenceMetricGramFrame_slice g hg L q k).continuous
    have hdU : ∀ k : Fin 3, Continuous (fun y =>
        ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) := fun k =>
      ((IH).continuous.comp ((hUc.continuous_fderiv (by simp)).clm_apply (hX k))).norm
    have hcont : Continuous (MJ δr Ar p q F0) := by
      unfold secondMajorant
      exact hμc.mul ((((hRR.continuous.pow 2).mul hUc.continuous.norm).mul
        (continuous_finset_sum _ (fun k _ => hdU k))).add
        (((hRR.continuous.pow 2).mul hβc).mul (hUc.continuous.norm.mul hUc.continuous.norm)))
    exact ActualHigherSIntegratedPairing.integrable_of_vanish _ hcont _ F0.property.2.1 hMJ0
  have hPi := (ActualHigherSSecondAdjoint.integrated_second_physical_adjoint g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 F0 hTF hTF).1
  have hAi : ∀ i j : Fin 3, Integrable (fun y => referenceDensityFamily g L (q,y) *
      ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
      PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
        (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))) := by
    intro i j
    have hv : ContDiff ℝ ∞ (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) := (IH).contDiff.comp (hVc j)
    have hvc : HasCompactSupport (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) :=
      ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _
        (fun z hz => by simp only [hV0 j z hz, map_zero])
    have hpt : ∀ y, JL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
        (VF δr Ar p q hreg δ0 W F0 j) y i) =
        referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
          (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) y i := fun y =>
      ActualHigherSFormation.referenceWeightedHorizontalAction_inclusion g L q
        (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i
        (((hVc j).differentiable (by simp)) y)
    simp only [hpt]
    exact ActualHigherSIntegratedPairing.integrable_of_vanish _
      ((hμc.mul (ActualHigherSSecondAdjoint.contDiff_secondCoefficient g g2 hg hg2 L q δr Ar p hδr hAr
        i j).continuous).mul (continuous_halfPairing ((IH).continuous.comp hUc.continuous)
          (continuous_lowerWeighted g L q (referenceRadius δr Ar p L) hg hRR hr _ hv i)))
      _ hvc (fun y hy => by
        rw [lowerWeighted_eq_zero_of_notMem g L q (referenceRadius δr Ar p L) _ y i hy,
          pp_zero_right', mul_zero])
  have hSplit := pointwise_second_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W
    δ Cm g2 δr Ar p hδr hAr q F0 hTF
  have hZi : Integrable (fun y => referenceDensityFamily g L (q,y) * ZG hreg δ0 W g2 δr Ar p q F0 y) :=
    integrable_zero_of_sum _ _ _ hPi hAi hSplit
  have hIntEq : (∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ) =
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, referenceDensityFamily g L (q,y) *
          ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
          PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
            (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))) +
        ∫ y, referenceDensityFamily g L (q,y) * ZG hreg δ0 W g2 δr Ar p q F0 y :=
    integral_sum_decomposition _ _ _ hAi hZi hSplit
  exact ⟨hPi,hMJi,hIntEq⟩

private lemma second_form_pG1_bound (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p))
    (D : SecondFormPointwiseData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc) (c1 : ℝ)
    (hc1 : c1 = CQ * ‖KL‖^2 * CE * (1 + CD)) :
    ∀ i j : Fin 3, ∀ y, ‖referenceDensityFamily g L (q,y) *
      ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
      PP (IH (VF δr Ar p q hreg δ0 W F0 j y)) (JL (referenceHighWeightedHorizontalAction g L q
        (referenceRadius δr Ar p L) (Uin F0) y i))‖ ≤ c1 * MJ δr Ar p q F0 y := by
  have hV0 := D.hV0
  have hEn := D.hEn
  have hDd := D.hDd
  have hSa := D.hSa
  have hMJ0 := D.hMJ0
  have hK2 : 0 ≤ ‖KL‖^2 := sq_nonneg _
  intro i j y
  by_cases hy : y ∈ TS F0
  · have hμ := referenceDensityFamily_pos g hg L (q,y)
    have hβ := hβ1 y hy
    rw [norm_scalar_halfPairing hO hD, abs_mul, abs_of_pos hμ]
    have hin := (abs_inner_KL_le hO hD _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hEn j y) (hDd y hy i) (norm_nonneg _) (by positivity)) hK2)
    have hX : referenceDensityFamily g L (q,y) *
        |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y| *
        |⟪KL (IH (VF δr Ar p q hreg δ0 W F0 j y)), KL (referenceHighWeightedHorizontalAction g L q
          (referenceRadius δr Ar p L) (Uin F0) y i)⟫_ℝ| ≤
        referenceDensityFamily g L (q,y) * (referenceRadius δr Ar p L y)^2 *
          ((CQ * ‖KL‖^2 * CE) * (‖Uin F0 y‖ *
            ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
          (CQ * ‖KL‖^2 * CE * CD) * BETA q δr Ar p y * (‖Uin F0 y‖ * ‖Uin F0 y‖)) := by
      calc _ ≤ referenceDensityFamily g L (q,y) * ((referenceRadius δr Ar p L y)^2 * CQ) *
            (‖KL‖^2 * ((CE * ‖Uin F0 y‖) *
              ((∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
                CD * BETA q δr Ar p y * ‖Uin F0 y‖))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hSa y hy i j) hμ.le) hin (abs_nonneg _)
              (mul_nonneg hμ.le (mul_nonneg (sq_nonneg _) hCQ))
        _ = _ := by ring
    have hm := maj_absorb _ _ _ _ _ _ _ _ hμ.le (sq_nonneg _) (norm_nonneg _)
      (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hβ (by positivity) (by positivity) hX
    unfold secondMajorant
    refine hm.trans (le_of_eq ?_)
    rw [hc1]; ring
  · exact norm_scalar_pairing_zero _ _ _
      (by simpa only [map_zero] using congrArg IH (hV0 j y hy)) _ _ (hMJ0 y hy)

private lemma second_form_pG2_bound (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p))
    (D : SecondFormPointwiseData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc) (c2 : ℝ)
    (hc2 : c2 = Cf * CQ * ‖KL‖^2 * CE * ‖BH‖) :
    ∀ i j : Fin 3, ∀ y, ‖referenceDensityFamily g L (q,y) *
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i *
      ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
      PP (IH (VF δr Ar p q hreg δ0 W F0 j y))
        (JL (BH (Uin F0 y)))‖ ≤ c2 * MJ δr Ar p q F0 y := by
  have hV0 := D.hV0
  have hEn := D.hEn
  have hBn := D.hBn
  have hSa := D.hSa
  have hMJ0 := D.hMJ0
  have hK2 : 0 ≤ ‖KL‖^2 := sq_nonneg _
  have hBH : 0 ≤ ‖BH‖ := ContinuousLinearMap.opNorm_nonneg _
  have hc2nn : 0 ≤ c2 := by rw [hc2]; positivity
  intro i j y
  by_cases hy : y ∈ TS F0
  · have hμ := referenceDensityFamily_pos g hg L (q,y)
    have hβ := hβ1 y hy
    have hβ0 : 0 ≤ BETA q δr Ar p y := zero_le_one.trans hβ
    refine (le_of_eq (norm_triple_halfPairing hO hD
      (referenceDensityFamily g L (q,y))
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i)
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y)
      (IH (VF δr Ar p q hreg δ0 W F0 j y)) (BH (Uin F0 y)) hμ)).trans ?_
    have hin := (abs_inner_KL_le hO hD _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hEn j y) (hBn y) (norm_nonneg _) (by positivity)) hK2)
    have hX : referenceDensityFamily g L (q,y) *
        |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i| *
        |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y| *
        |⟪KL (IH (VF δr Ar p q hreg δ0 W F0 j y)), KL (BH (Uin F0 y))⟫_ℝ| ≤
        referenceDensityFamily g L (q,y) * (referenceRadius δr Ar p L y)^2 *
          (0 * (‖Uin F0 y‖ *
            ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
          c2 * BETA q δr Ar p y * (‖Uin F0 y‖ * ‖Uin F0 y‖)) := by
      calc _ ≤ referenceDensityFamily g L (q,y) * (Cf * BETA q δr Ar p y) *
            ((referenceRadius δr Ar p L y)^2 * CQ) *
            (‖KL‖^2 * ((CE * ‖Uin F0 y‖) * (‖BH‖ * ‖Uin F0 y‖))) :=
            mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hf y hy i) hμ.le) (hSa y hy i j)
              (abs_nonneg _) (by positivity)) hin (abs_nonneg _) (by positivity)
        _ = _ := by rw [hc2]; ring
    have hm := maj_absorb _ _ _ _ _ _ _ _ hμ.le (sq_nonneg _) (norm_nonneg _)
      (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hβ le_rfl (by positivity) hX
    unfold secondMajorant
    refine hm.trans (le_of_eq ?_)
    ring
  · exact norm_scalar_pairing_zero _ _ _
      (by simpa only [map_zero] using congrArg IH (hV0 j y hy)) _ _ (hMJ0 y hy)

private lemma second_form_pG3_bound (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p))
    (D : SecondFormPointwiseData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc) (c3 : ℝ)
    (hc3 : c3 = Cc * ‖KL‖^2 * ‖IH‖ * CE) :
    ∀ i j : Fin 3, ∀ y, ‖ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) y *
      PP (IH (Uin F0 y)) (JL (IH (VF δr Ar p q hreg δ0 W F0 j y)))‖ ≤ c3 * MJ δr Ar p q F0 y := by
  have hU0 := D.hU0
  have hIn := D.hIn
  have hEn := D.hEn
  have hMJ0 := D.hMJ0
  have hK2 : 0 ≤ ‖KL‖^2 := sq_nonneg _
  have hIH : 0 ≤ ‖IH‖ := ContinuousLinearMap.opNorm_nonneg _
  have hc3nn : 0 ≤ c3 := by rw [hc3]; positivity
  intro i j y
  by_cases hy : y ∈ TS F0
  · have hμ := referenceDensityFamily_pos g hg L (q,y)
    have hβ := hβ1 y hy
    have hβ0 : 0 ≤ BETA q δr Ar p y := zero_le_one.trans hβ
    rw [norm_scalar_halfPairing hO hD]
    have hin := (abs_inner_KL_le hO hD _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hIn y) (hEn j y) (norm_nonneg _) (by positivity)) hK2)
    have hX : |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) y| *
        |⟪KL (IH (Uin F0 y)), KL (IH (VF δr Ar p q hreg δ0 W F0 j y))⟫_ℝ| ≤
        referenceDensityFamily g L (q,y) * (referenceRadius δr Ar p L y)^2 *
          (0 * (‖Uin F0 y‖ *
            ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖) +
          c3 * BETA q δr Ar p y * (‖Uin F0 y‖ * ‖Uin F0 y‖)) := by
      calc _ ≤ (Cc * referenceDensityFamily g L (q,y) * (referenceRadius δr Ar p L y)^2 *
              BETA q δr Ar p y) * (‖KL‖^2 * ((‖IH‖ * ‖Uin F0 y‖) * (CE * ‖Uin F0 y‖))) :=
            mul_le_mul (hc y hy i j) hin (abs_nonneg _) (by positivity)
        _ = _ := by rw [hc3]; ring
    have hm := maj_absorb _ _ _ _ _ _ _ _ hμ.le (sq_nonneg _) (norm_nonneg _)
      (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hβ le_rfl (by positivity) hX
    unfold secondMajorant
    refine hm.trans (le_of_eq ?_)
    ring
  · exact norm_scalar_pairing_zero _ _ _
      (by simpa only [map_zero] using congrArg IH (hU0 y hy)) _ _ (hMJ0 y hy)

private lemma second_form_pZ_bound (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p))
    (D : SecondFormPointwiseData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc) (cZ : ℝ)
    (hcZ : cZ = 9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) + 3 * Cb * ‖KL‖^2 * ‖IH‖ * CE) :
    ∀ y, ‖referenceDensityFamily g L (q,y) * ZG hreg δ0 W g2 δr Ar p q F0 y‖ ≤
      cZ * MJ δr Ar p q F0 y := by
  intro y
  by_cases hy : y ∈ TS F0
  · let N : ℝ := ‖Uin F0 y‖
    let s : ℝ := ∑ k : Fin 3, ‖IH (fderiv ℝ (Uin F0) y (referenceMetricGramFrame g L (q,y) k))‖
    let b : ℝ := BETA q δr Ar p y
    have hN : 0 ≤ N := norm_nonneg _
    have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hb1 : 1 ≤ b := hβ1 y hy
    have hi : 0 ≤ ‖IH‖ := ContinuousLinearMap.opNorm_nonneg _
    have hV : ∀ k : Fin 3, |⟪F0.val y,KL (IH (VF δr Ar p q hreg δ0 W F0 k y))⟫_ℝ| ≤
        ‖KL‖^2*(‖IH‖*CE)*(N*N) := by
      intro k
      have he := congrArg (fun z : SphereL2 =>
        ⟪z,KL (IH (VF δr Ar p q hreg δ0 W F0 k y))⟫_ℝ) (D.hFx y)
      exact (le_of_eq (congrArg abs he)).trans
        (inner_from_caps KL (IH (Uin F0 y)) (IH (VF δr Ar p q hreg δ0 W F0 k y))
          ‖IH‖ CE N hi hCE hN (D.hIn y) (D.hEn k y))
    have hY : ∀ i j : Fin 3,
        |⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y j),
          KL (eH i ((Tq δr Ar p q) y) (Uin F0 y))⟫_ℝ| ≤
        ‖KL‖^2*CrE*(N*s)+‖KL‖^2*CrE*CD*b*(N*N) := by
      intro i j
      exact inner_from_linear_caps KL
        (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y j)
        (eH i ((Tq δr Ar p q) y) (Uin F0 y)) CrE CD b N s hCrE hCD
        (zero_le_one.trans hb1) hN hs (D.hDd y hy j) (D.hrn i y)
    have hz := scalar_zero_form_bound (referenceDensityFamily g L (q,y)) (referenceRadius δr Ar p L y)
      N s b (‖KL‖^2) ‖IH‖ CE CrE CD Cf CG Cb CQ
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
      (fun i j => ⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) y j),
        KL (eH i ((Tq δr Ar p q) y) (Uin F0 y))⟫_ℝ)
      (fun i j k => referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j)
      (fun i => referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i)
      (fun k => ⟪F0.val y,KL (IH (VF δr Ar p q hreg δ0 W F0 k y))⟫_ℝ)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,y))
      (referenceDensityFamily_pos g hg L (q,y)).le hN hs hb1 (sq_nonneg _) hi hCE hCrE hCD hCf hCG hCb hCQ
      (hQ y hy) hY (hf y hy) hV (fun i j k => hΓ y hy i k j) (hb y hy)
    rw [hcZ]
    exact hz
  · have hz : ZG hreg δ0 W g2 δr Ar p q F0 y = 0 := by
      unfold secondZeroGram
      simp only [D.hU0 y hy, D.hV0 _ y hy, map_zero, inner_zero_right,
        Finset.sum_const_zero, mul_zero, zero_mul, zero_add, add_zero, sub_zero]
    rw [hz,D.hMJ0 y hy]
    simp


theorem second_form_of_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ Cf CD CG Cb Cc : ℝ) (hCE : 0 ≤ CE) (hCrE : 0 ≤ CrE) (hCQ : 0 ≤ CQ)
    (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD) (hCG : 0 ≤ CG) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (hQ : ∀ x ∈ TS F0, ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ)
    (hf : ∀ x ∈ TS F0, ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf * BETA q δr Ar p x)
    (hDW : ∀ x ∈ TS F0, ∀ i : Fin 3,
      ‖referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i‖ ≤
        ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖ +
          CD * BETA q δr Ar p x * ‖Uin F0 x‖)
    (hΓ : ∀ x ∈ TS F0, ∀ i k j : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j| ≤ CG)
    (hb : ∀ x ∈ TS F0, ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb)
    (hc : ∀ x ∈ TS F0, ∀ i j : Fin 3,
      |ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
          (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x| ≤
        Cc * referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^2 * BETA q δr Ar p x)
    (hβc : Continuous (BETA q δr Ar p)) :
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
    Integrable (MJ δr Ar p q F0) ∧
    |∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
      (9 * (CQ * ‖KL‖^2 * CE * (1 + CD) + 2 * (Cf * CQ * ‖KL‖^2 * CE * ‖BH‖) +
          Cc * ‖KL‖^2 * ‖IH‖ * CE) +
        (9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
          3 * Cb * ‖KL‖^2 * ‖IH‖ * CE)) *
        ∫ x, MJ δr Ar p q F0 x := by
  have D := second_form_pointwise_data g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc
  have I := second_form_integral_data g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc
  have hPi := I.hPi
  have hMJi := I.hMJi
  have hIntEq := I.hIntEq
  have hMJnn := D.hMJnn
  have hGreen := fun i j => ActualOriginalSDirectPhysicalForm.green_second_D_row g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF
    (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j)
    (ActualHigherSSecondAdjoint.contDiff_secondCoefficient g g2 hg hg2 L q δr Ar p hδr hAr i j) i j
  -- constants
  let c1 : ℝ := CQ * ‖KL‖^2 * CE * (1 + CD)
  have hc1 : c1 = CQ * ‖KL‖^2 * CE * (1 + CD) := rfl
  let c2 : ℝ := Cf * CQ * ‖KL‖^2 * CE * ‖BH‖
  have hc2 : c2 = Cf * CQ * ‖KL‖^2 * CE * ‖BH‖ := rfl
  let c3 : ℝ := Cc * ‖KL‖^2 * ‖IH‖ * CE
  have hc3 : c3 = Cc * ‖KL‖^2 * ‖IH‖ * CE := rfl
  let cZ : ℝ := 9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
    3 * Cb * ‖KL‖^2 * ‖IH‖ * CE
  have hcZ : cZ = 9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
    3 * Cb * ‖KL‖^2 * ‖IH‖ * CE := rfl
  have hK2 : 0 ≤ ‖KL‖^2 := sq_nonneg _
  have hIH : 0 ≤ ‖IH‖ := ContinuousLinearMap.opNorm_nonneg _
  have hBH : 0 ≤ ‖BH‖ := ContinuousLinearMap.opNorm_nonneg _
  have pG1 := second_form_pG1_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc D c1 hc1
  have pG2 := second_form_pG2_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc D c2 hc2
  have pG3 := second_form_pG3_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc D c3 hc3
  have pZ := second_form_pZ_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE hCrE hCQ hCf hCD hCG hCb hCc hE hβ1 hQ hf hDW hΓ hb hc hβc D cZ hcZ
  -- integrated bound
  have hint : ∀ (G : R3 → ℝ) (c : ℝ), (∀ y, ‖G y‖ ≤ c * MJ δr Ar p q F0 y) →
      |∫ y, G y| ≤ c * ∫ y, MJ δr Ar p q F0 y := fun G c hG => by
    have h := norm_integral_le_of_norm_le (hMJi.const_mul c) (ae_of_all _ hG)
    rwa [integral_const_mul, Real.norm_eq_abs] at h
  have hMint0 : 0 ≤ ∫ y, MJ δr Ar p q F0 y := integral_nonneg hMJnn
  refine ⟨hPi, hMJi, ?_⟩
  rw [hIntEq]
  have hrowI : ∀ i j : Fin 3, |∫ y, referenceDensityFamily g L (q,y) *
      ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
      PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
        (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))| ≤
      (c1 + 2 * c2 + c3) * ∫ y, MJ δr Ar p q F0 y := by
    intro i j
    rw [hGreen i j]
    have e1 := hint _ _ (pG1 i j)
    have e2 := hint _ _ (pG2 i j)
    have e3 := hint _ _ (pG3 i j)
    calc _ ≤ |∫ y, referenceDensityFamily g L (q,y) *
            ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
            PP (IH (VF δr Ar p q hreg δ0 W F0 j y)) (JL (referenceHighWeightedHorizontalAction g L q
              (referenceRadius δr Ar p L) (Uin F0) y i))| +
          2 * |∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i *
            ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j y *
            PP (IH (VF δr Ar p q hreg δ0 W F0 j y))
              (JL (BH (Uin F0 y)))| +
          |∫ y, ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
              (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) y *
            PP (IH (Uin F0 y)) (JL (IH (VF δr Ar p q hreg δ0 W F0 j y)))| := by
          exact abs_signed_three _ _ _
      _ ≤ c1 * (∫ y, MJ δr Ar p q F0 y) + 2 * (c2 * ∫ y, MJ δr Ar p q F0 y) +
            c3 * ∫ y, MJ δr Ar p q F0 y := by
          refine add_le_add (add_le_add e1 (mul_le_mul_of_nonneg_left e2 (by norm_num))) ?_
          unfold ActualHigherSSecondAdjoint.densityDerivativeCoefficient at e3 ⊢
          exact e3
      _ = _ := by ring
  have hZI := hint _ _ pZ
  calc _ ≤ 9 * ((c1 + 2 * c2 + c3) * ∫ y, MJ δr Ar p q F0 y) + cZ * ∫ y, MJ δr Ar p q F0 y :=
        (abs_add_le'' _ _).trans (add_le_add (abs_sum33_le _ _ hrowI) hZI)
    _ = _ := by rw [hc1, hc2, hc3, hcZ]; ring

/-! ## 5. FINAL original secondS form, all caps discharged -/

/-- Caller's retained `W`; `δ, Cm` before `g2`; `K` after fixed admissible `g2`, BEFORE every
profile, input, point. The extra hypothesis is continuity of the native `β`. -/
theorem exists_retained_original_secondS_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0)
    (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q : ℝ,
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
          Continuous (BETA q δr Ar p) →
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
          Integrable (MJ δr Ar p q F0) ∧
          |∫ x, referenceDensityFamily g L (q,x) *
              ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
            K * ∫ x, MJ δr Ar p q F0 x := by
  obtain ⟨δ, Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨CE, CrE, hCE, hCrE, hE⟩ := ActualOriginalSDirectPhysicalForm.exists_room_E_operator_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  obtain ⟨CD, hCD, hDW⟩ := ActualWeightedHorizontalActionBounds.exists_weighted_horizontal_uniform_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cf, hCf, hf⟩ := ActualSScalarCoefficientBounds.exists_profile_horizontal_log_derivative_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨CG, hCG, hGeo⟩ := exists_reference_geometry_uniform_bounds g hg L (closedBall y0 ρ)
    (isCompact_closedBall y0 ρ)
  refine ⟨δ, Cm.rev.pos, Cm, fun g2 hg2 => ?_⟩
  obtain ⟨CQ, hCQ, hQF⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    (g := g) (L := L) (y0 := y0) (ρ := ρ) (hg := hg) g2 hg2
  obtain ⟨Cc, hCc, hcF⟩ := exists_second_density_coefficient_bound g g2 hg hg2 L hL y0 ρ
  have hbK : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i : Fin 3,
      |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb := by
    obtain ⟨M, hMb⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod (isCompact_closedBall y0 ρ)).exists_bound_of_continuousOn
      (f := fun t : ℝ × R3 => ∑ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i t|)
      (continuous_finset_sum _ (fun i _ =>
        (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.abs)).continuousOn
    refine ⟨|M|, abs_nonneg _, fun q hq x hx i => ?_⟩
    have h1 := hMb (q,x) ⟨hq, hx⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _))] at h1
    exact (Finset.single_le_sum (f := fun k : Fin 3 => |normalizedSecondDriftFrameJoint g g2 L k (q,x)|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i)).trans (h1.trans (le_abs_self _))
  obtain ⟨Cb, hCb, hbF⟩ := hbK
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCrE0 : 0 ≤ CrE := zero_le_one.trans hCrE
  refine ⟨(9 * (CQ * ‖KL‖^2 * CE * (1 + CD) + 2 * (Cf * CQ * ‖KL‖^2 * CE * ‖BH‖) +
          Cc * ‖KL‖^2 * ‖IH‖ * CE) +
        (9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
          3 * Cb * ‖KL‖^2 * ‖IH‖ * CE)), by positivity, ?_⟩
  intro δr Ar p hδr hδr1 hAr hp q F0 hTF hβ1 hβc
  have hqx : ∀ x ∈ TS F0, q ∈ Icc (0 : ℝ) 1 ∧ x ∈ closedBall y0 ρ := fun x hx =>
    paramRoom_q_ball' L y0 ρ δr Ar p q δ x (hTF x hx)
  exact second_form_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2
    δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE0 hCrE0 hCQ0 hCf hCD hCG0 hCb hCc hE hβ1
    (fun x hx i j => (hQF q (hqx x hx).1 x (hqx x hx).2 i j).1)
    (fun x hx i => hf δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) i)
    (fun x hx i => hDW δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) (Uin F0) i)
    (fun x hx i k j => ((hGeo q (hqx x hx).1 x (hqx x hx).2).2.2.2 i k j))
    (fun x hx i => hbF q (hqx x hx).1 x (hqx x hx).2 i)
    (fun x hx i j => hcF δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) i j)
    hβc

/-! ## 6. FINAL full literal S (`nativeHigherSHalf`/`nativeHigherSOut`) on ONE common room -/

private lemma full_profile_form_from_components
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hβ1 : ∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x)
    (KS KA KD : ℝ) (hKS0 : 0 ≤ KS) (hKA0 : 0 ≤ KA) (hKD0 : 0 ≤ KD)
    (hSecond : Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F0.val x,KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
      Integrable (MJ δr Ar p q F0) ∧
      |∫ x, referenceDensityFamily g L (q,x)*
        ⟪F0.val x,KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ| ≤ KS*∫ x, MJ δr Ar p q F0 x)
    (hAngular : Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        (referenceRadius δr Ar p L x*(‖Uin F0 x‖*‖Uin F0 x‖))) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F0.val x,KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
        KA*∫ x, referenceDensityFamily g L (q,x)*(referenceRadius δr Ar p L x*(‖Uin F0 x‖*‖Uin F0 x‖)))
    (hDouble : Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F0.val x,KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*(referenceRadius δr Ar p L x)^3*
        (‖Uin F0 x‖*‖Uin F0 x‖)) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F0.val x,KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
        KD*∫ x, referenceDensityFamily g L (q,x)*(referenceRadius δr Ar p L x)^3*(‖Uin F0 x‖*‖Uin F0 x‖)) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ) ∧
      Integrable (FM δr Ar p q F0) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F0.val x,SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ| ≤
        (KS+KA+KD)*∫ x, FM δr Ar p q F0 x := by
  obtain ⟨hSi,hMJi,hSb⟩ := hSecond
  obtain ⟨hAi,hAMi,hAb⟩ := hAngular
  obtain ⟨hDi,hDMi,hDb⟩ := hDouble
  have hU0 : ∀ z ∉ TS F0, Uin F0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hsplit : ∀ x, referenceDensityFamily g L (q,x) *
      ⟪F0.val x, SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ =
      referenceDensityFamily g L (q,x) * ⟪F0.val x, KL (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)⟫_ℝ +
        referenceDensityFamily g L (q,x) * ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ +
        referenceDensityFamily g L (q,x) * ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ := by
    intro x
    exact density_inner_sum_three KL (F0.val x) (referenceDensityFamily g L (q,x))
      (SS δr Ar p hδr hAr q hreg δ0 W g2 F0 x)
      (FA δr Ar p q hreg δ0 W g2 F0 x) (FD δr Ar p q hreg δ0 W g2 F0 x)
  have hFsplit : ∀ x, FM δr Ar p q F0 x = MJ δr Ar p q F0 x +
      referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖)) +
      referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin F0 x‖) := by
    intro x
    exact full_majorant_split_real (referenceDensityFamily g L (q,x)) (referenceRadius δr Ar p L x)
      ‖Uin F0 x‖ (∑ i : Fin 3, ‖IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))‖)
      (BETA q δr Ar p x)
  have hnn : ∀ x, 0 ≤ referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x *
      (‖Uin F0 x‖ * ‖Uin F0 x‖)) := fun x => by
    have := (referenceDensityFamily_pos g hg L (q,x)).le
    have := (referenceRadius_pos δr Ar p L x hδr hAr).le
    positivity
  have hnn3 : ∀ x, 0 ≤ referenceDensityFamily g L (q,x) * (referenceRadius δr Ar p L x)^3 *
      (‖Uin F0 x‖ * ‖Uin F0 x‖) := fun x => by
    have := (referenceDensityFamily_pos g hg L (q,x)).le
    have := (referenceRadius_pos δr Ar p L x hδr hAr).le
    positivity
  have hMnn : ∀ x, 0 ≤ MJ δr Ar p q F0 x := fun x => by
    unfold secondMajorant
    by_cases hx : x ∈ TS F0
    · have := zero_le_one.trans (hβ1 x hx)
      have := (referenceDensityFamily_pos g hg L (q,x)).le
      positivity
    · simp [hU0 x hx]
  exact combine_three_forms _ _ _ _ _ _ _ _ KS KA KD hKS0 hKA0 hKD0
    hSi hAi hDi hMJi hAMi hDMi hsplit hFsplit hMnn hnn hnn3 hSb hAb hDb

theorem exists_retained_original_fullS_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0)
    (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 → ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q : ℝ,
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
          Continuous (BETA q δr Ar p) →
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            ⟪F0.val x, SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ) ∧
          Integrable (FM δr Ar p q F0) ∧
          |∫ x, referenceDensityFamily g L (q,x) *
              ⟪F0.val x, SO δr Ar p hδr hAr q hreg δ0 W g2 F0 x⟫_ℝ| ≤
            K * ∫ x, FM δr Ar p q F0 x := by
  obtain ⟨δ, Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨CE, CrE, hCE, hCrE, hE⟩ := ActualOriginalSDirectPhysicalForm.exists_room_E_operator_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  obtain ⟨CL, CA, hCL, hCA, hA⟩ := ActualOriginalSDirectPhysicalForm.exists_angular_clm_bounds hF hO hD
  obtain ⟨CD, hCD, hDW⟩ := ActualWeightedHorizontalActionBounds.exists_weighted_horizontal_uniform_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cf, hCf, hf⟩ := ActualSScalarCoefficientBounds.exists_profile_horizontal_log_derivative_bound
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨CG, hCG, hGeo⟩ := exists_reference_geometry_uniform_bounds g hg L (closedBall y0 ρ)
    (isCompact_closedBall y0 ρ)
  refine ⟨δ, Cm.rev.pos, Cm, fun g2 hg2 => ?_⟩
  obtain ⟨CQ, hCQ, hQF⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    (g := g) (L := L) (y0 := y0) (ρ := ρ) (hg := hg) g2 hg2
  obtain ⟨Cc, hCc, hcF⟩ := exists_second_density_coefficient_bound g g2 hg hg2 L hL y0 ρ
  have hbK : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i : Fin 3,
      |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Cb := by
    obtain ⟨M, hMb⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod (isCompact_closedBall y0 ρ)).exists_bound_of_continuousOn
      (f := fun t : ℝ × R3 => ∑ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i t|)
      (continuous_finset_sum _ (fun i _ =>
        (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.abs)).continuousOn
    refine ⟨|M|, abs_nonneg _, fun q hq x hx i => ?_⟩
    have h1 := hMb (q,x) ⟨hq, hx⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _))] at h1
    exact (Finset.single_le_sum (f := fun k : Fin 3 => |normalizedSecondDriftFrameJoint g g2 L k (q,x)|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i)).trans (h1.trans (le_abs_self _))
  obtain ⟨Cb, hCb, hbF⟩ := hbK
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCrE0 : 0 ≤ CrE := zero_le_one.trans hCrE
  have hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ :=
    fun q hq x hx i j => (hQF q hq x hx i j).1
  let KS : ℝ := (9 * (CQ * ‖KL‖^2 * CE * (1 + CD) + 2 * (Cf * CQ * ‖KL‖^2 * CE * ‖BH‖) +
          Cc * ‖KL‖^2 * ‖IH‖ * CE) +
        (9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
          3 * Cb * ‖KL‖^2 * ‖IH‖ * CE))
  have hKS : KS = (9 * (CQ * ‖KL‖^2 * CE * (1 + CD) + 2 * (Cf * CQ * ‖KL‖^2 * CE * ‖BH‖) +
          Cc * ‖KL‖^2 * ‖IH‖ * CE) +
        (9 * CQ * ‖KL‖^2 * (CrE * (1 + CD) + Cf * ‖IH‖ * CE + 3 * CG * ‖IH‖ * CE) +
          3 * Cb * ‖KL‖^2 * ‖IH‖ * CE)) := rfl
  let KA : ℝ := 9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE)
  have hKA : KA = 9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE) := rfl
  let KD : ℝ := 9 * CQ * ‖KL‖^2 * CE * CrE
  have hKD : KD = 9 * CQ * ‖KL‖^2 * CE * CrE := rfl
  have hKS0 : 0 ≤ KS := by rw [hKS]; positivity
  have hKA0 : 0 ≤ KA := by rw [hKA]; positivity
  have hKD0 : 0 ≤ KD := by rw [hKD]; positivity
  have hDC := OriginalDoubleEForm.originalDoubleEFormContract_of_bounds g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 CE CrE CQ hCQ0 hE hQ
  refine ⟨KS + KA + KD, by positivity, ?_⟩
  intro δr Ar p hδr hδr1 hAr hp q F0 hTF hβ1 hβc
  have hqx : ∀ x ∈ TS F0, q ∈ Icc (0 : ℝ) 1 ∧ x ∈ closedBall y0 ρ := fun x hx =>
    paramRoom_q_ball' L y0 ρ δr Ar p q δ x (hTF x hx)
  obtain ⟨hSi, hMJi, hSb⟩ := second_form_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ Cf CD CG Cb Cc hCE0 hCrE0 hCQ0 hCf hCD
    hCG0 hCb hCc hE hβ1
    (fun x hx i j => hQ q (hqx x hx).1 x (hqx x hx).2 i j)
    (fun x hx i => hf δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) i)
    (fun x hx i => hDW δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) (Uin F0) i)
    (fun x hx i k j => ((hGeo q (hqx x hx).1 x (hqx x hx).2).2.2.2 i k j))
    (fun x hx i => hbF q (hqx x hx).1 x (hqx x hx).2 i)
    (fun x hx i j => hcF δr Ar p hδr hδr1 hAr hp q (hqx x hx).1 x (hqx x hx).2 (hβ1 x hx) i j)
    hβc
  -- the angular bound on the SAME room: its `hQ` premise is global on `[0,1] × ball`
  have hAI := ActualOriginalSDirectPhysicalForm.integrated_angular_bound_of_bounds g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ CL CA hCQ0
    hE hA hQ
  obtain ⟨hAi, hAMi, hAb⟩ := hAI
  obtain ⟨-, -, -, -, -, hDi, -, -, hDMi, -, -, hDb, -⟩ := hDC δr Ar p hδr hAr q F0 F0 hTF hTF
  exact full_profile_form_from_components g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W g2 δr Ar p hδr hAr q F0 hβ1 KS KA KD hKS0 hKA0 hKD0
    ⟨hSi,hMJi,hSb⟩ ⟨hAi,hAMi,hAb⟩ ⟨hDi,hDMi,hDb⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalFormBounds
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalFormBounds.exists_second_density_coefficient_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalFormBounds.exists_retained_original_secondS_form
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalFormBounds.exists_retained_original_fullS_form
