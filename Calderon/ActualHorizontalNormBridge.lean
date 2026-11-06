import Calderon.ActualHorizontalGraph

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualHorizontalNormBridge
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication SmoothSphereRotationProjection
  SmoothSphereRotationBounds SmoothMovingFrameFields AmbientReferenceCovariantCore
  MovingFrameConnection SmoothMetricFrame MetricOperator ConformalDepth RadiusProfile
  ReferenceDensityBounds ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  SectionFiveErrorForms BaseDensityAdjoint WeightedBaseSpectral

lemma norm_sum_smul_sq_le (c : Fin 3 → ℝ) (v : Fin 3 → SphereL2)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, |c i| ≤ M) :
    ‖∑ i : Fin 3, c i • v i‖^2 ≤ 3*M^2*(∑ i : Fin 3, ‖v i‖^2) := by
  have hn : ‖∑ i : Fin 3, c i • v i‖ ≤ M*(∑ i : Fin 3, ‖v i‖) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖c i • v i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, M*‖v i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hsq : (∑ i : Fin 3, ‖v i‖)^2 ≤ 3*(∑ i : Fin 3, ‖v i‖^2) := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),
      sq_nonneg (‖v 1‖-‖v 2‖)]
  calc
    _ ≤ (M*(∑ i : Fin 3, ‖v i‖))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM
        (Finset.sum_nonneg fun i _ => norm_nonneg _))).2 hn
    _ = M^2*(∑ i : Fin 3, ‖v i‖)^2 := by ring
    _ ≤ M^2*(3*(∑ i : Fin 3, ‖v i‖^2)) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

lemma norm_sq_le_two_add_diff (u v : SphereL2) :
    ‖u‖^2 ≤ 2*‖v‖^2+2*‖u-v‖^2 := by
  have hn : ‖u‖ ≤ ‖v‖+‖u-v‖ := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  nlinarith [sq_nonneg (‖v‖-‖u-v‖)]

lemma sum_norm_sq_le_of_connection_correction
    (u v horizontal : Fin 3 → SphereL2) (c : Fin 3 → Fin 3 → ℝ)
    (higher : SphereL2) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ k i, |c k i| ≤ M)
    (hv : ∀ k, v k = ∑ i, c k i • horizontal i)
    (hdiff : ∀ k, ‖u k-v k‖ ≤ 9*M*‖higher‖) :
    (∑ k : Fin 3, ‖u k‖^2) ≤
      18*M^2*(∑ i : Fin 3, ‖horizontal i‖^2)+486*M^2*‖higher‖^2 := by
  have hterm (k : Fin 3) : ‖u k‖^2 ≤
      6*M^2*(∑ i : Fin 3, ‖horizontal i‖^2)+162*M^2*‖higher‖^2 := by
    have hvk : ‖v k‖^2 ≤ 3*M^2*(∑ i : Fin 3, ‖horizontal i‖^2) := by
      rw [hv k]
      exact norm_sum_smul_sq_le _ _ M hM (hc k)
    have hdk : ‖u k-v k‖^2 ≤ 81*M^2*‖higher‖^2 := by
      calc
        _ ≤ (9*M*‖higher‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hdiff k)
        _ = _ := by ring
    have hh := norm_sq_le_two_add_diff (u k) (v k)
    nlinarith only [hh,hvk,hdk]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  apply hh.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma coordinate_base_square_le_horizontal
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (U : R3 → SphereL2) (rotations : Fin 3 → Fin 3 → R3 → SphereL2)
    (x : R3) (higher : SphereL2) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ k i, |referenceCoFrameEntry g L k i (lam,x)| ≤ M)
    (hcorrection : ∀ k,
      ‖referenceHorizontalField g L lam U rotations x (coordinateDirection k) -
        fderiv ℝ U x (coordinateDirection k)‖ ≤ 9*M*‖higher‖) :
    (∑ k : Fin 3, ‖fderiv ℝ U x (coordinateDirection k)‖^2) ≤
      18*M^2*(∑ i : Fin 3, ‖referenceHorizontalField g L lam U rotations x
        (referenceMetricGramFrame g L (lam,x) i)‖^2)+486*M^2*‖higher‖^2 := by
  apply sum_norm_sq_le_of_connection_correction
    (fun k => fderiv ℝ U x (coordinateDirection k))
    (fun k => referenceHorizontalField g L lam U rotations x (coordinateDirection k))
    (fun i => referenceHorizontalField g L lam U rotations x (referenceMetricGramFrame g L (lam,x) i))
    (fun k i => referenceCoFrameEntry g L k i (lam,x)) higher M hM he
  · intro k
    rw [coordinateDirection_eq_sum_referenceGramFrame g hg L lam x k]
    exact referenceHorizontalField_sum g L lam U rotations x _ _
  · intro k
    simpa only [norm_sub_rev] using hcorrection k

lemma horizontal_base_square_le_coordinate
    (g : MatrixField) (L lam : ℝ) (U : R3 → SphereL2)
    (rotations : Fin 3 → Fin 3 → R3 → SphereL2) (x : R3)
    (higher : SphereL2) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i k, |frameEntry g L i k (lam,x)| ≤ M)
    (hcorrection : ∀ i,
      ‖referenceHorizontalField g L lam U rotations x (referenceMetricGramFrame g L (lam,x) i) -
        fderiv ℝ U x (referenceMetricGramFrame g L (lam,x) i)‖ ≤ 9*M*‖higher‖) :
    (∑ i : Fin 3, ‖referenceHorizontalField g L lam U rotations x
      (referenceMetricGramFrame g L (lam,x) i)‖^2) ≤
      18*M^2*(∑ k : Fin 3, ‖fderiv ℝ U x (coordinateDirection k)‖^2)+486*M^2*‖higher‖^2 := by
  apply sum_norm_sq_le_of_connection_correction
    (fun i => referenceHorizontalField g L lam U rotations x (referenceMetricGramFrame g L (lam,x) i))
    (fun i => fderiv ℝ U x (referenceMetricGramFrame g L (lam,x) i))
    (fun k => fderiv ℝ U x (coordinateDirection k))
    (fun i k => frameEntry g L i k (lam,x)) higher M hM he
  · intro i
    rw [referenceGramFrame_eq_sum_coordinateDirection g L lam x i]
    simp only [map_sum,map_smul]
  · exact hcorrection

lemma four_term_comparison (beta M : ℝ) (hbeta : 1 ≤ beta)
    (uZero vZero uHalf vHalf : Fin 3 → SphereL2) (one three : SphereL2)
    (hzero : (∑ i, ‖uZero i‖^2) ≤ 18*M^2*(∑ i, ‖vZero i‖^2)+486*M^2*‖one‖^2)
    (hhalf : (∑ i, ‖uHalf i‖^2) ≤ 18*M^2*(∑ i, ‖vHalf i‖^2)+486*M^2*‖three‖^2) :
    sourceNormSquareIntegrand beta uZero one uHalf three ≤
      (504*M^2+1)*sourceNormSquareIntegrand beta vZero one vHalf three := by
  have hp : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hbinv : beta⁻¹ ≤ beta := by
    apply (mul_le_mul_iff_right₀ hp).mp
    simpa only [inv_mul_cancel₀ hp.ne',mul_inv_cancel₀ hp.ne',← pow_two] using hb2
  let V := (∑ i, ‖vZero i‖^2)+beta⁻¹*(∑ i, ‖vHalf i‖^2)
  let A := beta^2*‖one‖^2+beta*‖three‖^2
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsmall : ‖one‖^2+beta⁻¹*‖three‖^2 ≤ A := by
    exact add_le_add
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖one‖))
      (mul_le_mul_of_nonneg_right hbinv (sq_nonneg ‖three‖))
  calc
    _ ≤ (18*M^2*V)+(486*M^2*(‖one‖^2+beta⁻¹*‖three‖^2))+A := by
      have hh := mul_le_mul_of_nonneg_left hhalf (inv_nonneg.mpr hp.le)
      unfold sourceNormSquareIntegrand
      dsimp only [V,A]
      nlinarith only [hzero,hh]
    _ ≤ (18*M^2*V)+(486*M^2*A)+A := by
      have hcor : 486*M^2*(‖one‖^2+beta⁻¹*‖three‖^2) ≤ 486*M^2*A :=
        mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 486*M^2 by positivity)
      exact add_le_add (add_le_add (le_refl (18*M^2*V)) hcor) (le_refl A)
    _ ≤ (18*M^2*(V+A))+(486*M^2*(V+A))+(V+A) := by
      gcongr <;> linarith
    _ = _ := by unfold sourceNormSquareIntegrand; dsimp only [V,A]; ring

def referenceHorizontalNormSquareIntegrand
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (beta : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : ℝ :=
  sourceNormSquareIntegrand (beta x)
    (fun i => referenceHorizontalZero g L lam G hG x (referenceMetricGramFrame g L (lam,x) i))
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (fun i => referenceHorizontalHalf hO hD g L lam G hG x (referenceMetricGramFrame g L (lam,x) i))
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)

/-- The manuscript N squared: actual Gram tensor slots and exact source angular weights. -/
def referenceHorizontalNormSquare
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (beta : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  sourceNormSquare g L lam beta
    (fun x i => referenceHorizontalZero g L lam G hG x (referenceMetricGramFrame g L (lam,x) i))
    (ambientBesselField hO hD 1 (by norm_num) G hG)
    (fun x i => referenceHorizontalHalf hO hD g L lam G hG x (referenceMetricGramFrame g L (lam,x) i))
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG)

theorem coordinate_horizontal_integrand_comparison
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (x : R3) (M : ℝ) (hM : 0 ≤ M) (hbeta : 1 ≤ beta x)
    (hf : ∀ i k, |frameEntry g L i k (lam,x)| ≤ M)
    (he : ∀ k i, |referenceCoFrameEntry g L k i (lam,x)| ≤ M)
    (hc : ∀ k a b, |referenceFrameConnectionCoefficient g L lam x (coordinateDirection k) a b| ≤ M)
    (hgC : ∀ i a b, |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a b| ≤ M) :
    let NC := sourceNormSquareIntegrand (beta x)
      (fun k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun k => directionalDeriv (coordinateDirection k)
        (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)
    NC ≤ (504*M^2+1)*referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG x ∧
      referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG x ≤ (504*M^2+1)*NC := by
  dsimp only
  have hC0 := coordinate_base_square_le_horizontal g hg L lam (ambientSphereL2 G hG)
    (fun a b => ambientRotationField a b G hG) x
    (ambientBesselField hO hD 1 (by norm_num) G hG x) M hM he
    (fun k => norm_referenceHorizontalZero_correction_le hO hD g L lam G hG x _ M hM (hc k))
  have hCh := coordinate_base_square_le_horizontal g hg L lam
    (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)
    (fun a b => ambientHalfRotationField hO hD a b G hG) x
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x) M hM he
    (fun k => norm_referenceHorizontalHalf_correction_le hO hD g L lam G hG x _ M hM (hc k))
  have hH0 := horizontal_base_square_le_coordinate g L lam (ambientSphereL2 G hG)
    (fun a b => ambientRotationField a b G hG) x
    (ambientBesselField hO hD 1 (by norm_num) G hG x) M hM hf
    (fun i => norm_referenceHorizontalZero_correction_le hO hD g L lam G hG x _ M hM (hgC i))
  have hHh := horizontal_base_square_le_coordinate g L lam
    (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG)
    (fun a b => ambientHalfRotationField hO hD a b G hG) x
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x) M hM hf
    (fun i => norm_referenceHorizontalHalf_correction_le hO hD g L lam G hG x _ M hM (hgC i))
  constructor
  · exact four_term_comparison (beta x) M hbeta _ _ _ _ _ _ hC0 hCh
  · exact four_term_comparison (beta x) M hbeta _ _ _ _ _ _ hH0 hHh

lemma contDiff_referenceHorizontalZero_field (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => referenceHorizontalZero g L lam G hG x (X x)) := by
  have he : (fun x => referenceHorizontalZero g L lam G hG x (X x)) =
      ambientSphereL2
        (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
        (contDiff_ambientFrameHorizontal _
          (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
          X hX G hG) := by
    funext x; exact (referenceHorizontalZero_eq_native g hg L lam X hX G hG x).symm
  rw [he]
  exact contDiff_ambientSphereL2 _ _

lemma contDiff_referenceHorizontalHalf_field
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => referenceHorizontalHalf hO hD g L lam G hG x (X x)) := by
  have he : (fun x => referenceHorizontalHalf hO hD g L lam G hG x (X x)) =
      ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
        (ambientFrameHorizontal (fun y => referenceFrameConnectionCoefficient g L lam y (X y)) X G)
        (contDiff_ambientFrameHorizontal _
          (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L lam X hX a b)
          X hX G hG) := by
    funext x; exact (referenceHorizontalHalf_eq_native hO hD g hg L lam X hX G hG x).symm
  rw [he]
  exact contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) _ _

lemma referenceHorizontalZero_eq_zero_off_compact (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsClosed K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceHorizontalZero g L lam G hG x (X x) = 0 := by
  rw [← referenceHorizontalZero_eq_native g hg L lam X hX G hG x]
  apply ambientSphereL2_eq_zero
  exact ambientFrameHorizontal_sphere_zero _
    (fun y a b => referenceFrameConnectionCoefficient_skew g hg L lam y (X y) a b)
    X G hG K hK hz x hx

lemma referenceHorizontalHalf_eq_zero_off_compact
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsClosed K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceHorizontalHalf hO hD g L lam G hG x (X x) = 0 := by
  rw [← referenceHorizontalHalf_eq_native hO hD g hg L lam X hX G hG x]
  apply ambientBesselField_eq_zero hO hD (1/2 : ℝ) (by norm_num) _ _ K _ x hx
  exact ambientFrameHorizontal_sphere_zero _
    (fun y a b => referenceFrameConnectionCoefficient_skew g hg L lam y (X y) a b)
    X G hG K hK hz

lemma integrable_reference_horizontal_norm_on_compact
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG x) := by
  have hH0 (i : Fin 3) : Continuous (fun x => referenceHorizontalZero g L lam G hG x
      (referenceMetricGramFrame g L (lam,x) i)) :=
    (contDiff_referenceHorizontalZero_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG).continuous
  have hHh (i : Fin 3) : Continuous (fun x => referenceHorizontalHalf hO hD g L lam G hG x
      (referenceMetricGramFrame g L (lam,x) i)) :=
    (contDiff_referenceHorizontalHalf_field hO hD g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG).continuous
  have hinv : Continuous (fun x => (beta x)⁻¹) := hbeta.inv₀ (fun x => (hpos x).ne')
  have hone := (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).continuous
  have hthree := (contDiff_ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG).continuous
  have hNN : Continuous (referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG) := by
    unfold referenceHorizontalNormSquareIntegrand sourceNormSquareIntegrand
    fun_prop
  have hcNN : HasCompactSupport (referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG) :=
    HasCompactSupport.intro hK (fun x hx => by
      have hzero (i : Fin 3) : referenceHorizontalZero g L lam G hG x
          (referenceMetricGramFrame g L (lam,x) i) = 0 :=
        referenceHorizontalZero_eq_zero_off_compact g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG K hK.isClosed hz x hx
      have hhalfzero (i : Fin 3) : referenceHorizontalHalf hO hD g L lam G hG x
          (referenceMetricGramFrame g L (lam,x) i) = 0 :=
        referenceHorizontalHalf_eq_zero_off_compact hO hD g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG K hK.isClosed hz x hx
      have honezero := ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx
      have hthreezero := ambientBesselField_eq_zero hO hD (3/2 : ℝ) (by norm_num) G hG K hz x hx
      simp [referenceHorizontalNormSquareIntegrand,sourceNormSquareIntegrand,
        hzero,hhalfzero,honezero,hthreezero])
  exact ((continuous_referenceBaseDensity g hg L lam).mul hNN).integrable_of_hasCompactSupport hcNN.mul_left

/-- Actual two-way comparison, with the constant chosen before every profile and radius. -/
theorem exists_coordinate_horizontal_norm_comparison
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ beta : R3 → ℝ, Continuous beta → (∀ x, 0 < beta x) → (∀ x ∈ K, 1 ≤ beta x) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      let NC := sourceNormSquare g L lam beta
        (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
        (ambientBesselField hO hD 1 (by norm_num) G hG)
        (fun x k => directionalDeriv (coordinateDirection k)
          (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
        (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG)
      NC ≤ C*referenceHorizontalNormSquare hO hD g L lam beta G hG ∧
        referenceHorizontalNormSquare hO hD g L lam beta G hG ≤ C*NC := by
  obtain ⟨M,hM,hgeom⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  refine ⟨504*M^2+1,by positivity,?_⟩
  intro lam hlam beta hbeta hpos hb G hG hz
  dsimp only
  let NC : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
    (fun k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x)
    (fun k => directionalDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
    (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)
  let NH := referenceHorizontalNormSquareIntegrand hO hD g L lam beta G hG
  have hNC : Integrable (fun x => referenceDensityFamily g L (lam,x)*NC x) :=
    integrable_ambient_source_norm_on_compact hO hD g hg L lam beta hbeta hpos G hG K hK hz
  have hNH : Integrable (fun x => referenceDensityFamily g L (lam,x)*NH x) :=
    integrable_reference_horizontal_norm_on_compact hO hD g hg L lam beta hbeta hpos G hG K hK hz
  have hpoint : ∀ x, NC x ≤ (504*M^2+1)*NH x ∧ NH x ≤ (504*M^2+1)*NC x := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨hf,he,hc,hgC⟩ := hgeom lam hlam x hx
      exact coordinate_horizontal_integrand_comparison hO hD g hg L lam beta G hG x M
        (by linarith) (hb x hx) hf he hc hgC
    · have hphi := contDiff_ambientSphereL2 G hG
      have hhalf := contDiff_ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG
      have hsupp : tsupport (ambientSphereL2 G hG) ⊆ K := by
        apply closure_minimal _ hK.isClosed
        intro y hy
        by_contra hyK
        change ambientSphereL2 G hG y ≠ 0 at hy
        exact hy (ambientSphereL2_eq_zero G hG y (hz y hyK))
      have hsupph := tsupport_ambientBesselField_subset hO hD (1/2 : ℝ) (by norm_num) G hG K hK hz
      have hdzero (k : Fin 3) : directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x = 0 :=
        directionalDeriv_eq_zero_off_support _ K hsupp _ x hx
      have hdhzero (k : Fin 3) : directionalDeriv (coordinateDirection k)
          (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x = 0 :=
        directionalDeriv_eq_zero_off_support _ K hsupph _ x hx
      have hH0zero (i : Fin 3) : referenceHorizontalZero g L lam G hG x
          (referenceMetricGramFrame g L (lam,x) i) = 0 :=
        referenceHorizontalZero_eq_zero_off_compact g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG K hK.isClosed hz x hx
      have hHhzero (i : Fin 3) : referenceHorizontalHalf hO hD g L lam G hG x
          (referenceMetricGramFrame g L (lam,x) i) = 0 :=
        referenceHorizontalHalf_eq_zero_off_compact hO hD g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam i) G hG K hK.isClosed hz x hx
      have honezero := ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx
      have hthreezero := ambientBesselField_eq_zero hO hD (3/2 : ℝ) (by norm_num) G hG K hz x hx
      simp [NC,NH,referenceHorizontalNormSquareIntegrand,sourceNormSquareIntegrand,
        hdzero,hdhzero,hH0zero,hHhzero,honezero,hthreezero]
  have hNHid : referenceHorizontalNormSquare hO hD g L lam beta G hG =
      ∫ x, referenceDensityFamily g L (lam,x)*NH x := by
    unfold referenceHorizontalNormSquare
    exact sourceNormSquare_eq_density_integral g hg L lam _ _ _ _ _
  have hNCid : sourceNormSquare g L lam beta
      (fun x k => directionalDeriv (coordinateDirection k) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG)
      (fun x k => directionalDeriv (coordinateDirection k)
        (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG) =
      ∫ x, referenceDensityFamily g L (lam,x)*NC x :=
    sourceNormSquare_eq_density_integral g hg L lam _ _ _ _ _
  rw [hNHid,hNCid]
  constructor
  · rw [← integral_const_mul]
    apply integral_mono hNC (hNH.const_mul _)
    intro x
    simpa only [mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left (hpoint x).1
      (referenceDensityFamily_pos g hg L (lam,x)).le
  · rw [← integral_const_mul]
    apply integral_mono hNH (hNC.const_mul _)
    intro x
    simpa only [mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left (hpoint x).2
      (referenceDensityFamily_pos g hg L (lam,x)).le

end OAI.AnisotropicCalderon.ActualHorizontalNormBridge
