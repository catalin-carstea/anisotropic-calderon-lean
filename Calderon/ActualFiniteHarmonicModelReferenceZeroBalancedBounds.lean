import Calderon.ActualFiniteHarmonicModelReferenceZeroBalanced
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualReferenceDDHigherCLMProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherLogFrameJets ActualReferenceDDHigherCLMProducts
  ActualReferenceModelTrace AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile MetricOperator ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroBoundFunction

theorem exists_nativeReferenceZeroDefectBalancedAngularCoefficient_uniform_coordinate_word_bounds
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p) x‖ ≤
          C * beta^(1+w.length) := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds
    hO hD g hg L K hK 2
  obtain ⟨J,hJ,hlog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 2
  let B2 : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2 -
    (2 : ℝ) • inverseDegreeMultiplier hO hD
  let B1 : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2 -
    inverseDegreeMultiplier hO hD
  let B : ℝ := 1+‖B2‖+‖B1‖
  let T : ℝ := 1+∑ a : Fin 3,
    (‖balancedDerivative hF hO hD a‖+‖balancedRaising hF hO hD a‖)
  let C : ℝ := 1+192*T*(M+4*J*B)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hB : 1 ≤ B := by dsimp only [B]; linarith [norm_nonneg B1,norm_nonneg B2]
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hB2 : ‖B2‖ ≤ B := by dsimp only [B]; linarith [norm_nonneg B1]
  have hB1 : ‖B1‖ ≤ B := by dsimp only [B]; linarith [norm_nonneg B2]
  have hT : 1 ≤ T := by
    have hs : 0 ≤ ∑ a : Fin 3,
        (‖balancedDerivative hF hO hD a‖+‖balancedRaising hF hO hD a‖) :=
      Finset.sum_nonneg (fun a _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
    dsimp only [T]
    linarith
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hShift (a : Fin 3) : ‖balancedDerivative hF hO hD a‖ ≤ T ∧
      ‖balancedRaising hF hO hD a‖ ≤ T := by
    have hs : ‖balancedDerivative hF hO hD a‖+‖balancedRaising hF hO hD a‖ ≤
        ∑ b : Fin 3, (‖balancedDerivative hF hO hD b‖+‖balancedRaising hF hO hD b‖) :=
      Finset.single_le_sum (fun b _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ a)
    dsimp only [T]
    constructor <;> linarith [norm_nonneg (balancedDerivative hF hO hD a),
      norm_nonneg (balancedRaising hF hO hD a)]
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  let A (a : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    ActualReferenceParallelRaising.normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)
  let f (a : Fin 3) : R3 → ℝ := referenceFrameDerivative g L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  let LF (a : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => -(A a y)+f a y • B2
  let RF (a : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => A a y+f a y • B1
  let DL (a : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    (balancedDerivative hF hO hD a).comp (LF a y)
  let RR (a : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    (balancedRaising hF hO hD a).comp (RF a y)
  let S : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, (DL a y - RR a y)
  have hAS (a : Fin 3) : ContDiff ℝ ∞ (A a) :=
    contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hfS (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hLF (a : Fin 3) : ContDiff ℝ ∞ (LF a) := (hAS a).neg.add ((hfS a).smul contDiff_const)
  have hRF (a : Fin 3) : ContDiff ℝ ∞ (RF a) := (hAS a).add ((hfS a).smul contDiff_const)
  have hDL (a : Fin 3) : ContDiff ℝ ∞ (DL a) := contDiff_const.clm_comp (hLF a)
  have hRR (a : Fin 3) : ContDiff ℝ ∞ (RR a) := contDiff_const.clm_comp (hRF a)
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun a _ => (hDL a).sub (hRR a))
  have hAJ0 (a : Fin 3) : HasCoordinateWordJetBound 2 (A a) x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx v hv).2.2.2.2.2.1 a
    calc
      _ ≤ M := ht
      _ ≤ M*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0
  have hAJ (a : Fin 3) : HasCoordinateWordJetBound 2 (A a) x M beta 1 :=
    hasCoordinateWordJetBound_raise_degree 2 (A a) x M beta 0 1 hM0 hb (by norm_num) (hAJ0 a)
  have hfJ (a : Fin 3) : HasCoordinateWordJetBound 2 (f a) x J beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs,f,beta,actualReferenceBeta] using
      (hlog lam hlam δ hδ hδ1 R hR p hp x hx hb v hv).1 a
  have hConst (B0 : SphereL2 →L[ℝ] SphereL2) (hB0norm : ‖B0‖ ≤ B) :
      HasCoordinateWordJetBound 2 (fun _ : R3 => B0) x B beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 B0 x B beta hB0norm hb0
  have hProfile (a : Fin 3) (B0 : SphereL2 →L[ℝ] SphereL2) (hB0norm : ‖B0‖ ≤ B) :
      HasCoordinateWordJetBound 2 (fun y => f a y • B0) x (4*J*B) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul 2 (f a) (fun _ : R3 => B0)
      (hfS a) contDiff_const x J B beta 1 0 hJ.le hB0 hb0 (hfJ a) (hConst B0 hB0norm)
    convert ht using 1 <;> norm_num
  have hLFJ (a : Fin 3) : HasCoordinateWordJetBound 2 (LF a) x (M+4*J*B) beta 1 :=
    hasCoordinateWordJetBound_add 2 (fun y => -(A a y)) (fun y => f a y • B2)
      (hAS a).neg ((hfS a).smul contDiff_const) x M (4*J*B) beta 1
      (hasCoordinateWordJetBound_neg 2 (A a) (hAS a) x M beta 1 (hAJ a)) (hProfile a B2 hB2)
  have hRFJ (a : Fin 3) : HasCoordinateWordJetBound 2 (RF a) x (M+4*J*B) beta 1 :=
    hasCoordinateWordJetBound_add 2 (A a) (fun y => f a y • B1)
      (hAS a) ((hfS a).smul contDiff_const) x M (4*J*B) beta 1 (hAJ a) (hProfile a B1 hB1)
  have hComp (Q : SphereL2 →L[ℝ] SphereL2) (hQ : ‖Q‖ ≤ T)
      (F0 : R3 → SphereL2 →L[ℝ] SphereL2) (hF0 : ContDiff ℝ ∞ F0)
      (hFJ : HasCoordinateWordJetBound 2 F0 x (M+4*J*B) beta 1) :
      HasCoordinateWordJetBound 2 (fun y => Q.comp (F0 y)) x (4*T*(M+4*J*B)) beta 1 := by
    have hQJ := hasCoordinateWordJetBound_const_normed 2 Q x T beta hQ hb0
    have ht := hasCoordinateWordJetBound_clm_comp 2 (fun _ : R3 => Q) F0
      contDiff_const hF0 x T (M+4*J*B) beta 0 1 hT0 (by positivity) hb0 hQJ hFJ
    convert ht using 1 <;> norm_num
  have hTermJ (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => DL a y-RR a y) x
      (8*T*(M+4*J*B)) beta 1 := by
    have ht := hasCoordinateWordJetBound_sub 2 (DL a) (RR a) (hDL a) (hRR a) x
      (4*T*(M+4*J*B)) (4*T*(M+4*J*B)) beta 1
      (hComp _ (hShift a).1 _ (hLF a) (hLFJ a)) (hComp _ (hShift a).2 _ (hRF a) (hRFJ a))
    convert ht using 1 <;> ring
  have hSJ : HasCoordinateWordJetBound 2 S x (24*T*(M+4*J*B)) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun a y => DL a y-RR a y)
      (fun a => (hDL a).sub (hRR a)) x (8*T*(M+4*J*B)) beta 1 hTermJ
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hTwo := hasCoordinateWordJetBound_const_normed 2 (2 : ℝ) x 2 beta (by norm_num) hb0
  have hFullJ : HasCoordinateWordJetBound 2 (fun y => (2 : ℝ) • S y) x
      (192*T*(M+4*J*B)) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul 2 (fun _ : R3 => (2 : ℝ)) S
      contDiff_const hS x 2 (24*T*(M+4*J*B)) beta 0 1 (by norm_num) (by positivity) hb0 hTwo hSJ
    convert ht using 1 <;> norm_num <;> ring
  have hExact : (fun y => (2 : ℝ) • S y) =
      nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p := rfl
  rw [hExact] at hFullJ
  have hEnlarge : 192*T*(M+4*J*B) ≤ C := by dsimp only [C]; linarith
  exact (hFullJ w hw).trans
    (mul_le_mul_of_nonneg_right hEnlarge (pow_nonneg hb0 (1+w.length)))

theorem exists_referenceZeroDefect_uniform_threehalf_half_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ 2 →
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪coordinateFieldWordPartial w
        (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x), G x⟫_ℝ| ≤
          (C * beta^(1+w.length)) *
            ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
            ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeReferenceZeroDefectBalancedAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw F G
  rw [coordinateFieldWordPartial_referenceZeroDefect_inner_threehalf_half hO hD hF g hg
    L lam δ R p hδ hR w F G x]
  have hA := hBounds lam hlam δ hδ hδ1 R hR p hp x hx hb w hw
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (((coordinateFieldWordPartial w
        (nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p) x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
