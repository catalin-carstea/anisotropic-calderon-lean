import Calderon.ActualFiniteHarmonicModelWeightedYAngularPart
import Calderon.ActualDensitySigmaMixedCoefficient
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualReferenceDDHigherCLMProducts
import Calderon.ActualReferenceDDHigherProfileJets

/-!
The scalar part of the original weighted adjoint derivative. All caps below are
derived from actual compact background families and the original radius jets;
no cap callback is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  DirichletFamily.DriftBootstrap ActualPhysicalMixedReferenceCancellation
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherProfileJets
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth SmoothMetricFrame
  MovingFrameConnection ReferenceDensityBounds PrincipalCommutator ConformalDepth
  ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- The actual profile-independent scalar connection contraction in sigma. -/
def weightedFirstScalarBackground (g g2 : MatrixField) (L : ℝ)
    (j : Fin 3) (z : ℝ × R3) : ℝ :=
  -(∑ a : Fin 3, ∑ b : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 a b *
      (referenceConnectionFamily g L z (referenceMetricGramFrame g L z a)
        (referenceMetricGramFrame g L z b)) j)

lemma contDiff_weightedFirstScalarBackground (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (j : Fin 3) :
    ContDiff ℝ ∞ (weightedFirstScalarBackground g g2 L j) := by
  have hc (a b : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      (referenceConnectionFamily g L z (referenceMetricGramFrame g L z a)
        (referenceMetricGramFrame g L z b)) j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (((contDiff_referenceConnectionFamily g hg L).clm_apply
        (contDiff_referenceMetricGramFrame g hg L a)).clm_apply
          (contDiff_referenceMetricGramFrame g hg L b))
  unfold weightedFirstScalarBackground
  exact (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L a b).mul
      (hc a b)))).neg

/-- Literal sigma equals radius times an actual compact smooth background. -/
lemma nativeReferenceWeightedFirstScalarCoefficient_eq_radius_background
    (g g2 : MatrixField) (L q dr Ar : ℝ) (p : ℕ) (j : Fin 3) :
    nativeReferenceWeightedFirstScalarCoefficient g L q dr Ar p
      (referenceNormalizedPrincipalDifference g g2 L q) j =
    fun x => referenceRadius dr Ar p L x * weightedFirstScalarBackground g g2 L j (q,x) := by
  funext x
  unfold nativeReferenceWeightedFirstScalarCoefficient weightedFirstScalarBackground
  simp_rw [referenceDensityPrincipalFrameCoefficient_eq_physicalMixedQFrameCoefficient]
  ring

/-- Exact scalar coefficient of the full weighted derivative, with its minus
sign, inverse density and differentiated density products intact. -/
def nativeWeightedYScalarCoefficient (g g2 : MatrixField)
    (L q dr Ar : ℝ) (p : ℕ) (x : R3) : ℝ :=
  -(referenceDensityFamily g L (q,x))⁻¹ *
    ∑ j : Fin 3, directionalFDeriv (coordinateDirection j)
      (fun y => referenceDensityFamily g L (q,y) *
        nativeReferenceWeightedFirstScalarCoefficient g L q dr Ar p
          (referenceNormalizedPrincipalDifference g g2 L q) j y) x

lemma contDiff_nativeWeightedYScalarCoefficient (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) :
    ContDiff ℝ ∞ (nativeWeightedYScalarCoefficient g g2 L q dr Ar p) := by
  have hm : ContDiff ℝ ∞ (fun y => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hi : ContDiff ℝ ∞ (fun y => (referenceDensityFamily g L (q,y))⁻¹) :=
    (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hs (j : Fin 3) : ContDiff ℝ ∞
      (nativeReferenceWeightedFirstScalarCoefficient g L q dr Ar p
        (referenceNormalizedPrincipalDifference g g2 L q) j) :=
    contDiff_nativeReferenceWeightedFirstScalarCoefficient g hg L q dr Ar p _
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g g2 hg hg2 L q)
      hdr hAr j
  unfold nativeWeightedYScalarCoefficient
  exact hi.neg.mul (ContDiff.sum (fun j _ =>
    contDiff_directionalFDeriv (coordinateDirection j) _ (hm.mul (hs j))))

/-- The scalar coefficient represents the existing full Y scalar part, not the
angular degree/rotation mass or an independently selected residual. -/
lemma nativeWeightedYScalarPart_eq_coefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) :
    nativeWeightedYScalarPart hO hD g hg L q dr Ar p
      (referenceNormalizedPrincipalDifference g g2 L q)
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g g2 hg hg2 L q)
      hdr hAr =
    coreScalar hO hD (nativeWeightedYScalarCoefficient g g2 L q dr Ar p)
      (contDiff_nativeWeightedYScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [nativeWeightedYScalarPart, nativeWeightedYScalarCoefficient,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    coreScalar, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply]
  simp only [← Finset.sum_smul, smul_smul]
  congr 1 <;> ring

/-- Original fixed-metric scalar-density derivative jets. The constant is fixed
before dilation and every radius/profile choice. The H8 hypothesis is unnecessary
for this actual smooth background scalar component. -/
theorem exists_nativeWeightedYScalarCoefficient_uniform_coordinate_word_smallness
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ C_Y : ℝ, 0 < C_Y ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ w : List (Fin 3), w.length ≤ 1 →
        |coordinateFieldWordPartial w (nativeWeightedYScalarCoefficient g g2 L q dr Ar p) x| ≤
          (C_Y * eta) * (actualReferenceBeta g L q dr Ar p x)^w.length := by
  let K : Set R3 := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  let bg : Fin 3 ⊕ Bool → ℝ × R3 → ℝ := fun i =>
    match i with
    | Sum.inl j => weightedFirstScalarBackground g g2 L j
    | Sum.inr false => referenceDensityFamily g L
    | Sum.inr true => fun z => (referenceDensityFamily g L z)⁻¹
  have hbgSmooth (i : Fin 3 ⊕ Bool) : ContDiff ℝ ∞ (bg i) := by
    cases i with
    | inl j => exact contDiff_weightedFirstScalarBackground g g2 hg hg2 L j
    | inr b => cases b <;> first
      | exact contDiff_referenceDensityFamily g hg L
      | exact contDiff_referenceDensityFamily_inv g hg L
  obtain ⟨M,hM,hbg⟩ := exists_parameter_coordinate_word_uniform_bound bg hbgSmooth K hK 2
  obtain ⟨Cr,hCr,hrJet⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g hg L hL K hK 2
  let B : ℝ := 16*M^2*Cr
  let C_Y : ℝ := 6*M*B
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hB : 0 < B := by dsimp [B]; positivity
  have hCY : 0 < C_Y := by dsimp [C_Y]; positivity
  refine ⟨C_Y,hCY,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs w hw
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let r : ℝ := referenceRadius dr Ar p L x
  let rr : R3 → ℝ := referenceRadius dr Ar p L
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (q,y)
  let mi : R3 → ℝ := fun y => (mu y)⁻¹
  let c : Fin 3 → R3 → ℝ := fun j y => weightedFirstScalarBackground g g2 L j (q,y)
  let sig : Fin 3 → R3 → ℝ := fun j =>
    nativeReferenceWeightedFirstScalarCoefficient g L q dr Ar p
      (referenceNormalizedPrincipalDifference g g2 L q) j
  let v : Fin 3 → R3 → ℝ := fun j => directionalFDeriv (coordinateDirection j)
    (fun y => mu y * sig j y)
  change 1 ≤ beta at hb
  change r*beta^2 ≤ eta at hs
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hrS : ContDiff ℝ ∞ rr := contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hmS : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmiS : ContDiff ℝ ∞ mi :=
    (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hcS (j : Fin 3) : ContDiff ℝ ∞ (c j) :=
    (contDiff_weightedFirstScalarBackground g g2 hg hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  have hsEq (j : Fin 3) : sig j = fun y => rr y * c j y :=
    nativeReferenceWeightedFirstScalarCoefficient_eq_radius_background g g2 L q dr Ar p j
  have hsS (j : Fin 3) : ContDiff ℝ ∞ (sig j) := by rw [hsEq]; exact hrS.mul (hcS j)
  have hvS (j : Fin 3) : ContDiff ℝ ∞ (v j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hmS.mul (hsS j))
  have hBg (i : Fin 3 ⊕ Bool) : HasCoordinateWordJetBound 2
      (fun y => bg i (q,y)) x M beta 0 := by
    intro a ha
    exact (hbg q hq x hx i a ha).trans
      (by simpa only [Nat.zero_add] using
        le_mul_of_one_le_right hM0 (one_le_pow₀ hb (n := a.length)))
  have hmJ : HasCoordinateWordJetBound 2 mu x M beta 0 := hBg (Sum.inr false)
  have hiJ : HasCoordinateWordJetBound 1 mi x M beta 0 :=
    fun a ha => hBg (Sum.inr true) a (by omega)
  have hcJ (j : Fin 3) : HasCoordinateWordJetBound 2 (c j) x M beta 0 := hBg (Sum.inl j)
  have hrJ : HasCoordinateWordJetBound 2 rr x (Cr*r) beta 0 := by
    intro a ha
    simpa only [Real.norm_eq_abs,Nat.zero_add,mul_assoc,rr,r,beta,actualReferenceBeta] using
      (hrJet q hq dr hdr hdr1 Ar hAr p hp x hx a ha).1
  have hProd (j : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => mu y * sig j y) x (B*r) beta 0 := by
    have hOne := hasCoordinateWordJetBound_mul 2 mu rr hmS hrS x M (Cr*r) beta 0 0
      hM0 (mul_nonneg hCr.le hr.le) hb0 hmJ hrJ
    have hTwo := hasCoordinateWordJetBound_mul 2 (fun y => mu y*rr y) (c j)
      (hmS.mul hrS) (hcS j) x ((2:ℝ)^2*M*(Cr*r)) M beta 0 0
      (by positivity) hM0 hb0 hOne (hcJ j)
    have he : (fun y => mu y * sig j y) = (fun y => (mu y * rr y) * c j y) := by
      rw [hsEq]
      funext y
      ring
    rw [he]
    convert hTwo using 1 <;> dsimp only [B] <;> ring
  have hvJ (j : Fin 3) : HasCoordinateWordJetBound 1 (v j) x (B*r) beta 1 := by
    intro a ha
    have ht := hProd j (a++[j]) (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [coordinateFieldWordPartial_append, coordinateFieldWordPartial,
      List.length_append,List.length_singleton,Nat.zero_add,Nat.add_comm,v] using ht
  have hsum := hasCoordinateWordJetBound_sum 1 v hvS x (B*r) beta 1 hvJ
  have hsum' : HasCoordinateWordJetBound 1 (fun y => ∑ j : Fin 3, v j y)
      x (3*B*r) beta 1 := by
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_assoc] using hsum
  have hmProd := hasCoordinateWordJetBound_mul 1 mi (fun y => ∑ j : Fin 3, v j y)
    hmiS (ContDiff.sum (fun j _ => hvS j)) x M (3*B*r) beta 0 1
    hM0 (by positivity) hb0 hiJ hsum'
  have hn := hasCoordinateWordJetBound_neg 1 (fun y => mi y*(∑ j : Fin 3, v j y))
    (hmiS.mul (ContDiff.sum (fun j _ => hvS j))) x ((2:ℝ)^1*M*(3*B*r)) beta 1 hmProd
  have ht := hn w hw
  have hExpr : nativeWeightedYScalarCoefficient g g2 L q dr Ar p =
      fun y => -(mi y * (∑ j : Fin 3, v j y)) := by
    funext y
    dsimp only [nativeWeightedYScalarCoefficient,mi,mu,v,sig]
    ring
  have ht' : |coordinateFieldWordPartial w
      (nativeWeightedYScalarCoefficient g g2 L q dr Ar p) x| ≤
      (C_Y*r)*beta^(1+w.length) := by
    rw [hExpr]
    convert ht using 1 <;> simp only [Real.norm_eq_abs,C_Y] <;> ring
  have hrb : r*beta ≤ eta :=
    (mul_le_mul_of_nonneg_left (by nlinarith : beta ≤ beta^2) hr.le).trans hs
  calc
    _ ≤ (C_Y*r)*beta^(1+w.length) := ht'
    _ = C_Y*(r*beta)*beta^w.length := by rw [pow_add,pow_one]; ring
    _ ≤ C_Y*eta*beta^w.length :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrb hCY.le)
        (pow_nonneg hb0 _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
