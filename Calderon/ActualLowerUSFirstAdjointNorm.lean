import Calderon.ActualLowerUSAdjointCoefficients
import Calderon.ActualFiniteHarmonicModelBAngularAdjointHalfNorm

/-!
Exact native D=-B-sphere-adjoint and genuine finite H^(3/2)->H^(1/2) test bounds.
These are explicit weighted finite-core norms, not an endpoint upgrade.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelErrorAssembly
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceDDSpectralTransport ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ActualPhysicalMixedFirst
  ReferenceDensityBounds NormalizedPrincipalMetric ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift PrincipalCommutator ConformalDepth ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

/-- The original full native B sphere adjoint includes its scalar row. -/
theorem nativeULowerAdjointFirstCoefficient_eq_neg_BAngularAdjoint (i : Fin 3) :
    nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i =
      -nativeBAngularAdjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr := by
  unfold nativeULowerAdjointFirstCoefficient nativeBAngularAdjoint
  abel

/-- Genuine pointwise sphere adjunction of D_i, with minus B_i on the test. -/
theorem nativeULowerAdjointFirstCoefficient_inner
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr i F).val x,G.val x⟫_ℝ =
      ⟪F.val x,-(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr G).val x⟫_ℝ := by
  rw [nativeULowerAdjointFirstCoefficient_eq_neg_BAngularAdjoint]
  simp only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,inner_neg_left,inner_neg_right]
  congr 1
  calc
    _ = ⟪G.val x,(nativeBAngularAdjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F).val x⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪(nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr G).val x,F.val x⟫_ℝ :=
      (nativeB_pointwise_inner_adjoint hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr G F x).symm
    _ = _ := real_inner_comm _ _

/-- The actual forward B high weighted norm, retaining the preserving scalar
and connection fields and all raising terms. -/
lemma norm_coreWeight_half_nativeB_le (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L q dr Ar p
      (referenceNormalizedPrincipalDifference g g2 L q) i x
    let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g g2 L q dr Ar p i x
    let m (a : Fin 3) := physicalMixedFirstCoefficient g L q
      (referenceNormalizedPrincipalDifference g g2 L q) a i x
    ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F)).val x‖ ≤
      (‖K‖+‖J‖+(2*(2 : ℝ)^(1/2 : ℝ))*(∑ a : Fin 3, |m a|))*
        ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖ := by
  intro K J m
  let M := K+J
  have hK : PreservesSphereSpectralGraphs hO hD K :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L q dr Ar p _ i x
  have hJ : PreservesSphereSpectralGraphs hO hD J := by
    unfold J normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_add hO hD _ _ hK hJ
  have hA : (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F).val x =
      M ((coreWeightOperator hO hD (besselWeight 1) F).val x)+
        ∑ a : Fin 3, m a • (coreRaising hO hD hF a F).val x := by
    rw [nativeB_preserving_raising_action]
    dsimp only [M,K,J,m]
    rw [ContinuousLinearMap.add_apply]
    abel
  have ht := norm_coreWeight_half_le_preserving_add_sum hO hD M hM
    (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F) F
    (fun a : Fin 3 => coreRaising hO hD hF a F) m
    (fun _ => 2*(2 : ℝ)^(1/2 : ℝ)) x hA
    (fun a => norm_coreWeight_half_raising_le hO hD hF a F x)
  have hMn : ‖M‖ ≤ ‖K‖+‖J‖ := norm_add_le _ _
  have hs : (∑ a : Fin 3, |m a| * (2*(2 : ℝ)^(1/2 : ℝ))) =
      (2*(2 : ℝ)^(1/2 : ℝ))*(∑ a : Fin 3, |m a|) := by
    rw [← Finset.sum_mul,mul_comm]
  rw [hs] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right (add_le_add hMn le_rfl) (norm_nonneg _))

/-- The original hypotheses produce one full finite high-to-Half test budget
for both D and its genuine sphere adjoint -B, before every profile and input. -/
theorem exists_nativeULowerAdjointFirst_uniform_half_norm_bounds
    (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
          L q dr Ar p hdr hAr i F)).val x‖ ≤
        (C_D*eta/actualReferenceBeta g L q dr Ar p x)*
          ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖ ∧
      ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F)).val x‖ ≤
        (C_D*eta/actualReferenceBeta g L q dr Ar p x)*
          ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖ := by
  let K : Set R3 := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨CD,hCD,hDcap⟩ := exists_nativeBAngularAdjoint_uniform_half_norm_bound
    hO hD hF g g2 hg hg2 L hL K hK
  obtain ⟨CB,hCB,hBcap⟩ := exists_nativeB_derivative_form_coefficient_uniform_smallness
    hO hD g g2 hg hg2 L hL K hK
  let cr : ℝ := 2*(2 : ℝ)^(1/2 : ℝ)
  have hcr : 0 ≤ cr := by dsimp only [cr]; positivity
  let C_D : ℝ := 1+CD+(1+cr)*CB
  have hC : 0 < C_D := by dsimp only [C_D]; positivity
  refine ⟨C_D,hC,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i F
  let beta := actualReferenceBeta g L q dr Ar p x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hNorm : 0 ≤ ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖ := norm_nonneg _
  have hDNorm := hDcap q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i F
  have hB := hBcap q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i
  let KK := referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L q dr Ar p
    (referenceNormalizedPrincipalDifference g g2 L q) i x
  let JJ := normalizedSecondDriftFirstNormalizedCoefficient hO hD g g2 L q dr Ar p i x
  let S : ℝ := ∑ a : Fin 3, |physicalMixedFirstCoefficient g L q
    (referenceNormalizedPrincipalDifference g g2 L q) a i x|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hKn : 0 ≤ ‖KK‖ := norm_nonneg _
  have hJn : 0 ≤ ‖JJ‖ := norm_nonneg _
  change 4*(‖KK‖+‖JJ‖)+8*S ≤ CB*eta/beta at hB
  have hKJ : ‖KK‖+‖JJ‖ ≤ CB*eta/beta := by linarith
  have hSbound : S ≤ CB*eta/beta := by linarith
  have hTotal : ‖KK‖+‖JJ‖+cr*S ≤ (1+cr)*(CB*eta/beta) := by
    have hh := add_le_add hKJ (mul_le_mul_of_nonneg_left hSbound hcr)
    nlinarith only [hh]
  have hDC : CD ≤ C_D := by dsimp only [C_D]; nlinarith [mul_nonneg (by linarith : 0 ≤ 1+cr) hCB.le]
  have hBC : (1+cr)*CB ≤ C_D := by dsimp only [C_D]; linarith
  constructor
  · rw [nativeULowerAdjointFirstCoefficient_eq_neg_BAngularAdjoint]
    simp only [LinearMap.neg_apply,map_neg,Submodule.coe_neg,Pi.neg_apply,norm_neg]
    exact hDNorm.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDC heta) hb0) hNorm)
  · have hRaw := norm_coreWeight_half_nativeB_le hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i F x
    change _ ≤ (‖KK‖+‖JJ‖+cr*S)*_ at hRaw
    calc
      _ ≤ (‖KK‖+‖JJ‖+cr*S)*_ := hRaw
      _ ≤ ((1+cr)*(CB*eta/beta))*_ := mul_le_mul_of_nonneg_right hTotal hNorm
      _ = (((1+cr)*CB)*eta/beta)*_ := by ring
      _ ≤ (C_D*eta/beta)*_ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC heta) hb0) hNorm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
