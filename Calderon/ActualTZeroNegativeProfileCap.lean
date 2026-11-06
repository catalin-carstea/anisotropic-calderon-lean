import Calderon.ActualTZeroNegativeGraph
import Calderon.ActualSecondGeometryCaps
import Calderon.ProfileRadiusJets
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeProfileCap

private lemma norm_zero_action_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : Fin 3 → F →L[ℝ] G) (B : Fin 3 → E →L[ℝ] F) (D : E →L[ℝ] F)
    (a : Fin 3 → ℝ) (M J beta : ℝ) (hM : 0 ≤ M) (hJ : 0 ≤ J) (hb : 1 ≤ beta)
    (hB : ∀ i, ‖B i‖ ≤ M) (ha : ∀ i, |a i| ≤ M*J*beta) (u : E) :
    ‖∑ i : Fin 3, A i (B i u+a i • D u)‖ ≤
      (∑ i : Fin 3, ‖A i‖)*M*(1+J*‖D‖)*beta*‖u‖ := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hrow (i : Fin 3) :
      ‖B i u+a i • D u‖ ≤ M*(1+J*‖D‖)*beta*‖u‖ := by
    have hBu : ‖B i u‖ ≤ M*‖u‖ :=
      ((B i).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hB i) (norm_nonneg u))
    have hDu : ‖a i • D u‖ ≤ (M*J*beta)*(‖D‖*‖u‖) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (ha i) (D.le_opNorm u) (norm_nonneg _) (by positivity)
    calc
      _ ≤ M*‖u‖+(M*J*beta)*(‖D‖*‖u‖) := (norm_add_le _ _).trans (add_le_add hBu hDu)
      _ ≤ (M*beta)*‖u‖+(M*J*beta)*(‖D‖*‖u‖) := add_le_add
        (mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hM) (norm_nonneg u)) le_rfl
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin 3, ‖A i (B i u+a i • D u)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖A i‖*(M*(1+J*‖D‖)*beta*‖u‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hrow i) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

open SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualTZeroNegativeGraph
  ActualSecondGeometryCaps ActualHigherSFormation ReferenceDensityBounds
  AmbientReferenceRaising ConformalDepth ReferenceWeightedApproximation SmoothMetricFrame

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "DL" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
attribute [local irreducible] raisingLow loweringLow sphereSobolevInclusionL
  sphereSobolevShiftedDegreeL referenceHighHorizontalAngularL

/-- Positive reference constant before every profile/input, for the genuine negative outputs.
No second metric enters these original reference operators. -/
theorem exists_reference_zero_negative_uniform_beta_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ CT : ℝ, 0 < CT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, 0 < dr → dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x →
      ∀ u : Hi,
        ‖referenceZeroNegative hO hD hF g L q dr Ar p x u‖ ≤
          CT*actualReferenceBeta g L q dr Ar p x*‖u‖ ∧
        ‖referenceAdjointZeroNegative hO hD hF g L q dr Ar p x u‖ ≤
          CT*actualReferenceBeta g L q dr Ar p x*‖u‖ := by
  obtain ⟨M,hM,hGeom⟩ := exists_geometryCaps g g hg hg L K hK
  obtain ⟨J,hJ,hJet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK 1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  let A : ℝ := (∑ i : Fin 3, ‖raisingLow hF hO hD i‖)*M*(1+J*‖DL‖)
  let B : ℝ := (∑ i : Fin 3, ‖loweringLow hF hO hD i‖)*M*(1+J*‖DL-IH‖)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ =>
      ContinuousLinearMap.opNorm_nonneg (raisingLow hF hO hD i))) hM0)
      (add_nonneg zero_le_one (mul_nonneg hJ0 (ContinuousLinearMap.opNorm_nonneg DL)))
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ =>
      ContinuousLinearMap.opNorm_nonneg (loweringLow hF hO hD i))) hM0)
      (add_nonneg zero_le_one (mul_nonneg hJ0 (ContinuousLinearMap.opNorm_nonneg (DL-IH))))
  let CT : ℝ := 1+A+B
  have hCT : 0 < CT := by dsimp only [CT]; linarith only [hA0,hB0]
  have hAC : A ≤ CT := by dsimp only [CT]; linarith only [hB0]
  have hBC : B ≤ CT := by dsimp only [CT]; linarith only [hA0]
  refine ⟨CT,hCT,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hb u
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let ell : R3 →L[ℝ] ℝ := fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x
  let f : Fin 3 → ℝ := fun i => referenceFrameDerivative g L q i
    (fun y => Real.log (referenceRadius dr Ar p L y)) x
  let Gamma : Fin 3 → Hi →L[ℝ] Half := referenceHighHorizontalAngularL g L q x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hEll : ‖ell‖ ≤ J*beta := by
    simpa only [ell,beta,norm_iteratedFDeriv_one,pow_one,actualReferenceBeta]
      using hJet q hq dr hdr hdr1 Ar hAr p hp x hx 1 (by norm_num) (by norm_num)
  have hGamma (i : Fin 3) : ‖Gamma i‖ ≤ M := (hGeom q hq x hx).high_connection i
  have hf (i : Fin 3) : |f i| ≤ M*J*beta := by
    rw [← Real.norm_eq_abs]
    change ‖ell (referenceMetricGramFrame g L (q,x) i)‖ ≤ M*J*beta
    calc
      _ ≤ ‖ell‖*‖referenceMetricGramFrame g L (q,x) i‖ := ell.le_opNorm _
      _ ≤ (J*beta)*M := mul_le_mul hEll ((hGeom q hq x hx).frame i)
        (norm_nonneg _) (mul_nonneg hJ0 hb0)
      _ = _ := by ring
  have hPlus := norm_zero_action_le (raisingLow hF hO hD) Gamma DL f M J beta
    hM0 hJ0 hb hGamma hf u
  have hMinus := norm_zero_action_le (loweringLow hF hO hD) (fun i => -Gamma i) (DL-IH) f M J beta
    hM0 hJ0 hb (fun i => by simpa only [norm_neg] using hGamma i) hf u
  have hp : ‖referenceZeroNegative hO hD hF g L q dr Ar p x u‖ ≤ A*beta*‖u‖ := by
    simpa only [referenceZeroNegative,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,_root_.smul_apply,A,Gamma,f] using hPlus
  have hm : ‖referenceAdjointZeroNegative hO hD hF g L q dr Ar p x u‖ ≤ B*beta*‖u‖ := by
    simpa only [referenceAdjointZeroNegative,_root_.sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,_root_.neg_apply,_root_.smul_apply,B,Gamma,f] using hMinus
  exact ⟨hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAC hb0) (norm_nonneg u)),
    hm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC hb0) (norm_nonneg u))⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeProfileCap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroNegativeProfileCap.exists_reference_zero_negative_uniform_beta_bound
