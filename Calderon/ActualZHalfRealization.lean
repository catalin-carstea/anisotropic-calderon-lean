import Calderon.ActualFiniteCoreLoweringRealization
import Calderon.ActualTSShiftedAdjointDictionary
import Calderon.ProfileRadiusJets
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZHalfRealization
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFiniteCoreLoweringRealization
  ActualTSShiftedAdjointDictionary SmoothMetricFrame ReferenceDensityBounds
  AmbientReferenceRaising ConformalDepth RadiusProfile ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "aH" => loweringHigh hF hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- Original logarithmic-radius coefficients and the actual all-output lowering operators. -/
def referenceZHalf (g : MatrixField) (L q dr Ar : ℝ) (p : ℕ) (x : R3) : Hi →L[ℝ] Half :=
  ∑ i : Fin 3, referenceFrameDerivative g L q i
    (fun y => Real.log (referenceRadius dr Ar p L y)) x • aH i

/-- Exact physical decoding of the whole original native Z. -/
theorem referenceZHalf_finiteCore_decode (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (referenceZHalf hF hO hD g L q dr Ar p x
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
      (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x := by
  rw [nativeZ_eq_coreDefectAction hO hD hF g hg L q dr Ar p hdr hAr]
  simp only [referenceZHalf,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    map_sum,map_smul,loweringHigh_finiteCore_decode hO hD hF,
    coreDefectAction,LinearMap.sum_apply,Module.End.mul_apply,coreScalar,
    LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_sum,Pi.smul_apply,
    Finset.sum_apply]

private theorem norm_lowering_sum_le (V : Fin 3 → R3) (ell : R3 →L[ℝ] ℝ) (u : Hi) :
    ‖∑ i : Fin 3, ell (V i) • aH i u‖ ≤
      (∑ i : Fin 3, ‖V i‖*‖aH i‖)*‖ell‖*‖u‖ := by
  calc
    ‖∑ i : Fin 3, ell (V i) • aH i u‖ ≤ ∑ i : Fin 3, ‖ell (V i) • aH i u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, (‖V i‖*‖aH i‖)*‖ell‖*‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      calc
        ‖ell (V i)‖*‖aH i u‖ ≤ (‖ell‖*‖V i‖)*‖aH i u‖ :=
          mul_le_mul_of_nonneg_right (ell.le_opNorm (V i)) (norm_nonneg _)
        _ ≤ (‖ell‖*‖V i‖)*(‖aH i‖*‖u‖) :=
          mul_le_mul_of_nonneg_left ((aH i).le_opNorm u)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (‖V i‖*‖aH i‖)*‖ell‖*‖u‖ := by ring
    _ = (∑ i : Fin 3, ‖V i‖*‖aH i‖)*‖ell‖*‖u‖ := by
      rw [Finset.sum_mul,Finset.sum_mul]

/-- Positive constant before every profile and input, for the original beta and full output. -/
theorem exists_referenceZHalf_uniform_beta_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, 0 < dr → dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ u : Hi,
        ‖referenceZHalf hF hO hD g L q dr Ar p x u‖ ≤
          CZ*actualReferenceBeta g L q dr Ar p x*‖u‖ := by
  let B : ℝ × R3 → ℝ := fun z =>
    ∑ i : Fin 3, ‖referenceMetricGramFrame g L z i‖*‖aH i‖
  have hBcont : Continuous B := by
    apply continuous_finset_sum
    intro i _
    exact (contDiff_referenceMetricGramFrame g hg L i).continuous.norm.mul continuous_const
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hBcont.continuousOn
  let M : ℝ := max 1 C
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hBudget : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, B (q,x) ≤ M := by
    intro q hq x hx
    have ha : |B (q,x)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (q,x) ⟨hq,hx⟩
    exact ((le_abs_self _).trans ha).trans (le_max_right _ _)
  obtain ⟨J,hJ,hjet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope
    g hg L hL K hK 1
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  refine ⟨M*J,mul_pos hM hJpos,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx u
  let ell : R3 →L[ℝ] ℝ := fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  have hb : 0 ≤ beta := Real.sqrt_nonneg _
  have hEll : ‖ell‖ ≤ J*beta := by
    simpa only [ell,beta,norm_iteratedFDeriv_one,pow_one,actualReferenceBeta]
      using hjet q hq dr hdr hdr1 Ar hAr p hp x hx 1 (by norm_num) (by norm_num)
  have hBnonneg : 0 ≤ B (q,x) :=
    Finset.sum_nonneg (fun (i : Fin 3) _ =>
      mul_nonneg (norm_nonneg (referenceMetricGramFrame g L (q,x) i)) (norm_nonneg (aH i)))
  have hNorm : ‖referenceZHalf hF hO hD g L q dr Ar p x u‖ ≤
      B (q,x)*‖ell‖*‖u‖ := by
    exact norm_lowering_sum_le hF hO hD (referenceMetricGramFrame g L (q,x)) ell u
  calc
    ‖referenceZHalf hF hO hD g L q dr Ar p x u‖ ≤ B (q,x)*‖ell‖*‖u‖ := hNorm
    _ ≤ B (q,x)*(J*beta)*‖u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEll hBnonneg) (norm_nonneg _)
    _ ≤ M*(J*beta)*‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hBudget q hq x hx) (mul_nonneg hJpos.le hb)) (norm_nonneg _)
    _ = (M*J)*actualReferenceBeta g L q dr Ar p x*‖u‖ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZHalfRealization
