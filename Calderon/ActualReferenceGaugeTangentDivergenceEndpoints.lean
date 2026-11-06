import Calderon.ActualReferenceGaugeTangentTranspose
import Calderon.NativeCoefficientRotationFieldSkew
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/
EXPANSION-divergence-endpoints-v005.md. Same genuine scalar jets at three finite orders. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)

lemma referenceGaugeTangentSecondDivergence_high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily,
    referenceGaugeTangentSecondDivergenceHalfMultiplierFamily,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p) (by
        funext z
        rw [coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily,
          coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily]))

lemma referenceGaugeTangentSecondDivergence_half_negative_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentSecondDivergenceHalfMultiplierFamily,
    referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
    (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p))

lemma contDiff_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationDerivativeCoefficient_support g L y0 Φ B ε C ρ H a w hData hg i j)

lemma exists_compact_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily_parameter_jets
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) Q hQ N

lemma exists_compact_referenceGaugeTangentSecondDivergenceHalfMultiplierFamily_parameter_jets
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) Q hQ N

lemma referenceGaugeTangentSecondDivergenceNegativeMultiplier_comm_nativeMultiplier
    (p : ℝ × (R3 × ℝ)) (G : SmoothCoefficientJets 2) (u : SphereSobolev (-(1/2 : ℝ))) :
    referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
        (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G
      (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) := by
  simp only [referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily,
    ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact nativeNegativeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0 _ G u

lemma referenceGaugeTangentSecond_rightMultiplier_defect_eq_skew_add_commutator
    (p : ℝ × (R3 × ℝ)) (G : SmoothCoefficientJets 2) :
    ((referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) -
      sphereLowerDistributionalTranspose (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
    nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0
      (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) G +
    ((referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) -
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
        (referenceGaugeTangentSecondEndpointFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)) :=
  nativeLowerRightMultiplier_defect_eq_skew_add_commutator hcalc hF hO hD τ0 _ _ G
    ((referenceGaugeTangentSecond_distributionalTranspose_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).trans
      (referenceGaugeTangentSecondAdjoint_eq_neg_add_divergence
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p))
    (referenceGaugeTangentSecondDivergenceNegativeMultiplier_comm_nativeMultiplier
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p G)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergence_high_half_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergence_half_negative_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily_parameter_jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentSecondDivergenceHalfMultiplierFamily_parameter_jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergenceNegativeMultiplier_comm_nativeMultiplier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecond_rightMultiplier_defect_eq_skew_add_commutator
