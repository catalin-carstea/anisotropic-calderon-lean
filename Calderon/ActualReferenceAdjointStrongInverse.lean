import Calderon.ActualReferenceAdjointStrongEnergy
import Calderon.NativeSupportedAdjointStrongInvertibility
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.CompactInverseDerivativeBounds

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

lemma referenceWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeSupportedOriginalZeroEnergyL
        (coefficientMatrixField 2 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth
          (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) 0
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let F := referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p
  have he := nativeZeroCoefficientEnergyL_eval_to_H1 (coefficientMatrixField 2 F) beta
    (coefficientValue 1 (0 : SmoothCoefficientJets 1))
    (nativeSupportedOriginalEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta) u v
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  simp only [coefficientMatrixField_referenceJointPrincipalJetsFamily,hzero] at he
  exact (referenceWeakDirichletEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v).trans he.symm

def referenceAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp nativeStrongH2InclusionL

lemma referenceAdjointStrongDirichletFamily_eq_native
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeSupportedAdjointStrongDirichletL hcalc
        (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) 0
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p) :=
  congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 0 => T.comp nativeStrongH2InclusionL)
    (referenceAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL g L y0 Φ B ε C ρ H a w hData hcalc p)

lemma contDiff_referenceAdjointStrongDirichletFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc) :=
  (contDiff_referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc).clm_comp contDiff_const

lemma referenceAdjointStrongDirichletFamily_isInvertible
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible := by
  have hA := hOriginal
  rw [referenceWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
    g L y0 Φ B ε C ρ H a w hData hcalc p] at hA
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic g L y0 Φ B ε C ρ H a w hData p
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) lam Lam := by
    rw [coefficientMatrixField_referenceJointPrincipalJetsFamily]
    exact hUE
  have hi := nativeSupportedAdjointStrongDirichletL_isInvertible τ0 hcalc hreg
    (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) lam Lam hUEF 0
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p) hA
  exact (referenceAdjointStrongDirichletFamily_eq_native g L y0 Φ B ε C ρ H a w hData hcalc p).symm ▸ hi

lemma contDiffOn_referenceAdjointStrongInverse_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (fun p =>
      (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).inverse)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  apply contDiffOn_banachInverseFamily _ _
    (contDiff_referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc).contDiffOn
  intro p hp
  exact referenceAdjointStrongDirichletFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg p hp.2.1

theorem exists_reference_commonRadius_adjointStrongInverse_bounds
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) ∧
      (∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        ‖(referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).inverse‖ ≤ D) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
          ‖iteratedFDeriv ℝ j (fun t =>
            (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc t).inverse) p‖ ≤ D := by
  obtain ⟨δ,hδ,hδρ,hSub⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  let A := referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc
  let S : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  have hS : IsCompact S := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hA : ContDiff ℝ ∞ A := contDiff_referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc
  have hi : ∀ p ∈ S, (A p).IsInvertible := fun p hp =>
    referenceAdjointStrongDirichletFamily_isInvertible g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p (hSub hp).2.1
  exact ⟨δ,hδ,hδρ,hi,uniform_norm_banachInverseFamily A S hS hA.continuous.continuousOn hi,
    fun N => exists_compact_banachInverse_derivative_bound A hA S hS hi N⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointStrongDirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointStrongDirichletFamily_eq_native

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointStrongDirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointStrongDirichletFamily_isInvertible

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointStrongInverse_invertibleLocus

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointStrongInverse_bounds
