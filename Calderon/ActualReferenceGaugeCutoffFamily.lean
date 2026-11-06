import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.NativeHighBulkMultiplierCommutatorForcingTopology
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Gradient ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap


def nativeUnitBallCutoffJets (k : ℕ) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) : SmoothCoefficientJets k :=
  compactCoefficient k (fun z => unitBallSmoothCutoff z * η z)
    (unitBallSmoothCutoff.contDiff.mul hη) (unitBallSmoothCutoff.hasCompactSupport.mul_right)

theorem coefficientValue_nativeUnitBallCutoffJets
    (k : ℕ) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) :
    coefficientValue k (nativeUnitBallCutoffJets k η hη) = fun z => unitBallSmoothCutoff z * η z := by
  exact coefficientValue_compactCoefficient k _ _ _

theorem coefficientValue_nativeUnitBallCutoffJets_on_ball
    (k : ℕ) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) (z : R3) (hz : z ∈ ballOpens) :
    coefficientValue k (nativeUnitBallCutoffJets k η hη) z = η z := by
  rw [coefficientValue_nativeUnitBallCutoffJets]
  change unitBallSmoothCutoff z * η z = η z
  rw [unitBallSmoothCutoff_one_of_mem hz,one_mul]

theorem nativeUnitBallCutoff_forcing_ae
    (hcalc : FixedSobolevCalculus) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) (f : BallSobolev 0) :
    coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 (nativeUnitBallCutoffJets 3 η hη)) f
      =ᵐ[volume.restrict ballOpens] (fun z => η z * f z) := by
  have hMult := coefficientMultiplier_value_ae hcalc 0
    (coefficientRepackedJets 3 1 (nativeUnitBallCutoffJets 3 η hη)) f
  filter_upwards [hMult,ae_restrict_mem ballOpens.isOpen.measurableSet] with z hM hz
  change (coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 (nativeUnitBallCutoffJets 3 η hη)) f) z = _
  simp only [TauCeti.Wkp.value_zero] at hM
  rw [hM,coefficientValue_repackedJets,coefficientValue_nativeUnitBallCutoffJets_on_ball 3 η hη z hz]

theorem nativeUnitBallCutoff_forcing_eq_zero_of_ae
    (hcalc : FixedSobolevCalculus) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) (f : BallSobolev 0)
    (hZero : ∀ᵐ z ∂volume.restrict ballOpens, η z * f z = 0) :
    coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 (nativeUnitBallCutoffJets 3 η hη)) f = 0 := by
  have h0 : (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun _ => (0 : ℝ)) := Lp.coeFn_zero ℝ 2 _
  apply Lp.ext
  filter_upwards [nativeUnitBallCutoff_forcing_ae hcalc η hη f,hZero,h0] with z hM hZ h0
  rw [hM,hZ,h0]

def referencePhysicalGaugeCutoffCommutatorL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) (p : ℝ × (R3 × ℝ)) :
    BallSobolev 2 →L[ℝ] BallSobolev 1 :=
  -nativeHighBulkMultiplierCommutatorForcingL hcalc
    (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)
    (fun _ => 0) (nativeUnitBallCutoffJets 3 η hη)

theorem contDiff_referencePhysicalGaugeCutoffCommutatorL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη) := by
  let A := referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2
  let q : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun x => unitBallSmoothCutoff x.2 * η x.2
  have hA : ContDiff ℝ ∞ A := contDiff_referencePhysicalGaugeCompactPrincipalCoefficient
    g hg L y0 Φ B ε C ρ H a w hData
  have hq : ContDiff ℝ ∞ q :=
    (unitBallSmoothCutoff.contDiff.comp contDiff_snd).mul (hη.comp contDiff_snd)
  have hG : ∀ p : ℝ × (R3 × ℝ), nativeSmoothDriftField (fun _ : Fin 3 => (0 : SmoothCoefficientJets 1)) =
      fun _ : R3 => (0 : R3) := by
    intro p
    funext z
    ext i
    rw [nativeSmoothDriftField_coordinate]
    rfl
  have hN := contDiff_nativeHighBulkMultiplierCommutatorForcingL_of_joint_graphs
    hcalc A (fun _ => (0 : R3)) q hA contDiff_const hq
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside g L Φ H)
    (fun _ _ _ => rfl) F (fun _ _ => 0) (fun _ => nativeUnitBallCutoffJets 3 η hη)
    (coefficientMatrixField_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2)
    hG (fun _ => coefficientValue_nativeUnitBallCutoffJets 3 η hη)
  exact hN.neg

theorem exists_compact_uniform_referencePhysicalGaugeCutoffCommutatorL_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ p ∈ K,
      ‖referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη p‖ ≤ M := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη).continuous.continuousOn
  exact ⟨max M 1,le_max_right _ _,fun p hp => (hM p hp).trans (le_max_left _ _)⟩

end OAI.AnisotropicCalderon.ConnectionError
