import Calderon.ClosedCoefficientMultiplier
import Calderon.NativeSmoothOperatorRealization

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
SMOOTH-BALL-FAMILY-EXPANSION-v001.md. Same native graph elements, no chosen-jet premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem contDiff_smoothBallSobolev_commonSupport
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (fun t => smoothBallSobolev k
      ⟨fun x => g (t,x), SpatialJetFields.contDiff_spatial_slice g hg t⟩) := by
  let one : SmoothData := ⟨fun _ => 1, contDiff_const⟩
  let F := commonSupportCoefficientFamily (k+1) g hg K hK hz
  have hSmooth := (contDiff_commonSupport_actual_coefficientMultiplier
    hcalc k g hg K hK hz).clm_apply
    (show ContDiff ℝ ∞ (fun _ : H => smoothBallSobolev k one) from contDiff_const)
  have hEqual : (fun t => coefficientMultiplier hcalc k (F t) (smoothBallSobolev k one)) =
      (fun t => smoothBallSobolev k
        ⟨fun x => g (t,x), SpatialJetFields.contDiff_spatial_slice g hg t⟩) := by
    funext t
    rw [coefficientMultiplier_smoothBallSobolev]
    apply congrArg (smoothBallSobolev k)
    apply Subtype.ext
    funext x
    change coefficientValue (k+1) (F t) x * 1 = g (t,x)
    rw [mul_one]
    exact coefficientValue_commonSupportCoefficientFamily (k+1) g hg K hK hz t x
  rw [← hEqual]
  exact hSmooth

theorem contDiff_smoothBallSobolev_of_joint
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun t => smoothBallSobolev k
      ⟨fun x => g (t,x), SpatialJetFields.contDiff_spatial_slice g hg t⟩) := by
  let G : H × R3 → ℝ := fun p => unitBallSmoothCutoff p.2 * g p
  have hG : ContDiff ℝ ∞ G := (unitBallSmoothCutoff.contDiff.comp contDiff_snd).mul hg
  let K := tsupport (unitBallSmoothCutoff : R3 → ℝ)
  have hK : IsCompact K := unitBallSmoothCutoff.hasCompactSupport
  have hz : ∀ t x, x ∉ K → G (t,x) = 0 := by
    intro t x hx
    have hzero : unitBallSmoothCutoff x = 0 := by
      by_contra hne
      exact hx (subset_tsupport (unitBallSmoothCutoff : R3 → ℝ) hne)
    change unitBallSmoothCutoff x * g (t,x) = 0
    rw [hzero, zero_mul]
  have hSmooth := contDiff_smoothBallSobolev_commonSupport hcalc k G hG K hK hz
  have hEqual : (fun t => smoothBallSobolev k
      ⟨fun x => G (t,x), SpatialJetFields.contDiff_spatial_slice G hG t⟩) =
      (fun t => smoothBallSobolev k
        ⟨fun x => g (t,x), SpatialJetFields.contDiff_spatial_slice g hg t⟩) := by
    funext t
    apply TauCeti.Wkp.ext k
    apply Lp.ext
    filter_upwards
      [value_smoothBallSobolev_ae k
        ⟨fun x => G (t,x), SpatialJetFields.contDiff_spatial_slice G hG t⟩,
       value_smoothBallSobolev_ae k
        ⟨fun x => g (t,x), SpatialJetFields.contDiff_spatial_slice g hg t⟩,
       ae_restrict_mem ballOpens.isOpen.measurableSet] with x hLeft hRight hmem
    rw [hLeft, hRight]
    change unitBallSmoothCutoff x * g (t,x) = g (t,x)
    rw [unitBallSmoothCutoff_one_of_mem hmem, one_mul]
  rw [← hEqual]
  exact hSmooth

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiff_smoothBallSobolev_commonSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiff_smoothBallSobolev_of_joint
