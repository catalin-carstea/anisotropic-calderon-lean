import Calderon.NativeHighBulkMultiplierCommutatorForcingTopology
import Calderon.ActualHighSmoothMultiplierStrongDefect
import Calderon.ActualReferenceCoordinateCorrectionTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. Independent actual geometry and multiplier parameters. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (Kq : Set R3) (hKq : IsCompact Kq)
  (hqz : ∀ t x, x ∉ Kq → q (t,x) = 0)

lemma contDiff_referenceHighSmoothMultiplierForcing_commonSupport_joint
    (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceHighSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc
        (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) := by
  let ha := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hb := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let A : ((ℝ × (R3 × ℝ)) × T) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun z => a (z.1.1,z.2)
  let b : ((ℝ × (R3 × ℝ)) × T) × R3 → R3 :=
    fun z => conformalReferenceWeightedFramedDrift g L Φ H w (z.1.1,z.2)
  let m : ((ℝ × (R3 × ℝ)) × T) × R3 → ℝ := fun z => q (z.1.2,z.2)
  have hA : ContDiff ℝ ∞ A := ha.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hb' : ContDiff ℝ ∞ b := hb.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hm : ContDiff ℝ ∞ m := hq.comp (contDiff_fst.snd.prodMk contDiff_snd)
  exact contDiff_nativeHighBulkMultiplierCommutatorForcingL_of_joint_graphs hcalc A b m hA hb' hm
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun z x hx => ha.2.2.2.1 z.1 x hx) (fun z x hx => hb.2 z.1 x hx)
    (fun z => referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2)
    (fun z => coefficientMatrixField_referenceCoordinateForcingPrincipalJets
      g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => nativeSmoothDriftField_referenceCoordinateForcingDriftJets
      g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => by funext x; exact coefficientValue_commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2 x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceHighSmoothMultiplierForcing_commonSupport_joint
