import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.ClosedCoefficientMultiplier

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-H1-product-fixed-topology-helper-v038.md. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma contDiff_nativeCoefficientH1ProductL_commonSupport
    (hcalc : FixedSobolevCalculus) (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : P => nativeCoefficientH1ProductL hcalc
      (commonSupportCoefficientFamily 2 g hg K hK hz p)) := by
  let D : BallSobolev 1 →L[ℝ] BallH1 :=
    TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0
  let M : P → BallSobolev 1 →L[ℝ] BallSobolev 1 := fun p =>
    coefficientMultiplier hcalc 1 (commonSupportCoefficientFamily 2 g hg K hK hz p)
  have hM : ContDiff ℝ ∞ M :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 1 g hg K hK hz
  have hD : ContDiff ℝ ∞ (fun _ : P => D) := contDiff_const
  change ContDiff ℝ ∞ (fun p : P => D.comp (M p))
  exact hD.clm_comp hM

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeCoefficientH1ProductL_commonSupport
