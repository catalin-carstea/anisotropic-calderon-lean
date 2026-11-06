import Calderon.NativeCoefficientMultiplierOrderCoherence
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.CoefficientFirstJetsCommonSupport

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. Topology from actual scalar functions. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma coefficientRepackedJets_eq_commonSupport_of_value_graph
    (r s : ℕ) (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x)=0)
    (F : P → SmoothCoefficientJets r)
    (hF : ∀ p, coefficientValue r (F p) = fun x => g (p,x)) (p : P) :
    coefficientRepackedJets r s (F p) = commonSupportCoefficientFamily s g hg K hK hz p := by
  apply smoothCoefficientJets_eq_of_coefficientValue_eq s
  funext x
  rw [coefficientValue_repackedJets,coefficientValue_commonSupportCoefficientFamily]
  exact congrFun (hF p) x

lemma contDiff_repackedCoefficientMultiplier_of_value_graph
    (hcalc : FixedSobolevCalculus) (k r : ℕ)
    (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x)=0)
    (F : P → SmoothCoefficientJets r)
    (hF : ∀ p, coefficientValue r (F p) = fun x => g (p,x)) :
    ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc k (coefficientRepackedJets r (k+1) (F p))) := by
  have he : (fun p => coefficientMultiplier hcalc k (coefficientRepackedJets r (k+1) (F p))) =
      fun p => coefficientMultiplier hcalc k (commonSupportCoefficientFamily (k+1) g hg K hK hz p) := by
    funext p
    exact congrArg (coefficientMultiplier hcalc k)
      (coefficientRepackedJets_eq_commonSupport_of_value_graph r (k+1) g hg K hK hz F hF p)
  rw [he]
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc k g hg K hK hz

lemma contDiff_repackedNativeThreeHalfCoefficientMulL_of_value_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (r : ℕ) (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → g (p,x)=0)
    (F : P → SmoothCoefficientJets r)
    (hValue : ∀ p, coefficientValue r (F p) = fun x => g (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRepackedJets r 3 (F p))) := by
  have he : (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRepackedJets r 3 (F p))) =
      fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 g hg K hK hz p) := by
    funext p
    exact congrArg (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0)
      (coefficientRepackedJets_eq_commonSupport_of_value_graph r 3 g hg K hK hz F hValue p)
  rw [he]
  exact contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 g hg K hK hz

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientRepackedJets_eq_commonSupport_of_value_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_repackedCoefficientMultiplier_of_value_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_repackedNativeThreeHalfCoefficientMulL_of_value_graph

