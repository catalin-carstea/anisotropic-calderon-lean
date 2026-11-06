import Calderon.NativeHighSmoothMultiplierForcing
import Calderon.NativeRepackedCoefficientMultiplierTopology

/-! High forcing topology from actual coefficient graphs. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

attribute [local irreducible] nativeH2FirstOrderL coefficientMultiplier unitBallCoordinateDerivativeL

lemma contDiff_nativeHighSmoothMultiplierForcingL_of_value_graphs
    (hcalc : FixedSobolevCalculus)
    (C R : Fin 3 → P × R3 → ℝ) (d : P × R3 → ℝ)
    (hC : ∀ i, ContDiff ℝ ∞ (C i)) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (hd : ContDiff ℝ ∞ d)
    (K : Set R3) (hK : IsCompact K)
    (hCz : ∀ i p x, x ∉ K → C i (p,x)=0)
    (hRz : ∀ i p x, x ∉ K → R i (p,x)=0)
    (hdz : ∀ p x, x ∉ K → d (p,x)=0)
    (F : P → Fin 3 → SmoothCoefficientJets 2)
    (G : P → Fin 3 → SmoothCoefficientJets 1) (D : P → SmoothCoefficientJets 1)
    (hF : ∀ p i, coefficientValue 2 (F p i) = fun x => C i (p,x))
    (hG : ∀ p i, coefficientValue 1 (G p i) = fun x => R i (p,x))
    (hD : ∀ p, coefficientValue 1 (D p) = fun x => d (p,x)) :
    ContDiff ℝ ∞ (fun p => nativeHighSmoothMultiplierForcingL hcalc (F p) (G p) (D p)) := by
  have hColumn (i : Fin 3) : ContDiff ℝ ∞ (fun p : P =>
      (unitBallCoordinateDerivativeL hcalc 1 i).comp
        (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 (F p i)))) :=
    contDiff_const.clm_comp
      (contDiff_repackedCoefficientMultiplier_of_value_graph hcalc 2 2
        (C i) (hC i) K hK (hCz i) (fun p => F p i) (fun p => hF p i))
  have hRow (j : Fin 3) : ContDiff ℝ ∞ (fun p : P =>
      (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (G p j))).comp
        (unitBallCoordinateDerivativeL hcalc 1 j)) :=
    (contDiff_repackedCoefficientMultiplier_of_value_graph hcalc 1 1
      (R j) (hR j) K hK (hRz j) (fun p => G p j) (fun p => hG p j)).clm_comp contDiff_const
  have hDrift : ContDiff ℝ ∞ (fun p : P =>
      (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (D p))).comp
        nativeH2FirstOrderL) :=
    (contDiff_repackedCoefficientMultiplier_of_value_graph hcalc 1 1 d hd K hK hdz D hD).clm_comp contDiff_const
  unfold nativeHighSmoothMultiplierForcingL
  exact ((ContDiff.sum (fun i _ => hColumn i)).add (ContDiff.sum (fun j _ => hRow j))).sub hDrift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeHighSmoothMultiplierForcingL_of_value_graphs

