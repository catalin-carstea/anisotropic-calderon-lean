import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-! EXPANSION.json precedes isolated literal native gradient indicator evaluation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local irreducible] TauCeti.W1p.posPartAbove TauCeti.W1p.posPart

theorem nativeH1_gradient_posPartAbove_literal_ae (u : BallH1) (ε : ℝ) (hε : 0 ≤ ε) :
    TauCeti.W1p.gradient (TauCeti.W1p.posPartAbove (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
        (fun x => if ε < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else 0) := by
  exact (TauCeti.W1p.gradient_posPartAbove_ae (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε u).mono
    (fun x hx => by
      rw [hx]
      change ({y | ε < TauCeti.W1p.value u y}.indicator (⇑(TauCeti.W1p.gradient u))) x =
        (if ε < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3))
      by_cases ht : ε < TauCeti.W1p.value u x
      · rw [if_pos ht,Set.indicator_of_mem
          (show x ∈ {y | ε < TauCeti.W1p.value u y} from ht)]
      · rw [if_neg ht,Set.indicator_of_notMem
          (show x ∉ {y | ε < TauCeti.W1p.value u y} from ht)])

theorem nativeH1_gradient_posPart_literal_ae (u : BallH1) :
    TauCeti.W1p.gradient (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
        (fun x => if 0 < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else 0) := by
  exact (TauCeti.W1p.gradient_posPart_ae (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u).mono
    (fun x hx => by
      rw [hx]
      change ({y | 0 < TauCeti.W1p.value u y}.indicator (⇑(TauCeti.W1p.gradient u))) x =
        (if 0 < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3))
      by_cases ht : 0 < TauCeti.W1p.value u x
      · rw [if_pos ht,Set.indicator_of_mem
          (show x ∈ {y | 0 < TauCeti.W1p.value u y} from ht)]
      · rw [if_neg ht,Set.indicator_of_notMem
          (show x ∉ {y | 0 < TauCeti.W1p.value u y} from ht)])

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.nativeH1_gradient_posPartAbove_literal_ae
#print axioms OAI.AnisotropicCalderon.EnergyBridge.nativeH1_gradient_posPart_literal_ae
