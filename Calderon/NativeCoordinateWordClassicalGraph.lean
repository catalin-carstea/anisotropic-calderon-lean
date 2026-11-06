import Calderon.NativeLocalCoordinateDerivativeGraph
import Calderon.ActualReferenceDDHigherHCoframeJets
import Mathlib.Data.List.OfFn

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume ReferenceDensityBounds
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets

/-- Actual coordinate words, with the last letter applied first. -/
def unitBallCoordinateWordL (hcalc : FixedSobolevCalculus) :
    (n : ℕ) → (s : ℕ) → (Fin n → Fin 3) →
      BallSobolev (s + n) →L[ℝ] BallSobolev s
  | 0, s, _ => ContinuousLinearMap.id ℝ (BallSobolev s)
  | n + 1, s, w =>
      (unitBallCoordinateWordL hcalc n s (fun i => w i.castSucc)).comp
        (unitBallCoordinateDerivativeL hcalc (s + n) (w (Fin.last n)))

/-- The finite-index native word agrees with the original ordered classical word. -/
theorem unitBallCoordinateWordL_value_ae_of_contDiffOn
    (hcalc : FixedSobolevCalculus) (n s : ℕ) (w : Fin n → Fin 3)
    (U : BallSobolev (s + n)) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f ballOpens)
    (hU : (TauCeti.Wkp.value (s + n) U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f) :
    (TauCeti.Wkp.value s (unitBallCoordinateWordL hcalc n s w U) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      coordinateFieldWordPartial (List.ofFn w) f := by
  induction n generalizing s f with
  | zero =>
      change (TauCeti.Wkp.value s U : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict ballOpens] f
      exact hU
  | succ n ih =>
      let d : R3 → ℝ := fun x => fderiv ℝ f x (coordinateDirection (w (Fin.last n)))
      have hd : ContDiffOn ℝ ∞ d ballOpens :=
        (hf.fderiv_of_isOpen ballOpens.isOpen (by simp)).clm_apply contDiffOn_const
      have hOne := unitBallCoordinateDerivativeL_value_ae_of_contDiffOn hcalc (s + n)
        (w (Fin.last n)) U f hf hU
      have hD : (TauCeti.Wkp.value (s + n)
          (unitBallCoordinateDerivativeL hcalc (s + n) (w (Fin.last n)) U) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict ballOpens] d := by
        filter_upwards [hOne] with x hx
        exact hx.trans (congrArg (fun e : R3 => fderiv ℝ f x e)
          (show coordinateVector (w (Fin.last n)) = coordinateDirection (w (Fin.last n)) from rfl))
      have hWord := ih s (fun i => w i.castSucc)
        (unitBallCoordinateDerivativeL hcalc (s + n) (w (Fin.last n)) U) d hd hD
      have hFunction : coordinateFieldWordPartial (List.ofFn w) f =
          coordinateFieldWordPartial (List.ofFn (fun i : Fin n => w i.castSucc)) d := by
        rw [List.ofFn_succ', List.concat_eq_append, coordinateFieldWordPartial_append]
        rfl
      change (TauCeti.Wkp.value s
        (unitBallCoordinateWordL hcalc n s (fun i => w i.castSucc)
          (unitBallCoordinateDerivativeL hcalc (s + n) (w (Fin.last n)) U)) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
        coordinateFieldWordPartial (List.ofFn w) f
      filter_upwards [hWord] with x hx
      exact hx.trans (congrFun hFunction.symm x)

/-- No new classical word convention is introduced for list-indexed consumers. -/
theorem unitBallCoordinateWordL_list_value_ae_of_contDiffOn
    (hcalc : FixedSobolevCalculus) (s : ℕ) (w : List (Fin 3))
    (U : BallSobolev (s + w.length)) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f ballOpens)
    (hU : (TauCeti.Wkp.value (s + w.length) U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f) :
    (TauCeti.Wkp.value s (unitBallCoordinateWordL hcalc w.length s w.get U) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] coordinateFieldWordPartial w f := by
  simpa only [List.ofFn_get] using
    unitBallCoordinateWordL_value_ae_of_contDiffOn hcalc w.length s w.get U f hf hU

/-- A finite word bound is chosen before the word and the actual graph-space input. -/
theorem exists_norm_bound_unitBallCoordinateWordL
    (hcalc : FixedSobolevCalculus) (n s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin n → Fin 3) (U : BallSobolev (s + n)),
      ‖unitBallCoordinateWordL hcalc n s w U‖ ≤ C * ‖U‖ := by
  refine ⟨∑ w : Fin n → Fin 3, ‖unitBallCoordinateWordL hcalc n s w‖,
    Finset.sum_nonneg (fun w _ => norm_nonneg _), ?_⟩
  intro w U
  have hOperator : ‖unitBallCoordinateWordL hcalc n s w‖ ≤
      ∑ v : Fin n → Fin 3, ‖unitBallCoordinateWordL hcalc n s v‖ :=
    Finset.single_le_sum (fun v _ => norm_nonneg _) (Finset.mem_univ w)
  exact ((unitBallCoordinateWordL hcalc n s w).le_opNorm U).trans
    (mul_le_mul_of_nonneg_right hOperator (norm_nonneg U))

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoordinateWordL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoordinateWordL_value_ae_of_contDiffOn
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoordinateWordL_list_value_ae_of_contDiffOn
#print axioms OAI.AnisotropicCalderon.DirichletFamily.exists_norm_bound_unitBallCoordinateWordL
