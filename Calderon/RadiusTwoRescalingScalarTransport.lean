import Calderon.RadiusTwoSmoothRescaling
import Calderon.RadiusTwoNativeSourceFoundation
import TauCeti.Analysis.PDE.EnergyForm.Basic

/-! EXPANSION.json precedes constructor-free scalar transport primitives. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError

theorem matrixBilinearForm_two_smul_two_smul
    (A : Matrix (Fin 3) (Fin 3) ℝ) (V U : R3) :
    TauCeti.PDE.matrixBilinearForm A ((2 : ℝ) • V) ((2 : ℝ) • U) =
      4 * TauCeti.PDE.matrixBilinearForm A V U := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,RingHom.id_apply]
  ring

theorem setIntegral_matrixBilinear_radiusTwo_transport
    (Aouter Ainner : MatrixField) (Xouter Youter Xinner Yinner : R3 → R3)
    (hA : ∀ x : R3, Ainner x = Aouter ((2 : ℝ) • x))
    (hX : Xinner =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => (2 : ℝ) • Xouter ((2 : ℝ) • x)))
    (hY : Yinner =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => (2 : ℝ) • Youter ((2 : ℝ) • x))) :
    (∫ x in ballOpens, TauCeti.PDE.matrixBilinearForm (Ainner x) (Xinner x) (Yinner x)
      ∂(volume : Measure R3)) = (1/2 : ℝ) *
      (∫ z in radiusTwoOpens, TauCeti.PDE.matrixBilinearForm (Aouter z) (Xouter z) (Youter z)
        ∂(volume : Measure R3)) := by
  let f : R3 → ℝ := fun z => TauCeti.PDE.matrixBilinearForm (Aouter z) (Xouter z) (Youter z)
  have hAE : (fun x : R3 => TauCeti.PDE.matrixBilinearForm (Ainner x) (Xinner x) (Yinner x))
      =ᵐ[(volume : Measure R3).restrict ballOpens] (fun x : R3 => 4 * f ((2 : ℝ) • x)) := by
    filter_upwards [hX,hY] with x hx hy
    calc
      _ = TauCeti.PDE.matrixBilinearForm (Aouter ((2 : ℝ) • x)) (Xinner x) (Yinner x) :=
        congrArg (fun A => TauCeti.PDE.matrixBilinearForm A (Xinner x) (Yinner x)) (hA x)
      _ = TauCeti.PDE.matrixBilinearForm (Aouter ((2 : ℝ) • x))
          ((2 : ℝ) • Xouter ((2 : ℝ) • x)) ((2 : ℝ) • Youter ((2 : ℝ) • x)) :=
        congrArg₂ (fun X Y : R3 => TauCeti.PDE.matrixBilinearForm (Aouter ((2 : ℝ) • x)) X Y) hx hy
      _ = _ := matrixBilinearForm_two_smul_two_smul _ _ _
  have hInt := integral_congr_ae hAE
  rw [integral_const_mul] at hInt
  have hOuter := setIntegral_ball_two_eq_eight_comp_two f
  change _ = (1/2 : ℝ) * (∫ z in Metric.ball (0 : R3) 2, f z ∂volume)
  rw [hInt,hOuter]
  simp only [coe_ballOpens,B]
  ring

theorem setIntegral_product_radiusTwo_transport
    (fouter vouter finner vinner : R3 → ℝ)
    (hF : finner =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => fouter ((2 : ℝ) • x)))
    (hV : vinner =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => vouter ((2 : ℝ) • x))) :
    (∫ z in radiusTwoOpens, fouter z * vouter z ∂(volume : Measure R3)) =
      8 * (∫ x in ballOpens, finner x * vinner x ∂(volume : Measure R3)) := by
  have hOuter := setIntegral_ball_two_eq_eight_comp_two (fun z : R3 => fouter z * vouter z)
  have hAE : (fun x : R3 => fouter ((2 : ℝ) • x) * vouter ((2 : ℝ) • x))
      =ᵐ[(volume : Measure R3).restrict ballOpens] (fun x : R3 => finner x * vinner x) := by
    filter_upwards [hF,hV] with x hf hv
    exact congrArg₂ (fun r s : ℝ => r*s) hf.symm hv.symm
  exact hOuter.trans (congrArg (fun t : ℝ => 8*t) (integral_congr_ae hAE))

end OAI.AnisotropicCalderon.ExteriorSource
