import Calderon.SmoothSobolevBridge

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem gradient_ae_eq_of_smooth_ball_representative
    (u : BallH1) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f (ballOpens : Set R3))
    (hValue : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f) :
    (TauCeti.W1p.gradient u : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict ballOpens] gradient f := by
  have hWeak : TauCeti.HasWeakFDerivOn (volume : Measure R3) ballOpens f
      (fun x => innerSL ℝ (TauCeti.W1p.gradient u x)) :=
    (TauCeti.W1p.hasWeakFDerivOn u).congr_ae hValue
  have hCont : ContinuousOn (fderiv ℝ f) (ballOpens : Set R3) :=
    hf.continuousOn_fderiv_of_isOpen ballOpens.isOpen (by simp)
  have hDiff (x : R3) (hx : x ∈ (ballOpens : Set R3)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (ballOpens.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hDeriv : (fun x => innerSL ℝ (TauCeti.W1p.gradient u x))
      =ᵐ[(volume : Measure R3).restrict ballOpens] fderiv ℝ f :=
    hWeak.ae_eq_fderiv (hCont.locallyIntegrableOn ballOpens.isOpen.measurableSet) hDiff
  filter_upwards [hDeriv] with x hx
  apply (innerSL_inj (𝕜 := ℝ)).mp
  rw [hx]
  ext v
  exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := v)).symm

theorem memLp_value_gradient_of_smooth_ball_representative
    (u : BallH1) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f (ballOpens : Set R3))
    (hValue : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f) :
    MemLp f 2 ((volume : Measure R3).restrict ballOpens) ∧
      MemLp (gradient f) 2 ((volume : Measure R3).restrict ballOpens) := by
  have hv : MeasureTheory.MemLp (TauCeti.W1p.value u : R3 → ℝ) 2
      ((volume : Measure R3).restrict ballOpens) :=
    MeasureTheory.Lp.memLp (TauCeti.W1p.value u)
  have hg : MeasureTheory.MemLp (TauCeti.W1p.gradient u : R3 → R3) 2
      ((volume : Measure R3).restrict ballOpens) :=
    MeasureTheory.Lp.memLp (TauCeti.W1p.gradient u)
  exact ⟨(MeasureTheory.memLp_congr_ae hValue).mp hv,
    (MeasureTheory.memLp_congr_ae
      (gradient_ae_eq_of_smooth_ball_representative u f hf hValue)).mp hg⟩

end OAI.AnisotropicCalderon.DirichletFamily
