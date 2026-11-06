import Calderon.StrongOperatorForcing

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem contDiff_coefficientMatrixField (r : ℕ) (F : SmoothCoefficientMatrix r) :
    ContDiff ℝ ∞ (coefficientMatrixField r F) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_coefficientValue r (F i j)

theorem contDiffOn_coefficientMatrixField_closedBall (r : ℕ)
    (F : SmoothCoefficientMatrix r) :
    ContDiffOn ℝ ∞ (coefficientMatrixField r F) (Metric.closedBall 0 2) :=
  (contDiff_coefficientMatrixField r F).contDiffOn

theorem aestronglyMeasurable_coefficientMatrixField (r : ℕ)
    (F : SmoothCoefficientMatrix r) :
    AEStronglyMeasurable (coefficientMatrixField r F)
      ((volume : Measure R3).restrict ballOpens) :=
  (contDiff_coefficientMatrixField r F).continuous.aestronglyMeasurable

theorem memLp_coefficientMatrixEnergyIntegrand (r : ℕ) (F : SmoothCoefficientMatrix r)
    {lam Lam : ℝ} (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField r F) lam Lam) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField r F x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  TauCeti.PDE.memLp_energyIntegrand_of_bounds ha.upper_nonneg
    (aestronglyMeasurable_coefficientMatrixField r F)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx eta xi => ha.upper_bound hx eta xi)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

end OAI.AnisotropicCalderon.DirichletFamily
