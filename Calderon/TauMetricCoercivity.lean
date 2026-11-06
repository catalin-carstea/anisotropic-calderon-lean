import Calderon.TauAffineAlgebra
import Calderon.MetricUniform

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

/-- Boundedness of the actual coefficient form follows from frozen admissibility. -/
theorem memLp_metricEnergyIntegrand (g : MatrixField) (hg : IsAdmissibleMetric g) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens) := by
  obtain ⟨M, hM, hupper⟩ := exists_principalCoefficient_upper_bound g hg
  exact TauCeti.PDE.memLp_energyIntegrand_of_bounds hM.le
    (continuous_principalCoefficient g hg).aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx => hupper x (Metric.ball_subset_closedBall hx))
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

/-- Actual Dirichlet energy coercivity is proved using Tau's checked ball Poincare bound. -/
theorem isCoercive_metricEnergyForm (g : MatrixField) (hg : IsAdmissibleMetric g) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens) (memLp_metricEnergyIntegrand g hg)) := by
  obtain ⟨lam, Lam, hu⟩ := exists_uniformlyEllipticOn_principalCoefficient_ball g hg
  have hu' : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (principalCoefficient g) lam Lam := hu
  apply TauCeti.PDE.isCoercive_energyFormH1L0 (memLp_metricEnergyIntegrand g hg)
    (C := (lam ^ 2) / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1)))
  · apply div_pos (sq_pos_of_pos hu.pos)
    have hlam : 0 < lam := hu.pos
    positivity
  · intro w
    have hn : ‖(w : BallH1)‖ = ‖w‖ := rfl
    have hb := hu'.mul_norm_sq_le_energyFormH1_self_of_subset_ball
      (continuous_principalCoefficient g hg).aestronglyMeasurable
      aestronglyMeasurable_const aestronglyMeasurable_const
      (b := fun _ : R3 => (0 : R3)) (c := fun _ : R3 => (0 : ℝ))
      (beta := 0) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
      (z := 0) (R := 1) (show (ballOpens : Set R3) ⊆ Metric.ball 0 1 from Set.Subset.rfl) w.2
    rw [hn] at hb
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero, mul_one] using hb

/-- Symmetry is likewise a consequence of exact positive definiteness. -/
theorem metricEnergy_coefficient_isSymm_ae (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, (principalCoefficient g x).IsSymm :=
  Filter.Eventually.of_forall fun x => (principalCoefficient_posDef g hg x).isHermitian.isSymm

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.memLp_metricEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.EnergyBridge.isCoercive_metricEnergyForm
#print axioms OAI.AnisotropicCalderon.EnergyBridge.metricEnergy_coefficient_isSymm_ae
