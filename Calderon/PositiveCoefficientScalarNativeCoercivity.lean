import Calderon.SmoothPositiveCoefficientNativeCoercivity

/-! EXPANSION.json precedes this direct actual scalar energy lower bound.
No raw nested operator coercivity predicate is unpacked. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

theorem exists_positiveCoefficient_native_energy_lower_bound
    (A : MatrixField) (hA : Continuous A) (hPos : ∀ x, (A x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : BallH1Zero,
      c * ‖w‖^2 ≤ TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) (w : BallH1) (w : BallH1) := by
  obtain ⟨lam,Lam,hu⟩ := exists_uniformlyEllipticOn_continuousPositiveCoefficient_ball A hA hPos
  have hu' : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam := hu
  let c : ℝ := (lam^2) / (2*lam*((2*(1 : ℝ))^2+1))
  have hc : 0 < c := by
    dsimp only [c]
    apply div_pos (sq_pos_of_pos hu.pos)
    have hlam : 0 < lam := hu.pos
    positivity
  refine ⟨c,hc,?_⟩
  intro w
  have hn : ‖(w : BallH1)‖ = ‖w‖ := rfl
  have hb := hu'.mul_norm_sq_le_energyFormH1_self_of_subset_ball
    hA.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (z := (0 : R3)) (R := (1 : ℝ))
    (show (ballOpens : Set R3) ⊆ Metric.ball 0 1 from Set.Subset.rfl) w.2
  rw [hn] at hb
  simpa only [c,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul,sub_zero,mul_one] using hb

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_positiveCoefficient_native_energy_lower_bound
