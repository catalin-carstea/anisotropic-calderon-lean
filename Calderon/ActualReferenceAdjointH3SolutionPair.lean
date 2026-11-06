import Calderon.ActualReferenceAdjointH3NativeLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- The actual H² inverse solution for one H¹ datum has an H³ representative
of the SAME first-order Dirichlet field. The full adjoint drift and mass are used. -/
theorem exists_referenceAdjointH3_solution_pair
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ))
    (hA0 : (referenceAdjointStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : BallSobolev 1) :
    ∃ U0 : StrongDirichletSpace 0,
      referenceAdjointStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc p U0 = nativeLowerOrderL 0 f ∧
      ∃ U : BallSobolev 3,
        TauCeti.Wkp.firstOrder 2 U =
          ((strongDirichletProjectionL 0 U0) : BallH1) := by
  let F := referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  let hb : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let hz : ∀ x, x ∉ K → beta x = 0 :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p
  have hNative : (nativeSupportedAdjointStrongDirichletL
      hcalc F 0 beta hb K hK hz).IsInvertible := by
    rw [← referenceAdjointStrongDirichletFamily_eq_native
      g L y0 Φ B ε C ρ H a w hData hcalc p]
    exact hA0
  obtain ⟨U,hU⟩ := exists_referenceAdjointH3_native_lift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg p hA0 f
  let U0 : StrongDirichletSpace 0 :=
    (nativeSupportedAdjointStrongDirichletL hcalc F 0 beta hb K hK hz).inverse
      (nativeLowerOrderL 0 f)
  refine ⟨U0, ?_, U, hU⟩
  have hEq : referenceAdjointStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeSupportedAdjointStrongDirichletL hcalc F 0 beta hb K hK hz :=
    referenceAdjointStrongDirichletFamily_eq_native
      g L y0 Φ B ε C ρ H a w hData hcalc p
  rw [hEq]
  exact hNative.self_apply_inverse _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
