import Calderon.ActualJointReferenceCoefficientData
import Calderon.ActualReferenceInverseConsistency
import Calderon.SmoothCommonSupportStrongOperator
import Calderon.CompactInverseDerivativeBounds

/-! Source-only exact joint actual inverse topology on the same common weak
room. Joint coefficient maps are the native maps of the identical evaluated
spatial functions. No new operator or desired uniform inverse premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem referenceStrongDriftFamily_joint_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ) :
    (fun p : ℝ × (R3 × ℝ) =>
      referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2) =
      let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
      fun p : ℝ × (R3 × ℝ) =>
        strongDirichletOperator hcalc s
          (commonSupportMatrixFamily (s+2) a h.1
            (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p) +
        (-L*p.2.2) • commonSupportWeightedDriftBaseOperator hcalc s w h.2.1
          (conformalReferenceFramedDriftBase g L Φ H) h.2.2.1
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.2 p := by
  funext p
  rw [referenceStrongDriftFamily_eq_commonSupport
    g L y0 Φ B ε C ρ H a w hData hcalc s p.1]
  rfl

theorem contDiff_joint_referenceStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2) := by
  rw [referenceStrongDriftFamily_joint_eq g L y0 Φ B ε C ρ H a w hData hcalc s]
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  change ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
    strongDirichletOperator hcalc s
      (commonSupportMatrixFamily (s+2) a h.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p) +
    (-L*p.2.2) • commonSupportWeightedDriftBaseOperator hcalc s w h.2.1
      (conformalReferenceFramedDriftBase g L Φ H) h.2.2.1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.2 p)
  have hA := contDiff_commonSupport_actual_strongDirichletOperator hcalc s a h.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1
  have hD := contDiff_commonSupportWeightedDriftBaseOperator hcalc s w h.2.1
    (conformalReferenceFramedDriftBase g L Φ H) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.2
  exact hA.add ((contDiff_const.mul contDiff_snd.snd).smul hD)

theorem exists_reference_commonRadius_allOrder_jointInverse_bounds
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ ρ ∧ ∀ s : ℕ,
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-delta) delta),
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).inverse)
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-delta) delta)) ∧
      (∃ D : ℝ, 0 ≤ D ∧
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-delta) delta),
          ‖(referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).inverse‖ ≤ D) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-delta) delta),
          ‖iteratedFDeriv ℝ j (fun t : ℝ × (R3 × ℝ) =>
            (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s t.1 t.2).inverse) p‖ ≤ D := by
  obtain ⟨lam,Lam,delta,hlam,hd,hdρ,hRoom⟩ :=
    exists_reference_commonRadius_allOrder_strongDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg
  refine ⟨delta,hd,hdρ,?_⟩
  intro s
  letI : CompleteSpace (StrongDirichletSpace s) := instCompleteSpaceStrongDirichletSpace s
  let A : ℝ × (R3 × ℝ) → StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    fun p => referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2
  let S : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-delta) delta)
  have hS : IsCompact S :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s
  have hi : ∀ p ∈ S, (A p).IsInvertible := by
    intro p hp
    have hy : ‖p.2.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    exact (hRoom p.1 hp.1 p.2.1 hy p.2.2 (abs_le.mpr hp.2.2)).2 s
  refine ⟨hi,contDiffOn_banachInverseFamily A S hA.contDiffOn hi,
    uniform_norm_banachInverseFamily A S hS hA.continuous.continuousOn hi,?_⟩
  intro N
  exact exists_compact_banachInverse_derivative_bound A hA S hS hi N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
