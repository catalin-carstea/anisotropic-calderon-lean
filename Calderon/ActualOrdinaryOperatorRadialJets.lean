import Calderon.ActualReferenceRadialJets
import Calderon.OrdinaryStrongDriftRadialJet

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator

def jointFixedParameterSlice {V : Type*} (f : (ℝ × (R3 × ℝ)) × R3 → V)
    (q : ℝ) (p : (R3 × ℝ) × R3) : V := f ((q,p.1),p.2)

theorem contDiff_jointFixedParameterSlice {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × (R3 × ℝ)) × R3 → V) (hf : ContDiff ℝ ∞ f) (q : ℝ) :
    ContDiff ℝ ∞ (jointFixedParameterSlice f q) := by
  exact hf.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
theorem jointFixedParameterSlice_data (q : ℝ) :
    ContDiff ℝ ∞ (jointFixedParameterSlice a q) ∧
    ContDiff ℝ ∞ (jointFixedParameterSlice w q) ∧
    ContDiff ℝ ∞ (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) ∧
    (∀ p z, z ∉ closedBall (0 : R3) 3 → jointFixedParameterSlice a q (p,z) = 0) ∧
    (∀ p z, z ∉ closedBall (0 : R3) 3 → jointFixedParameterSlice w q (p,z) = 0) := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,ha,hw,hSupport,_,_,_,_⟩
  refine ⟨contDiff_jointFixedParameterSlice a ha q,
    contDiff_jointFixedParameterSlice w hw q,
    contDiff_jointFixedParameterSlice _ hData.2.1 q, ?_, ?_⟩
  · intro p z hz
    have hz3 : 3 ≤ ‖z‖ := le_of_lt (by
      simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
    exact (hSupport (q,p) z hz3).1
  · intro p z hz
    have hz3 : 3 ≤ ‖z‖ := le_of_lt (by
      simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
    exact (hSupport (q,p) z hz3).2

def referenceOrdinaryStrongDriftFamily (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) :
    R3 × ℝ → BallSobolev (s+2) →L[ℝ] BallSobolev s :=
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  ordinaryStrongDriftFamily hcalc s
    (jointFixedParameterSlice a q) h.1
    (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L

theorem referenceOrdinaryStrongDriftFamily_zero_apply
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (E : BallSobolev (s+2)) :
    referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0) E =
      -∑ i : Fin 3, unitBallCoordinateDerivativeL hcalc s i
        (unitBallCoordinateDerivativeL hcalc (s+1) i E) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hρ : 0 < ρ := hData.1.2.1
  have hzero : ∀ z ∈ (ballOpens : Set R3), jointFixedParameterSlice a q ((y,0),z) = 1 := by
    intro z hz
    change dist z (0 : R3) < (1 : ℝ) at hz
    rw [dist_zero_right] at hz
    exact (jointReference_coefficient_zero_radial_jets g L y0 Φ B ε C ρ H a w hData
      q hq y (by linarith) z (by linarith)).2.1
  exact ordinaryStrongDriftFamily_zero_apply hcalc s _ h.1 _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L y hzero E

theorem hasDerivAt_referenceOrdinaryStrongDriftFamily_zero
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    HasDerivAt
      (fun r : ℝ => referenceOrdinaryStrongDriftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r))
      (-∑ i : Fin 3, (referenceCenterDrift g L q y i) •
        ordinaryLowerOrderCoordinateDerivativeL hcalc s i) 0 := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  let b0 : R3 := (conformalReferenceGramFrameOperatorJoint g L (q,y)).adjoint
    (gradient conformalReferenceCoordinateDepth y)
  have hρ : 0 < ρ := hData.1.2.1
  have ha0 : ∀ z ∈ (ballOpens : Set R3),
      HasDerivAt (fun r : ℝ => jointFixedParameterSlice a q ((y,r),z)) 0 0 := by
    intro z hz
    change dist z (0 : R3) < (1 : ℝ) at hz
    rw [dist_zero_right] at hz
    exact (jointReference_coefficient_zero_radial_jets g L y0 Φ B ε C ρ H a w hData
      q hq y (by linarith) z (by linarith)).2.2.2.2.1
  have hb0 : ∀ z ∈ (ballOpens : Set R3), ∀ i : Fin 3,
      jointFixedParameterSlice w q ((y,0),z) *
        jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q ((y,0),z) i = b0 i := by
    intro z hz i
    change dist z (0 : R3) < (1 : ℝ) at hz
    rw [dist_zero_right] at hz
    have hCoeff := jointReference_coefficient_zero_radial_jets g L y0 Φ B ε C ρ H a w hData
      q hq y (by linarith) z (by linarith)
    have hBase := jointReferenceFramedDriftBase_zero g L y0 Φ B ε C ρ H a w hData
      q hq y (by linarith) z (by linarith)
    change w ((q,(y,0)),z) * conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z) i = _
    rw [hCoeff.2.2.1,hBase,one_mul]
  have hj := hasDerivAt_ordinaryStrongDriftFamily_zero hcalc s _ h.1 _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L y ha0
  rw [ordinaryWeightedDriftBaseL_zero_eq hcalc s _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.2 y b0 hb0] at hj
  have hd : referenceCenterDrift g L q y = L • b0 := rfl
  have he : (-L) • (∑ i : Fin 3, (b0 i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i) =
      -∑ i : Fin 3, (referenceCenterDrift g L q y i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i := by
    rw [hd]
    simp only [PiLp.smul_apply,smul_eq_mul,Finset.smul_sum,neg_smul,smul_smul,neg_mul,Finset.sum_neg_distrib]
  rw [he] at hj
  exact hj

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
