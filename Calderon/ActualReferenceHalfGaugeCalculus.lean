import Calderon.NormalCoefficientResidualLpFamily
import Calderon.ActualReferenceGaugePrincipalFamily
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


def coefficientGradientFluxRow (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (s : P × R3 → ℝ) (i : Fin 3) (x : P × R3) : ℝ :=
  ∑ j : Fin 3, a x i j * spatialDerivative s x (MetricVolume.coordinateVector j)

def scalarCoefficientPotential (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (s : P × R3 → ℝ) (x : P × R3) : ℝ :=
  coordinateFluxDivergence (fun z => matrixOperatorMap (a (x.1,z))
    (gradient (fun w => s (x.1,w)) z)) x.2

theorem contDiff_coefficientGradientFluxRow
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (s : P × R3 → ℝ)
    (ha : ContDiff ℝ ∞ a) (hs : ContDiff ℝ ∞ s) (i : Fin 3) :
    ContDiff ℝ ∞ (coefficientGradientFluxRow a s i) := by
  apply ContDiff.sum
  intro j _
  exact ((normalResidualMatrixEntryL i j).contDiff.comp ha).mul
    ((contDiff_spatialDerivative s hs).clm_apply contDiff_const)

theorem contDiff_scalarCoefficientPotential
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (s : P × R3 → ℝ)
    (ha : ContDiff ℝ ∞ a) (hs : ContDiff ℝ ∞ s) :
    ContDiff ℝ ∞ (scalarCoefficientPotential a s) := by
  have hRow (p : P) (i : Fin 3) :
      (fun z => matrixOperatorMap (a (p,z)) (gradient (fun w => s (p,w)) z) i) =
        (fun z => coefficientGradientFluxRow a s i (p,z)) := by
    funext z
    simp only [matrixOperator_coordinate, gradient_coordinate,
      coefficientGradientFluxRow, spatialDerivative]
  have hEq : scalarCoefficientPotential a s =
      (fun x => ∑ i : Fin 3, spatialDerivative (coefficientGradientFluxRow a s i) x
        (NormalCoordinatesFrame.coordinateVector i)) := by
    funext x
    unfold scalarCoefficientPotential coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    rw [hRow]
    rfl
  rw [hEq]
  exact ContDiff.sum (fun i _ => (contDiff_spatialDerivative
    (coefficientGradientFluxRow a s i) (contDiff_coefficientGradientFluxRow a s ha hs i)).clm_apply contDiff_const)

def referencePhysicalHalfGauge
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (x : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  Real.exp (L * referenceRescaledDepth g L Φ x.1 x.2 / 2)

theorem contDiff_referenceRescaledDepth_halfGauge_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) :
    ContDiff ℝ ∞ (fun x : (ℝ × (R3 × ℝ)) × R3 => referenceRescaledDepth g L Φ x.1 x.2) := by
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (fun v : (ℝ × (R3 × ℝ)) × R3 =>
      referenceFramedPhysicalEndpoint g L Φ (v.1.1,(v.1.2,v.2))) :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  simpa only [referenceRescaledDepth_eq_physicalEndpoint_depth, Function.comp_def] using
    contDiff_conformalReferenceCoordinateDepth.comp hX

theorem contDiff_referencePhysicalHalfGauge
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) :
    ContDiff ℝ ∞ (referencePhysicalHalfGauge g L Φ) := by
  exact ((contDiff_const.mul (contDiff_referenceRescaledDepth_halfGauge_joint
    g hg L y0 Φ B ε C ρ H a w hData)).div_const 2).exp

theorem referencePhysicalHalfGauge_pos
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (x : (ℝ × (R3 × ℝ)) × R3) :
    0 < referencePhysicalHalfGauge g L Φ x := by exact Real.exp_pos _

theorem referencePhysicalHalfGauge_sq_smul_native
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (x : (ℝ × (R3 × ℝ)) × R3) :
    (referencePhysicalHalfGauge g L Φ x)^2 • a x =
      referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H x := by
  rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
    g L y0 Φ B ε C ρ H a w hData x]
  congr 1
  unfold referencePhysicalHalfGauge
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem referenceNativePrincipalCoefficient_isSymm
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (x : (ℝ × (R3 × ℝ)) × R3) :
    (a x).IsSymm := by
  rcases hData.1 with ⟨_,_,_,_,ha,_,_,hPos,_,_,_,_,_,_,_⟩
  rw [ha, cutoffPrincipalCoefficient]
  exact ((matrixPrincipalCoefficient_posDef H hPos x).isHermitian.isSymm).smul _

theorem contDiff_referencePhysicalHalfGaugePotential
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) :
    ContDiff ℝ ∞ (scalarCoefficientPotential a (referencePhysicalHalfGauge g L Φ)) := by
  exact contDiff_scalarCoefficientPotential a (referencePhysicalHalfGauge g L Φ)
    hData.1.2.2.2.2.2.2.2.2.1
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)

end OAI.AnisotropicCalderon.ConnectionError
