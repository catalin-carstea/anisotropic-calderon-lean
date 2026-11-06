import Calderon.NormalCoefficientInverseNormResidual
import Calderon.SmoothCutoffFixedLpFamily
import Calderon.ActualReferenceSpatialNormalJets

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance normalResidualFirstNormedGroup :
    NormedAddCommGroup (R3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance normalResidualFirstNormedSpace :
    NormedSpace ℝ (R3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ) :=
  ContinuousLinearMap.toNormedSpace
def normalResidualMeasure (R : ℝ) : Measure R3 := volume.restrict (ball (0 : R3) R)

def normalPairInverseCubeProfile (R : ℝ) (k j : Fin 3) : Lp ℝ 2 (normalResidualMeasure R) :=
  (memLp_coordinate_pair_inverse_cube_on_ball R k j).toLp (fun z : R3 => z k*z j/‖z‖^3)

def normalQuadInverseFifthProfile (R : ℝ) (k l i j : Fin 3) : Lp ℝ 2 (normalResidualMeasure R) :=
  (memLp_coordinate_quad_inverse_fifth_on_ball R k l i j).toLp
    (fun z : R3 => z k*z l*z i*z j/‖z‖^5)

def normalResidualMatrixEntryL (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))

def normalResidualUEntry (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (i j k : Fin 3) : P × R3 → ℝ :=
  fun x => (spatialFirstDerivativeRemainderTensor a x
    (NormalCoordinatesFrame.coordinateVector k) (NormalCoordinatesFrame.coordinateVector i)) i j

def normalResidualTEntry (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (i j k l : Fin 3) : P × R3 → ℝ :=
  fun x => (spatialSecondTaylorTensor a x
    (NormalCoordinatesFrame.coordinateVector k) (NormalCoordinatesFrame.coordinateVector l)) i j

def normalCoefficientResidualProfile (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 : ℝ)
    (x : P × R3) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    c0*normalResidualUEntry a i j k x*(x.2 k*x.2 j/‖x.2‖^3)) +
  (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    c0*normalResidualTEntry a i i k l x*(x.2 k*x.2 l/‖x.2‖^3)) -
  (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    (3*c0)*normalResidualTEntry a i j k l x*(x.2 k*x.2 l*x.2 i*x.2 j/‖x.2‖^5))


theorem normalPairInverseCubeProfile_ae (R : ℝ) (k j : Fin 3) :
    normalPairInverseCubeProfile R k j =ᵐ[normalResidualMeasure R]
      (fun z : R3 => z k*z j/‖z‖^3) := by
  exact (memLp_coordinate_pair_inverse_cube_on_ball R k j).coeFn_toLp


theorem normalQuadInverseFifthProfile_ae (R : ℝ) (k l i j : Fin 3) :
    normalQuadInverseFifthProfile R k l i j =ᵐ[normalResidualMeasure R]
      (fun z : R3 => z k*z l*z i*z j/‖z‖^5) := by
  exact (memLp_coordinate_quad_inverse_fifth_on_ball R k l i j).coeFn_toLp


theorem contDiff_normalResidualUEntry
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) (i j k : Fin 3) :
    ContDiff ℝ ∞ (normalResidualUEntry a i j k) := by
  have hSlots : ContDiff ℝ ∞ (fun x => spatialFirstDerivativeRemainderTensor a x
      (NormalCoordinatesFrame.coordinateVector k) (NormalCoordinatesFrame.coordinateVector i)) :=
    ((contDiff_spatialFirstDerivativeRemainderTensor a ha).clm_apply contDiff_const).clm_apply contDiff_const
  exact (normalResidualMatrixEntryL i j).contDiff.comp hSlots


theorem contDiff_normalResidualTEntry
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (normalResidualTEntry a i j k l) := by
  have hSlots : ContDiff ℝ ∞ (fun x => spatialSecondTaylorTensor a x
      (NormalCoordinatesFrame.coordinateVector k) (NormalCoordinatesFrame.coordinateVector l)) :=
    ((contDiff_spatialSecondTaylorTensor a ha).clm_apply contDiff_const).clm_apply contDiff_const
  exact (normalResidualMatrixEntryL i j).contDiff.comp hSlots


def normalResidualUFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k : Fin 3) : P → Lp ℝ 2 (normalResidualMeasure R) :=
  fun p => c0 • cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k j)
    (normalResidualUEntry a i j k) (contDiff_normalResidualUEntry a ha i j k) χ hχ hCompact p

def normalResidualDiagonalFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i k l : Fin 3) : P → Lp ℝ 2 (normalResidualMeasure R) :=
  fun p => c0 • cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k l)
    (normalResidualTEntry a i i k l) (contDiff_normalResidualTEntry a ha i i k l) χ hχ hCompact p

def normalResidualQuadFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k l : Fin 3) : P → Lp ℝ 2 (normalResidualMeasure R) :=
  fun p => (3*c0) • cutoffCoefficientLpFamily (normalResidualMeasure R) (normalQuadInverseFifthProfile R k l i j)
    (normalResidualTEntry a i j k l) (contDiff_normalResidualTEntry a ha i j k l) χ hχ hCompact p

def normalCoefficientResidualLpFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) : P → Lp ℝ 2 (normalResidualMeasure R) :=
  fun p => (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, normalResidualUFamily a ha χ hχ hCompact c0 R i j k p) +
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, normalResidualDiagonalFamily a ha χ hχ hCompact c0 R i k l p) -
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, normalResidualQuadFamily a ha χ hχ hCompact c0 R i j k l p)


theorem contDiff_normalResidualUFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k : Fin 3) :
    ContDiff ℝ ∞ (normalResidualUFamily a ha χ hχ hCompact c0 R i j k) := by
  exact (contDiff_cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k j)
    (normalResidualUEntry a i j k) (contDiff_normalResidualUEntry a ha i j k) χ hχ hCompact).const_smul c0


theorem contDiff_normalResidualDiagonalFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i k l : Fin 3) :
    ContDiff ℝ ∞ (normalResidualDiagonalFamily a ha χ hχ hCompact c0 R i k l) := by
  exact (contDiff_cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k l)
    (normalResidualTEntry a i i k l) (contDiff_normalResidualTEntry a ha i i k l) χ hχ hCompact).const_smul c0


theorem contDiff_normalResidualQuadFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (normalResidualQuadFamily a ha χ hχ hCompact c0 R i j k l) := by
  exact (contDiff_cutoffCoefficientLpFamily (normalResidualMeasure R) (normalQuadInverseFifthProfile R k l i j)
    (normalResidualTEntry a i j k l) (contDiff_normalResidualTEntry a ha i j k l) χ hχ hCompact).const_smul (3*c0)


theorem contDiff_normalCoefficientResidualLpFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    ContDiff ℝ ∞ (normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R) := by
  exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
      contDiff_normalResidualUFamily a ha χ hχ hCompact c0 R i j k).add
    (ContDiff.sum fun i _ => ContDiff.sum fun k _ => ContDiff.sum fun l _ =>
      contDiff_normalResidualDiagonalFamily a ha χ hχ hCompact c0 R i k l)).sub
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ => ContDiff.sum fun l _ =>
      contDiff_normalResidualQuadFamily a ha χ hχ hCompact c0 R i j k l)


private theorem normalResidual_lp_sum_ae {ι : Type} [Fintype ι]
    (μ : Measure R3) (F : ι → Lp ℝ 2 μ) (g : ι → R3 → ℝ)
    (hAE : ∀ i, F i =ᵐ[μ] g i) :
    (∑ i, F i) =ᵐ[μ] (fun z => ∑ i, g i z) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ F, ae_all_iff.mpr hAE] with z hSum hAll
  rw [hSum]
  exact Finset.sum_congr rfl (fun i _ => hAll i)


private theorem normalResidualUFamily_ae
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k : Fin 3) (p : P) :
    normalResidualUFamily a ha χ hχ hCompact c0 R i j k p =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (c0) * normalResidualUEntry a i j k (p,z) * (z k*z j/‖z‖^3)) := by
  let A : P → Lp ℝ 2 (normalResidualMeasure R) :=
    cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k j)
      (normalResidualUEntry a i j k) (contDiff_normalResidualUEntry a ha i j k) χ hχ hCompact
  have hCoeff := cutoffCoefficientLpFamily_ae (normalResidualMeasure R) (normalPairInverseCubeProfile R k j)
    (normalResidualUEntry a i j k) (contDiff_normalResidualUEntry a ha i j k) χ hχ hCompact p
  filter_upwards [Lp.coeFn_smul (c0) (A p), hCoeff, normalPairInverseCubeProfile_ae R k j] with z hS hC hP
  change ((c0) • A p) z = _
  simp only [Pi.smul_apply, smul_eq_mul] at hS
  rw [hS,hC,hP]
  ring


private theorem normalResidualDiagonalFamily_ae
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i k l : Fin 3) (p : P) :
    normalResidualDiagonalFamily a ha χ hχ hCompact c0 R i k l p =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (c0) * normalResidualTEntry a i i k l (p,z) * (z k*z l/‖z‖^3)) := by
  let A : P → Lp ℝ 2 (normalResidualMeasure R) :=
    cutoffCoefficientLpFamily (normalResidualMeasure R) (normalPairInverseCubeProfile R k l)
      (normalResidualTEntry a i i k l) (contDiff_normalResidualTEntry a ha i i k l) χ hχ hCompact
  have hCoeff := cutoffCoefficientLpFamily_ae (normalResidualMeasure R) (normalPairInverseCubeProfile R k l)
    (normalResidualTEntry a i i k l) (contDiff_normalResidualTEntry a ha i i k l) χ hχ hCompact p
  filter_upwards [Lp.coeFn_smul (c0) (A p), hCoeff, normalPairInverseCubeProfile_ae R k l] with z hS hC hP
  change ((c0) • A p) z = _
  simp only [Pi.smul_apply, smul_eq_mul] at hS
  rw [hS,hC,hP]
  ring


private theorem normalResidualQuadFamily_ae
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (i j k l : Fin 3) (p : P) :
    normalResidualQuadFamily a ha χ hχ hCompact c0 R i j k l p =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (3*c0) * normalResidualTEntry a i j k l (p,z) * (z k*z l*z i*z j/‖z‖^5)) := by
  let A : P → Lp ℝ 2 (normalResidualMeasure R) :=
    cutoffCoefficientLpFamily (normalResidualMeasure R) (normalQuadInverseFifthProfile R k l i j)
      (normalResidualTEntry a i j k l) (contDiff_normalResidualTEntry a ha i j k l) χ hχ hCompact
  have hCoeff := cutoffCoefficientLpFamily_ae (normalResidualMeasure R) (normalQuadInverseFifthProfile R k l i j)
    (normalResidualTEntry a i j k l) (contDiff_normalResidualTEntry a ha i j k l) χ hχ hCompact p
  filter_upwards [Lp.coeFn_smul (3*c0) (A p), hCoeff, normalQuadInverseFifthProfile_ae R k l i j] with z hS hC hP
  change ((3*c0) • A p) z = _
  simp only [Pi.smul_apply, smul_eq_mul] at hS
  rw [hS,hC,hP]
  ring


theorem normalCoefficientResidualLpFamily_ae_profile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (p : P) :
    normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p =ᵐ[normalResidualMeasure R]
      (fun z => χ z * normalCoefficientResidualProfile a c0 (p,z)) := by
  let A : Lp ℝ 2 (normalResidualMeasure R) :=
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, normalResidualUFamily a ha χ hχ hCompact c0 R i j k p
  let B : Lp ℝ 2 (normalResidualMeasure R) :=
    ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, normalResidualDiagonalFamily a ha χ hχ hCompact c0 R i k l p
  let C : Lp ℝ 2 (normalResidualMeasure R) :=
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, normalResidualQuadFamily a ha χ hχ hCompact c0 R i j k l p
  have hA : A =ᵐ[normalResidualMeasure R] (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      χ z*c0*normalResidualUEntry a i j k (p,z)*(z k*z j/‖z‖^3)) := by
    apply normalResidual_lp_sum_ae
    intro i
    apply normalResidual_lp_sum_ae
    intro j
    apply normalResidual_lp_sum_ae
    intro k
    exact normalResidualUFamily_ae a ha χ hχ hCompact c0 R i j k p
  have hB : B =ᵐ[normalResidualMeasure R] (fun z => ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      χ z*c0*normalResidualTEntry a i i k l (p,z)*(z k*z l/‖z‖^3)) := by
    apply normalResidual_lp_sum_ae
    intro i
    apply normalResidual_lp_sum_ae
    intro k
    apply normalResidual_lp_sum_ae
    intro l
    exact normalResidualDiagonalFamily_ae a ha χ hχ hCompact c0 R i k l p
  have hC : C =ᵐ[normalResidualMeasure R] (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      χ z*(3*c0)*normalResidualTEntry a i j k l (p,z)*(z k*z l*z i*z j/‖z‖^5)) := by
    apply normalResidual_lp_sum_ae
    intro i
    apply normalResidual_lp_sum_ae
    intro j
    apply normalResidual_lp_sum_ae
    intro k
    apply normalResidual_lp_sum_ae
    intro l
    exact normalResidualQuadFamily_ae a ha χ hχ hCompact c0 R i j k l p
  filter_upwards [Lp.coeFn_sub (A+B) C, Lp.coeFn_add A B, hA,hB,hC] with z hSub hAdd hAz hBz hCz
  change (A+B-C) z = _
  rw [hSub]
  change (A+B) z - C z = _
  rw [hAdd]
  change A z + B z - C z = _
  rw [hAz,hBz,hCz]
  simp only [normalCoefficientResidualProfile, mul_add, mul_sub, Finset.mul_sum, mul_assoc]


theorem exists_compact_uniform_normalCoefficientResidualLpFamily_bound
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ K,
      ‖normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p‖ ≤ C := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (contDiff_normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R).continuous.continuousOn
  exact ⟨max B 1, le_max_right _ _, fun p hp => (hB p hp).trans (le_max_left _ _)⟩


theorem normalCoefficientResidualLpFamily_ae_divergence_of_normal_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (p : P) (h0 : a (p,0) = 1)
    (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) :
    normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (-coordinateFluxDivergence
        (fun x => matrixOperatorMap (a (p,x)) (gradient (inverseNormPotential c0) x)) z)) := by
  have hNe : ∀ᵐ z ∂normalResidualMeasure R, z ≠ (0 : R3) :=
    ae_restrict_of_ae (volume.ae_ne (0 : R3))
  filter_upwards [normalCoefficientResidualLpFamily_ae_profile a ha χ hχ hCompact c0 R p,
    hNe] with z hF hz
  rw [hF]
  have h := coordinateFluxDivergence_inverseNormPotential_of_normal_coefficient_jets a ha p h0 h1 c0 z hz
  change -coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient (inverseNormPotential c0) x)) z =
      normalCoefficientResidualProfile a c0 (p,z) at h
  rw [h]



def actualReferenceNativeResidualLpFamily
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) : (ℝ × (R3 × ℝ)) → Lp ℝ 2 (normalResidualMeasure R) :=
  normalCoefficientResidualLpFamily a hData.1.2.2.2.2.2.2.2.2.1 χ hχ hCompact c0 R

def actualReferenceRawResidualLpFamily
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) : (ℝ × (R3 × ℝ)) → Lp ℝ 2 (normalResidualMeasure R) :=
  normalCoefficientResidualLpFamily (matrixPrincipalCoefficient H)
    (contDiff_matrixPrincipalCoefficient H hData.1.2.2.2.2.2.2.1 hData.1.2.2.2.2.2.2.2.1)
    χ hχ hCompact c0 R


theorem contDiff_actualReferenceNativeResidualLpFamily
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    ContDiff ℝ ∞ (actualReferenceNativeResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R) := by
  exact contDiff_normalCoefficientResidualLpFamily (a) (hData.1.2.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R


theorem exists_compact_uniform_actualReferenceNativeResidualLpFamily_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ K, ‖actualReferenceNativeResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R p‖ ≤ D := by
  exact exists_compact_uniform_normalCoefficientResidualLpFamily_bound
    (a) (hData.1.2.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R K hK


theorem actualReferenceNativeResidualLpFamily_ae_divergence
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (hg : IsAdmissibleMetric g)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    actualReferenceNativeResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R (q,(y,r)) =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (-coordinateFluxDivergence
        (fun x => matrixOperatorMap (a ((q,(y,r)),x))
          (gradient (inverseNormPotential c0) x)) z)) := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact normalCoefficientResidualLpFamily_ae_divergence_of_normal_jets
    (a) (hData.1.2.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R (q,(y,r)) hJet.1 hJet.2.fderiv


theorem contDiff_actualReferenceRawResidualLpFamily
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    ContDiff ℝ ∞ (actualReferenceRawResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R) := by
  exact contDiff_normalCoefficientResidualLpFamily (matrixPrincipalCoefficient H) (contDiff_matrixPrincipalCoefficient H hData.1.2.2.2.2.2.2.1 hData.1.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R


theorem exists_compact_uniform_actualReferenceRawResidualLpFamily_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ K, ‖actualReferenceRawResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R p‖ ≤ D := by
  exact exists_compact_uniform_normalCoefficientResidualLpFamily_bound
    (matrixPrincipalCoefficient H) (contDiff_matrixPrincipalCoefficient H hData.1.2.2.2.2.2.2.1 hData.1.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R K hK


theorem actualReferenceRawResidualLpFamily_ae_divergence
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (hg : IsAdmissibleMetric g)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    actualReferenceRawResidualLpFamily g L y0 Φ B ε C ρ H a w hData χ hχ hCompact c0 R (q,(y,r)) =ᵐ[normalResidualMeasure R]
      (fun z => χ z * (-coordinateFluxDivergence
        (fun x => matrixOperatorMap (matrixPrincipalCoefficient H ((q,(y,r)),x))
          (gradient (inverseNormPotential c0) x)) z)) := by
  have hJet := referenceNormalPrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact normalCoefficientResidualLpFamily_ae_divergence_of_normal_jets
    (matrixPrincipalCoefficient H) (contDiff_matrixPrincipalCoefficient H hData.1.2.2.2.2.2.2.1 hData.1.2.2.2.2.2.2.2.1) χ hχ hCompact c0 R (q,(y,r)) hJet.1 hJet.2.fderiv

end OAI.AnisotropicCalderon.ConnectionError
