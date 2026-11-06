import Calderon.ActualFiniteGaugePhysicalDensityBaseL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual finite-input weak squared norm only; no strong PdagP domain. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ReferenceDensityBounds

lemma integrable_weighted_norm_sq_of_continuous_compact
    {E : Type*} [NormedAddCommGroup E]
    (mu : R3 → ℝ) (hmu : Continuous mu)
    (f : R3 → E) (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable (fun y => mu y * ‖f y‖^2) (volume : Measure R3) := by
  have hn : Continuous (fun y => ‖f y‖^2) := hf.norm.pow 2
  have hcn : HasCompactSupport (fun y => ‖f y‖^2) :=
    hcf.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun z : E => ‖z‖^2) (by simp) f)
  have hcp : HasCompactSupport (fun y => mu y * ‖f y‖^2) := hcn.mul_left
  exact (hmu.mul hn).integrable_of_hasCompactSupport hcp

lemma sphereL2_eq_of_negative_inclusion_eq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f v : SphereL2)
    (h : sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD f) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD v)) : f = v := by
  exact (sphereSobolevZeroEquiv hO hD).injective
    (sphereSobolevInclusionL_injective 0 (-(1/2 : ℝ)) (by norm_num) h)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

theorem exists_reference_commonRadius_finitePhysicalDensityOperator_weakSquaredNorm
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
        ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
        (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < δ ∧ R y ≠ 0) →
        ∃ f : R3 → SphereL2, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
          MemLp f 2 (volume : Measure R3) ∧
          Integrable (fun y => referenceDensityFamily g L (q,y) * ‖f y‖^2) ∧
          0 ≤ (∫ y : R3, referenceDensityFamily g L (q,y) * ‖f y‖^2) ∧
          ∀ y : R3,
            sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y)) =
              referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
                (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y := by
  obtain ⟨d,hd,hdρ,hDomain⟩ :=
    exists_reference_commonRadius_finitePhysicalDensityOperator_baseL2_of_gauge
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg hKernel
  refine ⟨d,hd,hdρ,?_⟩
  intro n q hq R hR u hu hcu hRoom
  obtain ⟨f,hf,hcf,hMem,hGraph⟩ := hDomain n q hq R hR u hu hcu hRoom
  have hmu : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    ((contDiff_referenceDensityFamily g hg L).comp
      (contDiff_const.prodMk contDiff_id)).continuous
  have hInt : Integrable (fun y : R3 => referenceDensityFamily g L (q,y) * ‖f y‖^2) :=
    integrable_weighted_norm_sq_of_continuous_compact _ hmu f hf.continuous hcf
  have hNonneg : 0 ≤ (∫ y : R3, referenceDensityFamily g L (q,y) * ‖f y‖^2) :=
    integral_nonneg (fun y =>
      mul_nonneg (referenceDensityFamily_pos g hg L (q,y)).le (sq_nonneg ‖f y‖))
  exact ⟨f,hf,hcf,hMem,hInt,hNonneg,hGraph⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
