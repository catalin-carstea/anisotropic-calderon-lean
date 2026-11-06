import Calderon.ActualReferenceHalfGaugeCalculus
import Calderon.BoundedContinuousMulLpBilinear
import Calderon.ActualScalarGaugeDivergence
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


def halfGaugeResidualRatio (s : P × R3 → ℝ) (x : P × R3) : ℝ :=
  s x / s (x.1,0)

def halfGaugePotentialRatio (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (s : P × R3 → ℝ) (x : P × R3) : ℝ :=
  scalarCoefficientPotential a s x / s (x.1,0)

def normalizedHalfGaugePotential (s : P × R3 → ℝ) (c0 : ℝ) (p : P) (z : R3) : ℝ :=
  inverseNormPotential c0 z / (s (p,0) * s (p,z))

def normalInverseNormProfile (c0 R : ℝ) : Lp ℝ 2 (normalResidualMeasure R) :=
  c0 • (memLp_inverse_norm_on_ball R).toLp (fun z : R3 => 1 / ‖z‖)

theorem contDiff_halfGaugeResidualRatio
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0) :
    ContDiff ℝ ∞ (halfGaugeResidualRatio s) := by
  exact hs.div (hs.comp (contDiff_fst.prodMk contDiff_const)) (fun x => hne (x.1,0))

theorem contDiff_halfGaugePotentialRatio
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0) :
    ContDiff ℝ ∞ (halfGaugePotentialRatio a s) := by
  exact (contDiff_scalarCoefficientPotential a s ha hs).div
    (hs.comp (contDiff_fst.prodMk contDiff_const)) (fun x => hne (x.1,0))

theorem normalInverseNormProfile_ae (c0 R : ℝ) :
    normalInverseNormProfile c0 R =ᵐ[normalResidualMeasure R] inverseNormPotential c0 := by
  let f : Lp ℝ 2 (normalResidualMeasure R) :=
    (memLp_inverse_norm_on_ball R).toLp (fun z : R3 => 1 / ‖z‖)
  filter_upwards [Lp.coeFn_smul c0 f, (memLp_inverse_norm_on_ball R).coeFn_toLp] with z hS hF
  change (c0 • f) z = _
  simp only [Pi.smul_apply, smul_eq_mul] at hS
  change f z = 1 / ‖z‖ at hF
  rw [hS,hF]
  unfold inverseNormPotential
  ring

theorem normalCoefficientResidualProfile_eq_mul_one
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (c0 : ℝ) (x : P × R3) :
    normalCoefficientResidualProfile a c0 x = c0 * normalCoefficientResidualProfile a 1 x := by
  simp only [normalCoefficientResidualProfile, one_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem coordinateFluxDivergence_halfGauge_of_normal_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (hSym : ∀ x, (a x).IsSymm) (p : P) (h0 : a (p,0) = 1)
    (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    -coordinateFluxDivergence (fun x => matrixOperatorMap ((s (p,x))^2 • a (p,x))
      (gradient (normalizedHalfGaugePotential s c0 p) x)) z =
      halfGaugeResidualRatio s (p,z) * normalCoefficientResidualProfile a c0 (p,z) +
        (inverseNormPotential c0 z / s (p,0)) * scalarCoefficientPotential a s (p,z) := by
  have hsSlice : ContDiff ℝ ∞ (fun w : R3 => s (p,w)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  have haEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun w : R3 => a (p,w) i j) :=
    ((normalResidualMatrixEntryL i j).contDiff.comp ha).comp (contDiff_const.prodMk contDiff_id)
  have hQ : (fun w => inverseNormPotential (c0 / s (p,0)) w / s (p,w)) =
      normalizedHalfGaugePotential s c0 p := by
    funext w
    unfold normalizedHalfGaugePotential inverseNormPotential
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hGauge := coordinateFluxDivergence_scalar_gauge ({0}ᶜ : Set R3)
    isOpen_compl_singleton (fun w => a (p,w)) (inverseNormPotential (c0 / s (p,0)))
    (fun w => s (p,w)) (fun i j => (haEntry i j).contDiffOn)
    (fun w _ i j => (hSym (p,w)).apply j i)
    (contDiffOn_inverseNormPotential (c0 / s (p,0))) hsSlice.contDiffOn
    (fun w _ => hne (p,w)) z (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)
  rw [hQ] at hGauge
  have hPrincipal := coordinateFluxDivergence_inverseNormPotential_of_normal_coefficient_jets
    a ha p h0 h1 (c0 / s (p,0)) z hz
  change -coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient (inverseNormPotential (c0 / s (p,0))) x)) z =
      normalCoefficientResidualProfile a (c0 / s (p,0)) (p,z) at hPrincipal
  have hPrincipal' : coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient (inverseNormPotential (c0 / s (p,0))) x)) z =
      -normalCoefficientResidualProfile a (c0 / s (p,0)) (p,z) := neg_eq_iff_eq_neg.mp hPrincipal
  have hN : normalCoefficientResidualProfile a (c0 / s (p,0)) (p,z) =
      normalCoefficientResidualProfile a c0 (p,z) / s (p,0) := by
    rw [normalCoefficientResidualProfile_eq_mul_one a (c0 / s (p,0)),
      normalCoefficientResidualProfile_eq_mul_one a c0]
    ring
  have hGamma : inverseNormPotential (c0 / s (p,0)) z = inverseNormPotential c0 z / s (p,0) := by
    unfold inverseNormPotential
    ring
  rw [hPrincipal',hN,hGamma] at hGauge
  exact hGauge.trans (by dsimp only [halfGaugeResidualRatio, scalarCoefficientPotential]; ring)

def halfGaugedNormalResidualLpFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) : P → Lp ℝ 2 (normalResidualMeasure R) :=
  fun p => boundedContinuousMulLpBilin (normalResidualMeasure R)
    (cutoffCoefficientBCF (halfGaugeResidualRatio s) (contDiff_halfGaugeResidualRatio s hs hne)
      χ hχ hCompact p)
    (normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p) +
    cutoffCoefficientLpFamily (normalResidualMeasure R) (normalInverseNormProfile c0 R)
      (halfGaugePotentialRatio a s) (contDiff_halfGaugePotentialRatio a ha s hs hne)
      χ hχ hCompact p

theorem contDiff_halfGaugedNormalResidualLpFamily
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    ContDiff ℝ ∞ (halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R) := by
  exact (contDiff_boundedContinuousMulLpBilin_comp (normalResidualMeasure R)
    (cutoffCoefficientBCF (halfGaugeResidualRatio s) (contDiff_halfGaugeResidualRatio s hs hne)
      χ hχ hCompact) (normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R)
    (contDiff_cutoffCoefficientBCF (halfGaugeResidualRatio s) (contDiff_halfGaugeResidualRatio s hs hne)
      χ hχ hCompact) (contDiff_normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R)).add
    (contDiff_cutoffCoefficientLpFamily (normalResidualMeasure R) (normalInverseNormProfile c0 R)
      (halfGaugePotentialRatio a s) (contDiff_halfGaugePotentialRatio a ha s hs hne) χ hχ hCompact)

theorem exists_compact_uniform_halfGaugedNormalResidualLpFamily_bound
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (K : Set P) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ K,
      ‖halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R p‖ ≤ D := by
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (contDiff_halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R).continuous.continuousOn
  exact ⟨max D 1, le_max_right _ _, fun p hp => (hD p hp).trans (le_max_left _ _)⟩

theorem halfGaugedNormalResidualLpFamily_ae_principal_family
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ)
    (hOne : ∀ z ∈ ball (0 : R3) R, χ z = 1) (p : P) :
    halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R p =ᵐ[normalResidualMeasure R]
      (fun z => (s (p,z) / s (p,0)) * normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p z +
        (inverseNormPotential c0 z / s (p,0)) * scalarCoefficientPotential a s (p,z)) := by
  let A : Lp ℝ 2 (normalResidualMeasure R) :=
    boundedContinuousMulLpBilin (normalResidualMeasure R)
      (cutoffCoefficientBCF (halfGaugeResidualRatio s) (contDiff_halfGaugeResidualRatio s hs hne) χ hχ hCompact p)
      (normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p)
  let V : Lp ℝ 2 (normalResidualMeasure R) :=
    cutoffCoefficientLpFamily (normalResidualMeasure R) (normalInverseNormProfile c0 R)
      (halfGaugePotentialRatio a s) (contDiff_halfGaugePotentialRatio a ha s hs hne) χ hχ hCompact p
  have hA := boundedContinuousMulLpBilin_apply_ae (normalResidualMeasure R)
    (cutoffCoefficientBCF (halfGaugeResidualRatio s) (contDiff_halfGaugeResidualRatio s hs hne) χ hχ hCompact p)
    (normalCoefficientResidualLpFamily a ha χ hχ hCompact c0 R p)
  have hV := cutoffCoefficientLpFamily_ae (normalResidualMeasure R) (normalInverseNormProfile c0 R)
    (halfGaugePotentialRatio a s) (contDiff_halfGaugePotentialRatio a ha s hs hne) χ hχ hCompact p
  have hMem : ∀ᵐ z ∂normalResidualMeasure R, z ∈ ball (0 : R3) R := ae_restrict_mem measurableSet_ball
  filter_upwards [Lp.coeFn_add A V,hA,hV,normalInverseNormProfile_ae c0 R,hMem] with z hS hAz hVz hG hz
  change (A+V) z = _
  simp only [Pi.add_apply] at hS
  rw [hS,hAz,hVz,hG]
  simp only [cutoffCoefficientBCF_apply, hOne z hz, one_mul, halfGaugeResidualRatio, halfGaugePotentialRatio]
  ring

theorem halfGaugedNormalResidualLpFamily_ae_profile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ)
    (hOne : ∀ z ∈ ball (0 : R3) R, χ z = 1) (p : P) :
    halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R p =ᵐ[normalResidualMeasure R]
      (fun z => halfGaugeResidualRatio s (p,z) * normalCoefficientResidualProfile a c0 (p,z) +
        (inverseNormPotential c0 z / s (p,0)) * scalarCoefficientPotential a s (p,z)) := by
  have hMem : ∀ᵐ z ∂normalResidualMeasure R, z ∈ ball (0 : R3) R := ae_restrict_mem measurableSet_ball
  filter_upwards [halfGaugedNormalResidualLpFamily_ae_principal_family a ha s hs hne χ hχ hCompact c0 R hOne p,
    normalCoefficientResidualLpFamily_ae_profile a ha χ hχ hCompact c0 R p,hMem] with z hF hA hz
  rw [hF,hA,hOne z hz,one_mul]
  rfl

theorem halfGaugedNormalResidualLpFamily_ae_divergence_of_normal_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ)
    (hOne : ∀ z ∈ ball (0 : R3) R, χ z = 1) (hSym : ∀ x, (a x).IsSymm)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0) :
    halfGaugedNormalResidualLpFamily a ha s hs hne χ hχ hCompact c0 R p =ᵐ[normalResidualMeasure R]
      (fun z => -coordinateFluxDivergence (fun x => matrixOperatorMap ((s (p,x))^2 • a (p,x))
        (gradient (normalizedHalfGaugePotential s c0 p) x)) z) := by
  have hNe : ∀ᵐ z ∂normalResidualMeasure R, z ≠ (0 : R3) :=
    ae_restrict_of_ae (volume.ae_ne (0 : R3))
  filter_upwards [halfGaugedNormalResidualLpFamily_ae_profile a ha s hs hne χ hχ hCompact c0 R hOne p,hNe]
    with z hF hz
  rw [hF]
  exact (coordinateFluxDivergence_halfGauge_of_normal_jets a ha s hs hne hSym p h0 h1 c0 z hz).symm

def actualReferenceHalfGaugedResidualLpFamily
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    (ℝ × (R3 × ℝ)) → Lp ℝ 2 (normalResidualMeasure R) :=
  halfGaugedNormalResidualLpFamily a hData.1.2.2.2.2.2.2.2.2.1
    (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') χ hχ hCompact c0 R

theorem contDiff_actualReferenceHalfGaugedResidualLpFamily
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) :
    ContDiff ℝ ∞ (actualReferenceHalfGaugedResidualLpFamily g hg L y0 Φ B ε C ρ H a w hData
      χ hχ hCompact c0 R) := by
  exact contDiff_halfGaugedNormalResidualLpFamily a hData.1.2.2.2.2.2.2.2.2.1
    (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') χ hχ hCompact c0 R

theorem exists_compact_uniform_actualReferenceHalfGaugedResidualLpFamily_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ K,
      ‖actualReferenceHalfGaugedResidualLpFamily g hg L y0 Φ B ε C ρ H a w hData
        χ hχ hCompact c0 R p‖ ≤ D := by
  exact exists_compact_uniform_halfGaugedNormalResidualLpFamily_bound a hData.1.2.2.2.2.2.2.2.2.1
    (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') χ hχ hCompact c0 R K hK

theorem actualReferenceHalfGaugedResidualLpFamily_ae_divergence
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ) (c0 R : ℝ)
    (hOne : ∀ z ∈ ball (0 : R3) R, χ z = 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    actualReferenceHalfGaugedResidualLpFamily g hg L y0 Φ B ε C ρ H a w hData
      χ hχ hCompact c0 R (q,(y,r)) =ᵐ[normalResidualMeasure R]
      (fun z => -coordinateFluxDivergence
        (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
          (gradient (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) c0 (q,(y,r))) x)) z) := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  have hAE := halfGaugedNormalResidualLpFamily_ae_divergence_of_normal_jets
    a hData.1.2.2.2.2.2.2.2.2.1 (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') χ hχ hCompact c0 R hOne
    (referenceNativePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData)
    (q,(y,r)) hJet.1 hJet.2.fderiv
  have hFlux : (fun x => matrixOperatorMap
      ((referencePhysicalHalfGauge g L Φ ((q,(y,r)),x))^2 • a ((q,(y,r)),x))
      (gradient (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) c0 (q,(y,r))) x)) =
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
        (gradient (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) c0 (q,(y,r))) x)) := by
    funext x
    rw [referencePhysicalHalfGauge_sq_smul_native g L y0 Φ B ε C ρ H a w hData]
  simpa only [actualReferenceHalfGaugedResidualLpFamily,hFlux] using hAE

end OAI.AnisotropicCalderon.ConnectionError
