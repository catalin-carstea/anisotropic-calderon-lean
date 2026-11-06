import Calderon.NormalCoefficientWeakPoleIdentity
import Calderon.HalfGaugedNormalResidualLpFamily
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily.DriftBootstrap NativePolynomialBulkMoments
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem integral_normalizedHalfGaugePotential_principal_of_normal_jets
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (p : P) (h0 : a (p,0) = 1) (h1 : fderiv ℝ (fun z : R3 => a (p,z)) 0 = 0)
    (hSym : ∀ z : R3, (a (p,z)).IsSymm)
    (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hCompact : HasCompactSupport φ) :
    (∫ z : R3, normalizedHalfGaugePotential s sphereSurfaceMass⁻¹ p z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap ((s (p,x))^2 • a (p,x)) (gradient φ x)) z)) =
      φ 0 + ∫ z : R3,
        (halfGaugeResidualRatio s (p,z) * normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z) +
          (inverseNormPotential sphereSurfaceMass⁻¹ z / s (p,0)) * scalarCoefficientPotential a s (p,z)) * φ z := by
  let G : R3 → ℝ := fun z => s (p,z) * φ z
  let V : R3 → ℝ := fun z => scalarCoefficientPotential a s (p,z)
  let Γ : R3 → ℝ := inverseNormPotential sphereSurfaceMass⁻¹
  let F : R3 → ℝ := fun z => normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z)
  let D : R3 → ℝ := fun z => -coordinateFluxDivergence
    (fun x => matrixOperatorMap (a (p,x)) (gradient G x)) z
  have hsSlice : ContDiff ℝ ∞ (fun z : R3 => s (p,z)) := hs.comp (contDiff_const.prodMk contDiff_id)
  have haEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun z : R3 => a (p,z) i j) :=
    ((normalResidualMatrixEntryL i j).contDiff.comp ha).comp (contDiff_const.prodMk contDiff_id)
  have hG : ContDiff ℝ ∞ G := hsSlice.mul hφ
  have hGc : HasCompactSupport G := hCompact.mul_left
  have hV : ContDiff ℝ ∞ V := (contDiff_scalarCoefficientPotential a s ha hs).comp
    (contDiff_const.prodMk contDiff_id)
  have hD : ContDiff ℝ ∞ D := contDiff_neg_coordinateFluxDivergence_matrixGradient
    (fun z => a (p,z)) haEntry G hG
  have hDc : HasCompactSupport D := hasCompactSupport_neg_coordinateFluxDivergence_matrixGradient
    (fun z => a (p,z)) G hGc
  have hIntD : Integrable (fun z : R3 => Γ z * D z) :=
    integrable_inverseNormPotential_mul_continuous_compact sphereSurfaceMass⁻¹ D hD.continuous hDc
  have hIntV : Integrable (fun z : R3 => Γ z * (φ z * V z)) :=
    integrable_inverseNormPotential_mul_continuous_compact sphereSurfaceMass⁻¹
      (fun z => φ z * V z) (hφ.continuous.mul hV.continuous) hCompact.mul_right
  have hIntF : Integrable (fun z : R3 => F z * G z) :=
    integrable_normalCoefficientResidualProfile_mul_compact a ha sphereSurfaceMass⁻¹ p G hG.continuous hGc
  have hQuotient : (fun z => G z / s (p,z)) = φ := by
    funext z
    dsimp only [G]
    field_simp [hne (p,z)]
  have hGauge (z : R3) := coordinateFluxDivergence_scalar_gauge Set.univ isOpen_univ
    (fun x => a (p,x)) G (fun x => s (p,x))
    (fun i j => (haEntry i j).contDiffOn)
    (fun x _ i j => (hSym x).apply j i) hG.contDiffOn hsSlice.contDiffOn
    (fun x _ => hne (p,x)) z (Set.mem_univ z)
  simp only [hQuotient] at hGauge
  have hPoint (z : R3) : normalizedHalfGaugePotential s sphereSurfaceMass⁻¹ p z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap ((s (p,x))^2 • a (p,x)) (gradient φ x)) z) =
      (s (p,0))⁻¹ * (Γ z * D z) + (s (p,0))⁻¹ * (Γ z * (φ z * V z)) := by
    rw [hGauge z]
    dsimp only [normalizedHalfGaugePotential,Γ,D,G,V,scalarCoefficientPotential]
    field_simp [hne (p,0),hne (p,z)]
  have hLeft : (∫ z : R3, normalizedHalfGaugePotential s sphereSurfaceMass⁻¹ p z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap ((s (p,x))^2 • a (p,x)) (gradient φ x)) z)) =
      (s (p,0))⁻¹ * (∫ z : R3, Γ z * D z) +
        (s (p,0))⁻¹ * (∫ z : R3, Γ z * (φ z * V z)) := by
    calc
      _ = ∫ z : R3, (s (p,0))⁻¹ * (Γ z * D z) + (s (p,0))⁻¹ * (Γ z * (φ z * V z)) :=
        integral_congr_ae (Filter.Eventually.of_forall hPoint)
      _ = _ := by rw [integral_add (hIntD.const_mul _) (hIntV.const_mul _),integral_const_mul,integral_const_mul]
  have hResidual : (∫ z : R3,
      (halfGaugeResidualRatio s (p,z) * normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z) +
        (inverseNormPotential sphereSurfaceMass⁻¹ z / s (p,0)) * scalarCoefficientPotential a s (p,z)) * φ z) =
      (s (p,0))⁻¹ * (∫ z : R3, F z * G z) +
        (s (p,0))⁻¹ * (∫ z : R3, Γ z * (φ z * V z)) := by
    calc
      _ = ∫ z : R3, (s (p,0))⁻¹ * (F z * G z) + (s (p,0))⁻¹ * (Γ z * (φ z * V z)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp only [halfGaugeResidualRatio,F,G,Γ,V]
          ring
      _ = _ := by rw [integral_add (hIntF.const_mul _) (hIntV.const_mul _),integral_const_mul,integral_const_mul]
  have hWeak : (∫ z : R3, Γ z * D z) = G 0 + ∫ z : R3, F z * G z :=
    integral_inverseNormPotential_principal_of_normal_jets a ha p h0 h1 hSym G hG hGc
  rw [hLeft,hResidual,hWeak]
  have hPole : (s (p,0))⁻¹ * G 0 = φ 0 := by
    dsimp only [G]
    field_simp [hne (p,0)]
  rw [mul_add,hPole]
  ring

theorem integral_referenceNativeInverseNormPotential_principal
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ)
    (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hCompact : HasCompactSupport φ) :
    (∫ z : R3, inverseNormPotential sphereSurfaceMass⁻¹ z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap (a ((q,(y,r)),x)) (gradient φ x)) z)) =
      φ 0 + ∫ z : R3, normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ ((q,(y,r)),z) * φ z := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  exact integral_inverseNormPotential_principal_of_normal_jets
    a hData.1.2.2.2.2.2.2.2.2.1 (q,(y,r)) hJet.1 hJet.2.fderiv
    (fun z => referenceNativePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData ((q,(y,r)),z))
    φ hφ hCompact

theorem integral_referenceNormalizedHalfGaugePotential_principal
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ)
    (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hCompact : HasCompactSupport φ) :
    (∫ z : R3, normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r)) z *
      (-coordinateFluxDivergence
        (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
          (gradient φ x)) z)) =
      φ 0 + ∫ z : R3,
        (halfGaugeResidualRatio (referencePhysicalHalfGauge g L Φ) ((q,(y,r)),z) *
            normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ ((q,(y,r)),z) +
          (inverseNormPotential sphereSurfaceMass⁻¹ z / referencePhysicalHalfGauge g L Φ ((q,(y,r)),0)) *
            scalarCoefficientPotential a (referencePhysicalHalfGauge g L Φ) ((q,(y,r)),z)) * φ z := by
  have hJet := referenceNativePrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  have hWeak := integral_normalizedHalfGaugePotential_principal_of_normal_jets
    a hData.1.2.2.2.2.2.2.2.2.1 (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne')
    (q,(y,r)) hJet.1 hJet.2.fderiv
    (fun z => referenceNativePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData ((q,(y,r)),z))
    φ hφ hCompact
  have hFlux : (fun x => matrixOperatorMap
      ((referencePhysicalHalfGauge g L Φ ((q,(y,r)),x))^2 • a ((q,(y,r)),x)) (gradient φ x)) =
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
        (gradient φ x)) := by
    funext x
    rw [referencePhysicalHalfGauge_sq_smul_native g L y0 Φ B ε C ρ H a w hData]
  simpa only [hFlux] using hWeak

end OAI.AnisotropicCalderon.ConnectionError
