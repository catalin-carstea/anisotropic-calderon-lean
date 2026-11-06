import TaskInterface
import Calderon.ActualHarmonicCoordinateConformalRigidity
import Calderon.NormalizedPrincipalMetricEquality
import Calderon.NormalizedPrincipalMetricSmooth
import Calderon.ActualReferenceRadiusCompactContinuation

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricOperator NormalCoordinatesFrame
open NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ConformalDepth ReferenceDensityBounds
open CoordinateBootstrapJets RadiusProfile

/-- The actual normalized principal difference gives a smooth positive conformal
factor, without assuming conformality as a new premise. -/
theorem exists_smooth_conformal_factor_of_referenceNormalizedPrincipalDifference_eq_zero
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (U : Set R3)
    (hZero : EqOn (referenceNormalizedPrincipalDifference g1 g2 L lam) (fun _ => 0) U) :
    ∃ omega : R3 → ℝ, ContDiff ℝ ∞ omega ∧
      EqOn (dilatedMetric g2 lam) (conformalMatrix (dilatedMetric g1 lam) omega) U := by
  let T : R3 → ℝ := fun x => referenceNormalizationTraceFamily g1 g2 L (lam,x)
  let f : R3 → ℝ := fun x => (3 / T x) * Real.exp (2 * (-L * referenceCoordinateDepth x))
  let omega : R3 → ℝ := fun x => (1/2 : ℝ) * Real.log (f x)
  have hT : ContDiff ℝ ∞ T :=
    (contDiff_referenceNormalizationTraceFamily g1 g2 hg1 hg2 L).comp
      (contDiff_const.prodMk contDiff_id)
  have hTp (x : R3) : 0 < T x :=
    referenceNormalizationTraceFamily_pos g1 g2 hg1 hg2 L (lam,x)
  have hfp (x : R3) : 0 < f x := mul_pos (div_pos (by norm_num) (hTp x)) (Real.exp_pos _)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.div hT (fun x => (hTp x).ne')).mul
      ((contDiff_const.mul (contDiff_const.mul contDiff_referenceCoordinateDepth)).exp)
  have ho : ContDiff ℝ ∞ omega :=
    contDiff_const.mul (hf.log (fun x => (hfp x).ne'))
  refine ⟨omega, ho, ?_⟩
  intro x hx
  have he : Real.exp (2 * omega x) = f x := by
    dsimp [omega]
    have hh : 2 * ((1/2 : ℝ) * Real.log (f x)) = Real.log (f x) := by ring
    rw [hh, Real.exp_log (hfp x)]
  have hm := eq_smul_of_normalizedPrincipalDifference_eq_zero
    (referenceMetric (dilatedMetric g1 lam) L x) (g2 (lam • x))
    (conformalMatrix_posDef _ _ (dilatedMetric_posDef g1 hg1 lam) x)
    (hg2.posDef (lam • x)) (hZero hx)
  change g2 (lam • x) = Real.exp (2 * omega x) • g1 (lam • x)
  rw [he]
  simpa only [f, T, referenceNormalizationTraceFamily, referenceMetric, conformalMatrix, dilatedMetric, smul_smul] using hm

/-- The literal coordinate-flux divergence scales by lambda under the fixed
carrier dilation; this does not assert admissibility of the dilated carrier. -/
theorem coordinate_harmonic_divergence_dilated
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ) (x : R3) (j : Fin 3) :
    coordinateFluxDivergence (metricDivergenceFlux (dilatedMetric g lam)
      (fun z : R3 => z j)) x =
      lam * coordinateFluxDivergence (metricDivergenceFlux g (fun z : R3 => z j)) (lam • x) := by
  have hc (i : Fin 3) :
      (fun y => metricDivergenceFlux (dilatedMetric g lam) (fun z : R3 => z j) y i) =
        (fun y => principalCoefficient g (lam • y) i j) := by
    funext y
    rw [metricDivergenceFlux_coordinate_apply]
    rfl
  have ho (i : Fin 3) :
      (fun y => metricDivergenceFlux g (fun z : R3 => z j) y i) =
        (fun y => principalCoefficient g y i j) := by
    funext y
    exact metricDivergenceFlux_coordinate_apply g y i j
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun y => principalCoefficient g y i j) (lam • x) :=
    ((contDiff_pi.mp (contDiff_pi.mp
      (contDiff_principalCoefficient_of_smooth_posDef g hg.smooth hg.posDef) i) j).differentiable
        (by simp)) (lam • x)
  have hterm (i : Fin 3) :
      fderiv ℝ (fun y => principalCoefficient g (lam • y) i j) x (coordinateVector i) =
        lam * fderiv ℝ (fun y => principalCoefficient g y i j) (lam • x) (coordinateVector i) := by
    have hf := (hd i).hasFDerivAt.comp x
      ((lam • ContinuousLinearMap.id ℝ R3).hasFDerivAt)
    have hf' : HasFDerivAt (fun y : R3 => principalCoefficient g (lam • y) i j)
        ((fderiv ℝ (fun y => principalCoefficient g y i j) (lam • x)).comp
          (lam • ContinuousLinearMap.id ℝ R3)) x := by
      simpa only [Function.comp_def] using hf
    rw [hf'.fderiv]
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  unfold coordinateFluxDivergence
  simp_rw [hc,ho,hterm]
  exact (Finset.mul_sum _ _ _).symm

/-- The exact normalized-principal zero identity gives equality of the original
coordinate metrics on an origin ball, undoing the same positive dilation. -/
theorem exists_ball_metric_eq_of_referenceNormalizedPrincipalDifference_eq_zero
    (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hZero : EqOn (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) (fun _ => 0) U) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
      EqOn S.g1 S.g2 (ball (0 : R3) r) := by
  obtain ⟨omega,hOmega,hConformal⟩ :=
    exists_smooth_conformal_factor_of_referenceNormalizedPrincipalDifference_eq_zero
      S.g1 S.g2 S.g1_admissible S.g2_admissible L lam U hZero
  let V : Set R3 := U ∩ (fun x : R3 => lam • x) ⁻¹' S.coordinateRoom
  have hV : IsOpen V := hU.inter
    (S.coordinateRoom_open.preimage
      (lam • (ContinuousLinearMap.id ℝ R3)).continuous)
  have hV0 : (0 : R3) ∈ V := ⟨h0,by simpa using S.origin_mem⟩
  obtain ⟨a,ha,hBall⟩ := Metric.isOpen_iff.mp hV 0 hV0
  have hSame : dilatedMetric S.g1 lam 0 = dilatedMetric S.g2 lam 0 := by
    simpa only [dilatedMetric,smul_zero] using S.g1_origin.trans S.g2_origin.symm
  have hHarm1 : ∀ x ∈ ball (0 : R3) a, ∀ j : Fin 3,
      coordinateFluxDivergence (metricDivergenceFlux (dilatedMetric S.g1 lam)
        (fun z : R3 => z j)) x = 0 := by
    intro x hx j
    rw [coordinate_harmonic_divergence_dilated S.g1 S.g1_admissible]
    rw [S.harmonic_coordinates1 j (lam • x) (hBall hx).2,mul_zero]
  have hHarm2 : ∀ x ∈ ball (0 : R3) a, ∀ j : Fin 3,
      coordinateFluxDivergence (metricDivergenceFlux (dilatedMetric S.g2 lam)
        (fun z : R3 => z j)) x = 0 := by
    intro x hx j
    rw [coordinate_harmonic_divergence_dilated S.g2 S.g2_admissible]
    rw [S.harmonic_coordinates2 j (lam • x) (hBall hx).2,mul_zero]
  have hEq : EqOn (dilatedMetric S.g1 lam) (dilatedMetric S.g2 lam) (ball (0 : R3) a) :=
    eqOn_metric_of_conformal_and_coordinate_harmonic
      (dilatedMetric S.g1 lam) (dilatedMetric S.g2 lam) omega
      (fun i j => (S.g1_admissible.smooth i j).comp (lam • (ContinuousLinearMap.id ℝ R3)).contDiff)
      (dilatedMetric_posDef S.g1 S.g1_admissible lam) hOmega
      (ball (0 : R3) a) isOpen_ball (convex_ball 0 a).isPreconnected
      0 (by simpa using ha) hSame
      (fun x hx => hConformal (hBall hx).1) hHarm1 hHarm2
  refine ⟨lam*a,mul_pos hlam ha,?_,?_⟩
  · intro y hy
    have hNorm : ‖y‖ < lam*a := by simpa [dist_zero_right] using hy
    have hBack : lam⁻¹ • y ∈ ball (0 : R3) a := by
      rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam)]
      exact (inv_mul_lt_iff₀ hlam).2 hNorm
    have hh := (hBall hBack).2
    simpa only [mem_preimage,smul_smul,mul_inv_cancel₀ hlam.ne',one_smul] using hh
  · intro y hy
    have hNorm : ‖y‖ < lam*a := by simpa [dist_zero_right] using hy
    have hBack : lam⁻¹ • y ∈ ball (0 : R3) a := by
      rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam)]
      exact (inv_mul_lt_iff₀ hlam).2 hNorm
    simpa only [dilatedMetric,smul_smul,mul_inv_cancel₀ hlam.ne',one_smul] using hEq hBack

/-- Compact strict improvement and the exact off-K bound give equality of the original metrics locally. -/
theorem exists_ball_metric_eq_of_compact_strict_improvement
    (S : KnownSideSourceData)
    (L lam R eps : ℝ) (p : ℕ) (K : Set R3) (hK : IsCompact K)
    (hlam : 0 < lam) (hL : 0 < L) (hR : 0 < R) (heps : 0 < eps) (hp : 1 ≤ p)
    (hInitial : ∀ x ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius 1 R p L x)
    (hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius delta R p L x) →
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        (eps/2) * referenceRadius delta R p L x)
    (hOff : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ cylinder, x ∉ K →
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius delta R p L x) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
      EqOn S.g1 S.g2 (ball (0 : R3) r) := by
  obtain ⟨U,hU,h0,_hCyl,hZero⟩ :=
    exists_open_principal_vanishing_of_compact_strict_improvement
      S.g1 S.g2 S.g1_admissible S.g2_admissible L lam R eps p K hK hL hR heps hp
      hInitial hImprove hOff
  exact exists_ball_metric_eq_of_referenceNormalizedPrincipalDifference_eq_zero
    S L lam hlam U hU h0 hZero

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
