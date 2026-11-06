import Calderon.ActualLocalParameterStrictWeightCarleman
import Calderon.MixedKernelConstruction.MixedKernelNativeRoomInterpolation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem principal_carleman_uniform_near_dilation_of_metric_strictness
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3→ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ r C tau0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ tau0 ∧
      ∀ lambda ∈ closedBall lam r, ∀ tau : ℝ, tau0 ≤ tau → ∀ w : R3→ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall p r →
      tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*θ y)*w y) x^2)+
        tau^3*(∫ x,(Real.exp (tau*θ x)*w x)^2) ≤
        C*∫ x,Real.exp (2*(tau*θ x))*Lop (fun i k y => principalCoefficient g (lambda • y) i k) w x^2 := by
  have hA : ∀ i k, ContDiff ℝ ∞ (fun z => (g (lam • z))⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry g hg i k).comp (contDiff_id.const_smul lam)
  have hsymm : ∀ i k, (fun z => (g (lam • z))⁻¹ i k) =
      (fun z => (g (lam • z))⁻¹ k i) := fun i k => funext fun z => by
    simpa only [star_trivial] using ((hg.posDef (lam • z)).inv.isHermitian.apply k i)
  have hdg : ∀ i j, DifferentiableAt ℝ (fun y => g (lam • y) i j) p := fun i j =>
    (((hg.smooth i j).comp (contDiff_id.const_smul lam)).differentiable (by simp)) p
  have hpd := hg.posDef (lam • p)
  obtain ⟨hN, hcrit⟩ := StrictWeightCarleman.point_criterion_of_metric_strictness
    (A := fun i k z => (g (lam • z))⁻¹ i k) (G := fun i j z => g (lam • z) i j)
    hA hθ hsymm p
    (fun r i j => fderiv_inverseMetric_entry_apply (fun y => g (lam • y)) p
      (EuclideanSpace.single r 1) hdg hpd i j)
    (fun i k => by
      have hm := Matrix.mul_nonsing_inv (g (lam • p)) (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
      have := congrFun (congrFun hm i) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun v hv => by
      have := hpd.dotProduct_mulVec_pos hv
      convert this using 1
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring)
    hdθ hsrc
  have hvol : 0 < vol g (lam • p) := Real.sqrt_pos.mpr hpd.det_pos
  obtain ⟨hNb, hcritb⟩ := StrictWeightCarleman.point_strictness_smul
    (b := fun i k z => principalCoefficient g (lam • z) i k)
    (ρ := fun z => vol g (lam • z))
    (fun i k z => by simp [principalCoefficient])
    ((contDiff_vol g hg).comp (contDiff_id.const_smul lam)) hA hθ p hvol hN hcrit
  have hb : ∀ i k, ContDiff ℝ ∞ (fun z => principalCoefficient g (lam • z) i k) :=
    fun i k => (contDiff_principalCoefficient_entry g hg i k).comp (contDiff_id.const_smul lam)
  have hbs : ∀ i k, (fun z => principalCoefficient g (lam • z) i k) =
      (fun z => principalCoefficient g (lam • z) k i) := fun i k => funext fun z => by
    simpa only [star_trivial] using
      ((principalCoefficient_posDef g hg (lam • z)).isHermitian.apply k i)
  have haJoint : ∀ i k, JointSmooth (fun lambda:ℝ => fun y => principalCoefficient g (lambda • y) i k) :=
    fun i k => (contDiff_principalCoefficient_entry g hg i k).comp (contDiff_fst.smul contDiff_snd)
  have hthetaJoint : JointSmooth (fun _:ℝ => θ) := hθ.comp contDiff_snd
  have hsAll : ∀ (lambda:ℝ) i k,(fun y => principalCoefficient g (lambda • y) i k)=
      (fun y => principalCoefficient g (lambda • y) k i) := by
    intro lambda i k
    funext y
    simpa only [star_trivial] using ((principalCoefficient_posDef g hg (lambda • y)).isHermitian.apply k i)
  exact exists_local_parameter_strict_weight_carleman_of_point_criterion
    (fun lambda:ℝ => fun i k y => principalCoefficient g (lambda • y) i k)
    (fun _:ℝ => θ) haJoint hthetaJoint hsAll lam p hNb hcritb

theorem exists_kappa_principal_carleman_strictPhase_uniform_near_dilation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3→ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p=0)
    (hdθ : (fun k => pd k θ p)≠0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) :
    ∃ kappa0 : ℝ, 0 < kappa0 ∧ ∀ kappa : ℝ, 0 ≤ kappa → kappa ≤ kappa0 →
      ∃ r C tau0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ tau0 ∧
      ∀ lambda ∈ closedBall lam r, ∀ tau : ℝ, tau0 ≤ tau → ∀ w : R3→ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall p r →
      tau*(∫ x,∑ i,pd i (fun y => Real.exp (tau*(θ y-kappa*θ y^2))*w y) x^2)+
        tau^3*(∫ x,(Real.exp (tau*(θ x-kappa*θ x^2))*w x)^2) ≤
        C*∫ x,Real.exp (2*(tau*(θ x-kappa*θ x^2)))*
          Lop (fun i k y => principalCoefficient g (lambda • y) i k) w x^2 := by
  obtain ⟨kappa0,hkappa0,H⟩ := exists_kappa_srcStrict_strictPhase_dilate g hg lam hθ p h0 hsrc
  refine ⟨kappa0,hkappa0,?_⟩
  intro kappa hkappa hkappa0le
  have hpsi : ContDiff ℝ ∞ (fun y => θ y-kappa*θ y^2) := hθ.sub (contDiff_const.mul (hθ.pow 2))
  have hdpsi : (fun k => pd k (fun y => θ y-kappa*θ y^2) p)≠0 := by
    have heq : (fun k => pd k (fun y => θ y-kappa*θ y^2) p)=(fun k => pd k θ p) :=
      funext fun k => pd_strictPhase_of_zero hθ kappa h0 k
    rw [heq]
    exact hdθ
  exact principal_carleman_uniform_near_dilation_of_metric_strictness g hg lam hpsi p hdpsi (H kappa hkappa hkappa0le)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
