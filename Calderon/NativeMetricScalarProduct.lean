import Calderon.ActualFiniteCompatibleSourceJetsFromUniqueContinuation
import Calderon.RadiusTwoSmoothSourceClassicalEquation
import Calderon.FrozenCartesianChainRule
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Same native coefficient and actual source witnesses for Main M5.
Coefficient proportionality and the matched-source pullback PDE remain separate
obligations; this component only eliminates the scalar derivative. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Distributions Topology BigOperators Matrix
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature MetricVolume

theorem nativeMetricDifferential_eq_scalar_mul_sub_gradient
    (k g : MatrixField) (hg : IsAdmissibleMetric g) (c u : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (x : R3) (hx : x ∈ U)
    (hc : DifferentiableAt ℝ c x)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hA : ∀ y ∈ U, principalCoefficient k y = c y • principalCoefficient g y) :
    nativeMetricDifferential k u x = c x * nativeMetricDifferential g u x -
      ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ c x (coordinateVector i) * principalCoefficient g x i j *
          fderiv ℝ u x (coordinateVector j) := by
  classical
  let Q : Fin 3 → R3 → ℝ := fun i y =>
    ∑ j : Fin 3, principalCoefficient g y i j * fderiv ℝ u y (coordinateVector j)
  have hQ (i : Fin 3) : DifferentiableAt ℝ (Q i) x := by
    apply DifferentiableAt.fun_sum
    intro j _
    exact ((contDiff_principalCoefficient_entry g hg i j).differentiable (by simp) x).mul
      (hu.clm_apply (differentiableAt_const _))
  have hFlux (i : Fin 3) :
      (fun y : R3 => ∑ j : Fin 3, principalCoefficient k y i j *
        fderiv ℝ u y (coordinateVector j)) =ᶠ[𝓝 x] (fun y => c y * Q i y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hA y hy]
    simp only [Matrix.smul_apply, smul_eq_mul, Q, Finset.mul_sum, mul_assoc]
  have hDerivative (i : Fin 3) :
      fderiv ℝ (fun y : R3 => ∑ j : Fin 3, principalCoefficient k y i j *
        fderiv ℝ u y (coordinateVector j)) x (coordinateVector i) =
      fderiv ℝ c x (coordinateVector i) * Q i x +
        c x * fderiv ℝ (Q i) x (coordinateVector i) := by
    rw [(hFlux i).fderiv_eq, fderiv_fun_mul hc (hQ i)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hGradient :
      (∑ i : Fin 3, fderiv ℝ c x (coordinateVector i) * Q i x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ c x (coordinateVector i) * principalCoefficient g x i j *
          fderiv ℝ u x (coordinateVector j) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Q, Finset.mul_sum, mul_assoc]
  unfold nativeMetricDifferential
  simp_rw [hDerivative]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hGradient]
  change -(_ + c x * _) = c x * (-_) - _
  ring

theorem fderiv_eq_zero_of_nativeMetricDifferential_source_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (k g : MatrixField) (hg : IsAdmissibleMetric g) (c : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hRoom : U ⊆ (radiusTwoOpens : Set R3))
    (hSource : ∀ x ∈ U, x ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ))
    (hc : DifferentiableOn ℝ c U)
    (hA : ∀ x ∈ U, principalCoefficient k x = c x • principalCoefficient g x)
    (hPDE : ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ U,
      nativeMetricDifferential k (radiusTwoSmoothSourceResponse hreg hcalc g hg source) x = 0) :
    ∀ x ∈ U, fderiv ℝ c x = 0 := by
  classical
  intro x hx
  let v : Fin 3 → ℝ := fun i => fderiv ℝ c x (coordinateVector i)
  obtain ⟨f,hf⟩ := exists_radiusTwoSmoothSource_coordinate_firstJets_of_proved_uniqueContinuation
    hreg hcalc g hg x (hRoom hx) (hSource x hx)
  have hSum (j : Fin 3) : (∑ i : Fin 3, v i * principalCoefficient g x i j) = 0 := by
    let u := radiusTwoSmoothSourceResponse hreg hcalc g hg (f j)
    have hSmooth := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f j)).2.1
    have hDSmooth : ContDiffOn ℝ ∞ (fderiv ℝ u) (radiusTwoOpens : Set R3) :=
      hSmooth.fderiv_of_isOpen radiusTwoOpens.isOpen (by simp)
    have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
      (hDSmooth.contDiffAt (radiusTwoOpens.isOpen.mem_nhds (hRoom hx))).differentiableAt (by simp)
    have hOutside : x ∉ (fixedExteriorSourceOpens : Set R3) :=
      fun h => hSource x hx (ball_subset_closedBall h)
    have hZero : (f j) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hOutside ((f j).tsupport_subset h))
    have hLg : nativeMetricDifferential g u x = 0 :=
      (nativeMetricDifferential_radiusTwoSmoothSourceResponse hreg hcalc g hg (f j)
        x (hRoom hx)).trans hZero
    have hIdentity := nativeMetricDifferential_eq_scalar_mul_sub_gradient k g hg c u U hU x hx
      (hc.differentiableAt (hU.mem_nhds hx)) hD hA
    rw [hPDE (f j) x hx, hLg, mul_zero, zero_sub] at hIdentity
    have hContraction := neg_eq_zero.mp hIdentity.symm
    have hProj (l : Fin 3) :
        (EuclideanSpace.proj j : R3 →L[ℝ] ℝ) (coordinateVector l) =
          if l = j then 1 else 0 := by
      change (EuclideanSpace.single l (1 : ℝ)) j = _
      simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
    have hDu : fderiv ℝ u x = EuclideanSpace.proj j := (hf j).2.1
    rw [hDu] at hContraction
    simpa only [hProj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, v] using hContraction
  have hAv : (principalCoefficient g x).transpose *ᵥ v = 0 := by
    funext j
    change (∑ i : Fin 3, principalCoefficient g x i j * v i) = 0
    calc
      _ = ∑ i : Fin 3, v i * principalCoefficient g x i j :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = 0 := hSum j
  have hv : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero
    (M := (principalCoefficient g x).transpose)
    (by rw [Matrix.det_transpose]; exact (principalCoefficient_posDef g hg x).det_pos.ne') hAv
  have hPartial (i : Fin 3) : fderiv ℝ c x (EuclideanSpace.single i 1) = 0 :=
    congrFun hv i
  apply ContinuousLinearMap.ext
  intro W
  change fderiv ℝ c x W = 0
  rw [clm_apply_eq_sum_cartesian]
  simp only [hPartial, smul_zero, Finset.sum_const_zero]

theorem eqOn_const_of_nativeMetricDifferential_source_eq_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (k g : MatrixField) (hg : IsAdmissibleMetric g) (c : R3 → ℝ)
    (U : Set R3) (hU : IsOpen U) (hConn : IsPreconnected U)
    (hRoom : U ⊆ (radiusTwoOpens : Set R3))
    (hSource : ∀ x ∈ U, x ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ))
    (hc : DifferentiableOn ℝ c U)
    (hA : ∀ x ∈ U, principalCoefficient k x = c x • principalCoefficient g x)
    (hPDE : ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ U,
      nativeMetricDifferential k (radiusTwoSmoothSourceResponse hreg hcalc g hg source) x = 0)
    (p : R3) (hp : p ∈ U) : EqOn c (fun _ => c p) U := by
  have hZero : EqOn (fderiv ℝ c) 0 U :=
    fderiv_eq_zero_of_nativeMetricDifferential_source_eq_zero
      hreg hcalc k g hg c U hU hRoom hSource hc hA hPDE
  intro x hx
  exact hU.is_const_of_fderiv_eq_zero hConn hc hZero hx hp

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricDifferential_eq_scalar_mul_sub_gradient
#print axioms OAI.AnisotropicCalderon.ExteriorSource.fderiv_eq_zero_of_nativeMetricDifferential_source_eq_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eqOn_const_of_nativeMetricDifferential_source_eq_zero
