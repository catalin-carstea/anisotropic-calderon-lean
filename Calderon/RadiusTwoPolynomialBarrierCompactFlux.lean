import Calderon.SmoothFluxCompactTestIntegration
import TauCeti.Analysis.Sobolev.TestFunctionLp

/-! EXPANSION.json precedes literal polynomial barrier compact-test flux. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal Distributions Gradient ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open MetricVolume DirichletFamily.DriftBootstrap

lemma fderiv_radialBarrierFlux_coordinate (M : ℝ) (i : Fin 3) (x : R3) :
    fderiv ℝ (fun y : R3 => (-2*M)*y i) x (coordinateVector i) = -2*M := by
  have hD : HasFDerivAt (fun y : R3 => (-2*M)*y i)
      ((-2*M) • (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)) x :=
    (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt.const_mul (-2*M)
  rw [hD.fderiv]
  simp [ContinuousLinearMap.smul_apply,EuclideanSpace.coe_proj,coordinateVector,
    PiLp.single_apply,smul_eq_mul]

lemma integral_gradient_dot_radialBarrier (Omega : Opens R3) (M : ℝ) (phi : 𝓓(Omega, ℝ)) :
    (∫ x in Omega, ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x) ∂(volume : Measure R3)) =
      ∫ x in Omega, (6*M)*phi x ∂(volume : Measure R3) := by
  let J : Fin 3 → R3 → ℝ := fun i x => (-2*M)*x i
  have hJ : ∀ i : Fin 3, ContDiffOn ℝ ∞ (J i) Omega := by
    intro i
    have hProj : ContDiff ℝ ∞ (fun x : R3 => x i) :=
      (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff
    exact (contDiff_const.mul hProj).contDiffOn
  have hDiv (x : R3) : (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)) = -6*M := by
    simp only [J,fderiv_radialBarrierFlux_coordinate]
    simp only [Fin.sum_univ_three]
    ring
  have hPoint (x : R3) : ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x) =
      ∑ i : Fin 3, lineDeriv ℝ (phi : R3 → ℝ) x (coordinateVector i) * J i x := by
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i hi
    change ((∇ (phi : R3 → ℝ) x) : R3) i * ((-2*M)*x i) =
      lineDeriv ℝ (phi : R3 → ℝ) x (coordinateVector i) * ((-2*M)*x i)
    rw [gradient_coordinate,(phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have hGrad0 (x : R3) (hx : x ∉ (Omega : Set R3)) : ∇ (phi : R3 → ℝ) x = 0 := by
    by_contra h
    exact hx (TauCeti.support_gradient_testFunction_subset phi h)
  have hPhi0 (x : R3) (hx : x ∉ (Omega : Set R3)) : phi x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (phi.tsupport_subset h))
  have hLeftSet : (∫ x in Omega, ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x) ∂(volume : Measure R3)) =
      ∫ x, ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x) ∂(volume : Measure R3) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hGrad0 x hx,dotProduct])
  have hRightSet : (∫ x in Omega, (6*M)*phi x ∂(volume : Measure R3)) =
      ∫ x, (6*M)*phi x ∂(volume : Measure R3) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hPhi0 x hx,mul_zero])
  have hLeftGlobal : (∫ x, ((∇ (phi : R3 → ℝ) x) : R3) ⬝ᵥ ((-2*M) • x) ∂(volume : Measure R3)) =
      ∫ x, (∑ i : Fin 3, lineDeriv ℝ (phi : R3 → ℝ) x (coordinateVector i) * J i x)
        ∂(volume : Measure R3) := integral_congr_ae (Eventually.of_forall hPoint)
  have hIbP := smoothFlux_compactTest_integration Omega J hJ phi
  have hRight : -(∫ x, phi x * (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i))
      ∂(volume : Measure R3)) = ∫ x, (6*M)*phi x ∂(volume : Measure R3) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change -(phi x * (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i))) = (6*M)*phi x
      rw [hDiv x]
      ring)
  exact hLeftSet.trans (hLeftGlobal.trans (hIbP.trans (hRight.trans hRightSet.symm)))

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.fderiv_radialBarrierFlux_coordinate
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.integral_gradient_dot_radialBarrier
