import Calderon.NativeH1OrthogonalDerivativeTransport
import Calderon.StrongDerivativeValues

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma orthogonal_inverse_coordinate_eq_sum (e : R3 ≃ₗᵢ[ℝ] R3) (j : Fin 3) (z : R3) :
    (e.symm z) j = ∑ l : Fin 3, (e (EuclideanSpace.single j 1)) l * z l := by
  have h := e.inner_map_map (e.symm z) (EuclideanSpace.single j 1)
  simp only [e.apply_symm_apply,EuclideanSpace.inner_single_right,conj_trivial,one_mul] at h
  rw [← h]
  simp only [PiLp.inner_apply,Real.inner_apply,mul_comm]

lemma value_nativeH1_sum_smul_ae (c : Fin 3 → ℝ) (v : Fin 3 → BallH1) :
    TauCeti.W1p.value (∑ l : Fin 3, c l • v l) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => ∑ l : Fin 3, c l * TauCeti.W1p.value (v l) x := by
  have hmap : TauCeti.W1p.value (∑ l : Fin 3, c l • v l) =
      ∑ l : Fin 3, c l • TauCeti.W1p.value (v l) := by
    change TauCeti.W1p.valueL (∑ l : Fin 3, c l • v l) = _
    simp only [map_sum,map_smul,TauCeti.W1p.valueL_apply]
  rw [hmap]
  exact (Lp.coeFn_finsetSum Finset.univ (fun l => c l • TauCeti.W1p.value (v l))).trans
    (eventuallyEq_sum fun l _ => Lp.coeFn_smul (c l) (TauCeti.W1p.value (v l)))

lemma gradient_nativeH1OrthogonalPullback_ae (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    TauCeti.W1p.gradient (nativeH1OrthogonalPullback e u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => e.symm (TauCeti.W1p.gradient u (e x)) := by
  rw [gradient_nativeH1OrthogonalPullback]
  filter_upwards [e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (Lp.compMeasurePreserving e (orthogonal_measurePreserving_unitBall e) (TauCeti.W1p.gradient u)),
    Lp.coeFn_compMeasurePreserving (TauCeti.W1p.gradient u)
      (orthogonal_measurePreserving_unitBall e)] with x h1 h2
  exact h1.trans (congrArg e.symm h2)

def nativeH2OrthogonalDerivativeComponent
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (j : Fin 3)
    (U : BallSobolev 2) : BallH1 :=
  ∑ l : Fin 3, (e (EuclideanSpace.single j 1)) l •
    nativeH1OrthogonalPullback e
      (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 l U))

lemma value_nativeH2OrthogonalDerivativeComponent
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (j : Fin 3)
    (U : BallSobolev 2) :
    TauCeti.W1p.value (nativeH2OrthogonalDerivativeComponent hcalc e j U) =
      unitBallCoordinateGradientL j (nativeH1OrthogonalPullback e (TauCeti.Wkp.firstOrder 1 U)) := by
  let u := TauCeti.Wkp.firstOrder 1 U
  let v := fun l => nativeH1OrthogonalPullback e
    (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 l U))
  have hv : ∀ l, TauCeti.W1p.value (v l) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => (TauCeti.W1p.gradient u (e x)) l := by
    intro l
    change TauCeti.W1p.value (nativeH1OrthogonalPullback e _) =ᵐ[_] _
    rw [value_nativeH1OrthogonalPullback,TauCeti.Wkp.value_firstOrder,
      unitBallCoordinateDerivative_eq_coordinateGradient]
    exact (Lp.coeFn_compMeasurePreserving (unitBallCoordinateGradientL l u)
      (orthogonal_measurePreserving_unitBall e)).trans
      ((orthogonal_measurePreserving_unitBall e).quasiMeasurePreserving.ae_eq_comp
        (unitBallCoordinateGradientL_ae l u))
  apply Lp.ext
  filter_upwards [value_nativeH1_sum_smul_ae (fun l => (e (EuclideanSpace.single j 1)) l) v,
    ae_all_iff.mpr hv,unitBallCoordinateGradientL_ae j (nativeH1OrthogonalPullback e u),
    gradient_nativeH1OrthogonalPullback_ae e u] with x hs hvx hc hg
  change TauCeti.W1p.value (∑ l : Fin 3, (e (EuclideanSpace.single j 1)) l • v l) x = _
  rw [hs,hc,hg,orthogonal_inverse_coordinate_eq_sum]
  exact Finset.sum_congr rfl (fun l _ => congrArg ((e (EuclideanSpace.single j 1)) l * ·) (hvx l))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonal_inverse_coordinate_eq_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeH1_sum_smul_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_nativeH1OrthogonalPullback_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2OrthogonalDerivativeComponent
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeH2OrthogonalDerivativeComponent
