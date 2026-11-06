import Calderon.ActualMixedKernelScalarTransfer
import Calderon.ActualPhysicalBoundaryChainRule
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Basic
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap

theorem nativeMixedKernelDensityFunctional_sub_center_le_of_taylor_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam delta Rstar : ℝ) (p : ℕ)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (u : SmoothData) (y : R3)
    (C : ℝ) (hC : 0 ≤ C)
    (hMass : nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi
      (⟨fun _ => (1 : ℝ), contDiff_const⟩ : SmoothData) y = 1)
    (hCoordinates : ∀ k : Fin 3,
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi
        (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k)
    (hTaylor : ∀ z : UnitSphere,
      |u.1 (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val) - u.1 y -
        fderiv ℝ u.1 y
          (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z.val - y)| ≤
        C * (referenceRadius delta Rstar p L y)^2) :
    |nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y - u.1 y| ≤
      C * (referenceRadius delta Rstar p L y)^2 *
        ‖(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
  classical
  let r : ℝ := referenceRadius delta Rstar p L y
  let w : SphereL2 := (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
  let b : SmoothData → C(UnitSphere, ℝ) := fun v =>
    smoothSphereValue (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
      P.native_data.1.1.1 lam y r v)
  let oneData : SmoothData := ⟨fun _ => (1 : ℝ), contDiff_const⟩
  let coordinateData : Fin 3 → SmoothData := fun k =>
    ⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩
  let ell : R3 →L[ℝ] ℝ := fderiv ℝ u.1 y
  let coeff : Fin 3 → ℝ := fun k => ell (EuclideanSpace.single k 1)
  let residual : C(UnitSphere, ℝ) :=
    b u - u.1 y • b oneData - ∑ k : Fin 3, coeff k • (b (coordinateData k) - y k • b oneData)
  let T : C(UnitSphere, ℝ) →L[ℝ] SphereL2 := ContinuousMap.toLp 2 sphereProbability ℝ
  have hEval (v : SmoothData) :
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi v y =
        ⟪w, T (b v)⟫_ℝ := by
    unfold nativeMixedKernelDensityFunctional
    rw [tau.valueTrace_smooth]
  have hBasis (v : R3) : ell v = ∑ k : Fin 3, coeff k * v k := by
    have hv : v = ∑ k : Fin 3, v k • EuclideanSpace.single k (1 : ℝ) := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_succ, Pi.single_apply]
    calc
      ell v = ell (∑ k : Fin 3, v k • EuclideanSpace.single k (1 : ℝ)) := congrArg ell hv
      _ = ∑ k : Fin 3, coeff k * v k := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, coeff]
        apply Finset.sum_congr rfl
        intro k hk
        exact mul_comm _ _
  have hResidual (z : UnitSphere) :
      residual z = u.1 (packetEndpoint S L P lam y r z.val) - u.1 y -
        ell (packetEndpoint S L P lam y r z.val - y) := by
    rw [hBasis]
    simp only [residual, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply, smul_eq_mul, b, smoothSphereValue_referencePhysicalPullback_apply,
      oneData, coordinateData, sub_mul, Finset.sum_sub_distrib, mul_one]
    rfl
  have hPair : ⟪w, T residual⟫_ℝ =
      nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y - u.1 y := by
    simp only [residual, map_sub, map_smul, map_sum, inner_sub_right, inner_smul_right,
      inner_sum]
    rw [← hEval u, ← hEval oneData, hMass]
    have hCoord (k : Fin 3) : ⟪w, T (b (coordinateData k))⟫_ℝ = y k :=
      (hEval (coordinateData k)).symm.trans (hCoordinates k)
    simp only [hCoord, sub_self, mul_zero, Finset.sum_const_zero, mul_one, sub_zero]
  have hBound : ‖residual‖ ≤ C * r^2 := by
    apply (ContinuousMap.norm_le residual (mul_nonneg hC (sq_nonneg r))).2
    intro z
    rw [Real.norm_eq_abs, hResidual]
    exact hTaylor z
  have hTOp : ‖T‖ ≤ 1 := by
    simpa [T, measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (p := (2 : ENNReal)) (μ := sphereProbability) (𝕜 := ℝ) (E := ℝ))
  have hTBound : ‖T residual‖ ≤ C * r^2 :=
    ((T.le_opNorm residual).trans
      (mul_le_mul_of_nonneg_right hTOp (norm_nonneg residual))).trans
        (by simpa only [one_mul] using hBound)
  calc
    |nativeMixedKernelDensityFunctional hO hD tau S L P lam delta Rstar p Psi u y - u.1 y| =
        |⟪w, T residual⟫_ℝ| := congrArg abs hPair.symm
    _ ≤ ‖w‖ * ‖T residual‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * (C * r^2) := mul_le_mul_of_nonneg_left hTBound (norm_nonneg w)
    _ = _ := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
