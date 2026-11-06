import Calderon.NativeH1CoordinateBoundaryGreen
import Calderon.NativeSmoothMultiplicationTrace
import Calderon.NativeZeroValueTrace
import Calderon.NativeContinuousCoefficientOrthogonalEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Gradient Classical Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic MetricVolume NativeH1CoordinateBoundaryGreen NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! The formal adjoint is (aᵀ,-b,c-div b), with the positive normal-drift
boundary term measured using the existing sphereProbability and sphereSurfaceMass. -/

def nativeAdjointDriftField (G : Fin 3 → SmoothData) : R3 → R3 :=
  fun x => WithLp.toLp 2 (fun i => (G i).1 x)

def nativeDriftDivergence (G : Fin 3 → SmoothData) : R3 → ℝ :=
  fun x => ∑ i : Fin 3, (gradient (G i).1 x) i

def nativeNormalDriftCoefficient (G : Fin 3 → SmoothData) : C(UnitSphere,ℝ) :=
  ∑ i : Fin 3, sphereCoordinate i * smoothSphereValue (G i)

lemma continuous_nativeAdjointDriftField (G : Fin 3 → SmoothData) :
    Continuous (nativeAdjointDriftField G) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi (fun i => (G i).2.continuous))

lemma continuous_nativeDriftDivergence (G : Fin 3 → SmoothData) :
    Continuous (nativeDriftDivergence G) := by
  apply continuous_finset_sum
  intro i hi
  exact (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous.comp
    ((G i).2.gradient_right (m := 0) (by simp)).continuous

lemma nativeNormalDriftCoefficient_apply (G : Fin 3 → SmoothData) (x : UnitSphere) :
    nativeNormalDriftCoefficient G x = ⟪nativeAdjointDriftField G x.val,x.val⟫_ℝ := by
  simp only [nativeNormalDriftCoefficient,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
    sphereCoordinate,smoothSphereValue,ContinuousMap.coe_mk,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma exists_native_smoothH1Product
    (τ0 : UnitBallValueTrace) (m : SmoothData) (u : BallH1) :
    ∃ w : BallH1,
      (TauCeti.W1p.value w =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => m.1 x * TauCeti.W1p.value u x) ∧
      (∀ i : Fin 3, unitBallCoordinateGradientL i w =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => m.1 x * (TauCeti.W1p.gradient u x) i +
          TauCeti.W1p.value u x * (gradient m.1 x) i) ∧
      τ0.valueTraceL w = sphereContinuousScalarMulL (smoothSphereValue m) (τ0.valueTraceL u) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound m
  let w : BallH1 := TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3))
    (Omega := ballOpens) (p := 2) m.1 m.2 hM hm hg u
  refine ⟨w,?_,?_,?_⟩
  · change TauCeti.W1p.value (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg u) =ᵐ[_] _
    rw [TauCeti.W1p.contDiffSMulL_apply]
    filter_upwards [TauCeti.W1p.value_contDiffSMul_ae
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.2 hM hm hg u] with x hx
    exact hx
  · intro i
    have hprod := TauCeti.W1p.gradient_contDiffSMul_ae
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.2 hM hm hg u
    filter_upwards [unitBallCoordinateGradientL_ae i w,hprod] with x hcoord hgrad
    rw [hcoord]
    change (TauCeti.W1p.gradient (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg u) x) i = _
    rw [TauCeti.W1p.contDiffSMulL_apply,hgrad]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  · exact valueTraceL_contDiffSMulL τ0 m hM hm hg u

lemma energyIntegrand_adjoint_difference (A : Matrix (Fin 3) (Fin 3) ℝ)
    (B D : R3) (c : ℝ) (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A B c V U -
      TauCeti.PDE.energyIntegrand Aᵀ (-B) (c-∑ i : Fin 3, D i) U V =
        ∑ i : Fin 3,
          ((B i * V.2 i + V.1 * D i) * U.1 + (B i * V.1) * U.2 i) := by
  simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.matrixBilinearForm_transpose_apply,
    TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,inner_neg_left,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial,
    Fin.sum_univ_three]
  ring

lemma sphereContinuousScalarMulL_native_value_ae (m : C(UnitSphere,ℝ)) (u : SphereL2) :
    sphereContinuousScalarMulL m u =ᵐ[sphereProbability] (fun x => m x * u x) := by
  change sphereContinuousScalarMul m u =ᵐ[sphereProbability] (fun x => m x * u x)
  exact sphereContinuousScalarMul_value_ae m u

lemma native_normalDrift_multiplier_sum (G : Fin 3 → SmoothData) (u : SphereL2) :
    (∑ i : Fin 3, sphereCoordinateMulL i
      (sphereContinuousScalarMulL (smoothSphereValue (G i)) u)) =
        sphereContinuousScalarMulL (nativeNormalDriftCoefficient G) u := by
  apply Lp.ext
  have hi : ∀ᵐ x ∂sphereProbability, ∀ i : Fin 3,
      sphereCoordinateMulL i (sphereContinuousScalarMulL (smoothSphereValue (G i)) u) x =
        x.val i * (G i).1 x.val * u x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [sphereCoordinateMul_value_ae i
      (sphereContinuousScalarMulL (smoothSphereValue (G i)) u),
      sphereContinuousScalarMulL_native_value_ae (smoothSphereValue (G i)) u] with x hcoord hmul
    change sphereCoordinateMul i (sphereContinuousScalarMulL (smoothSphereValue (G i)) u) x = _
    rw [hcoord,hmul]
    change x.val i * ((G i).1 x.val * u x) = _
    ring
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : Fin 3 => sphereCoordinateMulL i
        (sphereContinuousScalarMulL (smoothSphereValue (G i)) u)),
    sphereContinuousScalarMulL_native_value_ae (nativeNormalDriftCoefficient G) u,hi] with x hsum hmul hx
  rw [hsum,hmul]
  simp only [nativeNormalDriftCoefficient,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
  change (∑ i : Fin 3, sphereCoordinateMulL i
      (sphereContinuousScalarMulL (smoothSphereValue (G i)) u) x) =
    (∑ i : Fin 3, x.val i * (G i).1 x.val) * u x
  simp_rw [hx]
  rw [Finset.sum_mul]

lemma inner_nativeNormalDriftMultiplier_comm (G : Fin 3 → SmoothData) (u v : SphereL2) :
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G) v,u⟫_ℝ =
      ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G) u,v⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereContinuousScalarMulL_native_value_ae (nativeNormalDriftCoefficient G) u,
    sphereContinuousScalarMulL_native_value_ae (nativeNormalDriftCoefficient G) v] with x hu hv
  rw [Real.inner_apply,Real.inner_apply,hu,hv]
  ring


lemma nativeCoordinateBulkPairing_eq_integral (F u : BallH1) (i : Fin 3) :
    ⟪unitBallCoordinateGradientL i F,TauCeti.W1p.value u⟫_ℝ +
      ⟪TauCeti.W1p.value F,unitBallCoordinateGradientL i u⟫_ℝ =
    ∫ x in ballOpens, (⟪unitBallCoordinateGradientL i F x,TauCeti.W1p.value u x⟫_ℝ +
      ⟪TauCeti.W1p.value F x,unitBallCoordinateGradientL i u x⟫_ℝ) := by
  rw [L2.inner_def,L2.inner_def]
  exact (integral_add
    (L2.integrable_inner (𝕜 := ℝ) (unitBallCoordinateGradientL i F) (TauCeti.W1p.value u))
    (L2.integrable_inner (𝕜 := ℝ) (TauCeti.W1p.value F) (unitBallCoordinateGradientL i u))).symm

lemma energyFormH1_adjoint_bulk_difference
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (c x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hadj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (c x-nativeDriftDivergence G x)) ⊤
        ((volume : Measure R3).restrict ballOpens)) (u v : BallH1)
    (W : Fin 3 → BallH1)
    (hWvalue : ∀ i : Fin 3, TauCeti.W1p.value (W i) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (G i).1 x * TauCeti.W1p.value v x))
    (hWgrad : ∀ i j : Fin 3, unitBallCoordinateGradientL j (W i) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (G i).1 x * (TauCeti.W1p.gradient v x) j +
        TauCeti.W1p.value v x * (gradient (G i).1 x) j)) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (nativeAdjointDriftField G) c v u -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
      (fun x => c x-nativeDriftDivergence G x) u v =
    ∑ i : Fin 3, (⟪unitBallCoordinateGradientL i (W i),TauCeti.W1p.value u⟫_ℝ +
      ⟪TauCeti.W1p.value (W i),unitBallCoordinateGradientL i u⟫_ℝ) := by
  let z (i : Fin 3) (x : R3) : ℝ :=
    ⟪unitBallCoordinateGradientL i (W i) x,TauCeti.W1p.value u x⟫_ℝ +
      ⟪TauCeti.W1p.value (W i) x,unitBallCoordinateGradientL i u x⟫_ℝ
  have hz (i : Fin 3) : Integrable (z i) ((volume : Measure R3).restrict ballOpens) :=
    (L2.integrable_inner (𝕜 := ℝ) (unitBallCoordinateGradientL i (W i))
      (TauCeti.W1p.value u)).add
        (L2.integrable_inner (𝕜 := ℝ) (TauCeti.W1p.value (W i)) (unitBallCoordinateGradientL i u))
  have hV : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      TauCeti.W1p.value (W i) x = (G i).1 x * TauCeti.W1p.value v x :=
    ae_all_iff.mpr hWvalue
  have hD : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      unitBallCoordinateGradientL i (W i) x = (G i).1 x * (TauCeti.W1p.gradient v x) i +
        TauCeti.W1p.value v x * (gradient (G i).1 x) i :=
    ae_all_iff.mpr (fun i => hWgrad i i)
  have hDu : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      unitBallCoordinateGradientL i u x = (TauCeti.W1p.gradient u x) i :=
    ae_all_iff.mpr (fun i => unitBallCoordinateGradientL_ae i u)
  calc
    _ = ∫ x in ballOpens, ∑ i : Fin 3, z i x := by
      rw [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormH1_def,
        ← integral_sub (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff v u)
          (TauCeti.PDE.integrable_energyIntegrand_jetField hadj u v)]
      apply integral_congr_ae
      filter_upwards [hV,hD,hDu] with x hxV hxD hxDu
      have hp := energyIntegrand_adjoint_difference (a x) (nativeAdjointDriftField G x)
        (WithLp.toLp 2 (fun i : Fin 3 => (gradient (G i).1 x) i)) (c x)
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)
      change TauCeti.PDE.energyIntegrand (a x) (nativeAdjointDriftField G x) (c x)
        (TauCeti.PDE.jetField v x) (TauCeti.PDE.jetField u x) -
          TauCeti.PDE.energyIntegrand (a x)ᵀ (-nativeAdjointDriftField G x)
            (c x-nativeDriftDivergence G x) (TauCeti.PDE.jetField u x)
            (TauCeti.PDE.jetField v x) = _
      simp only [PiLp.toLp_apply] at hp
      unfold nativeDriftDivergence
      rw [hp]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [TauCeti.PDE.jetField_apply,z,Real.inner_apply]
      rw [hxV i,hxD i,hxDu i]
      change ((G i).1 x * (TauCeti.W1p.gradient v x) i +
        TauCeti.W1p.value v x * (gradient (G i).1 x) i) * TauCeti.W1p.value u x +
          ((G i).1 x * TauCeti.W1p.value v x) * (TauCeti.W1p.gradient u x) i = _
      ring
    _ = ∑ i : Fin 3, ∫ x in ballOpens, z i x :=
      integral_finsetSum (μ := (volume : Measure R3).restrict ballOpens)
        (f := fun i x => z i x) Finset.univ (fun i hi => hz i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (nativeCoordinateBulkPairing_eq_integral (W i) u i).symm

lemma nativeCoordinateProduct_boundary_sum
    (τ0 : UnitBallValueTrace) (G : Fin 3 → SmoothData) (u v : BallH1) (W : Fin 3 → BallH1)
    (hWtrace : ∀ i : Fin 3, τ0.valueTraceL (W i) =
      sphereContinuousScalarMulL (smoothSphereValue (G i)) (τ0.valueTraceL v)) :
    (∑ i : Fin 3, (⟪unitBallCoordinateGradientL i (W i),TauCeti.W1p.value u⟫_ℝ +
      ⟪TauCeti.W1p.value (W i),unitBallCoordinateGradientL i u⟫_ℝ)) =
    sphereSurfaceMass * ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G)
      (τ0.valueTraceL u),τ0.valueTraceL v⟫_ℝ := by
  calc
    _ = ∑ i : Fin 3, sphereSurfaceMass *
        ⟪sphereCoordinateMulL i (sphereContinuousScalarMulL (smoothSphereValue (G i))
          (τ0.valueTraceL v)),τ0.valueTraceL u⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [unitBall_coordinate_boundary_inner τ0 (W i) u i,hWtrace i]
    _ = sphereSurfaceMass * ⟪∑ i : Fin 3, sphereCoordinateMulL i
        (sphereContinuousScalarMulL (smoothSphereValue (G i)) (τ0.valueTraceL v)),
          τ0.valueTraceL u⟫_ℝ := by
      rw [sum_inner,Finset.mul_sum]
    _ = _ := by
      rw [native_normalDrift_multiplier_sum,inner_nativeNormalDriftMultiplier_comm]

lemma energyFormH1_adjoint_Green_of_memLp
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (c x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hadj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (c x-nativeDriftDivergence G x)) ⊤
        ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (nativeAdjointDriftField G) c v u =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
          (fun x => c x-nativeDriftDivergence G x) u v +
        sphereSurfaceMass * ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G)
          (τ0.valueTraceL u),τ0.valueTraceL v⟫_ℝ := by
  choose W hWvalue hWgrad hWtrace using
    (fun i : Fin 3 => exists_native_smoothH1Product τ0 (G i) v)
  have hbulk := energyFormH1_adjoint_bulk_difference τ0 a G c hcoeff hadj u v W hWvalue hWgrad
  have hboundary := nativeCoordinateProduct_boundary_sum τ0 G u v W hWtrace
  linarith [hbulk.trans hboundary]

lemma energyFormH1_adjoint_Green
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (ha : Continuous a) (hc : Continuous c) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (nativeAdjointDriftField G) c v u =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
          (fun x => c x-nativeDriftDivergence G x) u v +
        sphereSurfaceMass * ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G)
          (τ0.valueTraceL u),τ0.valueTraceL v⟫_ℝ := by
  exact energyFormH1_adjoint_Green_of_memLp τ0 a G c
    (memLp_nativeEnergyIntegrand_of_continuous a (nativeAdjointDriftField G) c ha
      (continuous_nativeAdjointDriftField G) hc)
    (memLp_nativeEnergyIntegrand_of_continuous (fun x => (a x)ᵀ)
      (fun x => -nativeAdjointDriftField G x) (fun x => c x-nativeDriftDivergence G x)
      ha.matrix_transpose (continuous_nativeAdjointDriftField G).neg
      (hc.sub (continuous_nativeDriftDivergence G))) u v

lemma energyFormH1_adjoint_zero_test
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (ha : Continuous a) (hc : Continuous c) (u : BallH1Zero) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
      (fun x => c x-nativeDriftDivergence G x) (u : BallH1) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (nativeAdjointDriftField G) c v (u : BallH1) := by
  have h := energyFormH1_adjoint_Green τ0 a G c ha hc (u : BallH1) v
  rw [valueTraceL_zeroDirichlet,map_zero,inner_zero_left,mul_zero,add_zero] at h
  exact h.symm

lemma nativeNormalDriftBoundaryPairing_eq_probability_integral
    (G : Fin 3 → SmoothData) (u v : SphereL2) :
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient G) u,v⟫_ℝ =
      ∫ x : UnitSphere, ⟪nativeAdjointDriftField G x.val,x.val⟫_ℝ * u x * v x ∂sphereProbability := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereContinuousScalarMulL_native_value_ae (nativeNormalDriftCoefficient G) u] with x hu
  rw [Real.inner_apply,hu,nativeNormalDriftCoefficient_apply]

lemma energyFormH1L0_adjoint_flip
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (c x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hadj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (c x-nativeDriftDivergence G x)) ⊤
        ((volume : Measure R3).restrict ballOpens)) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
      (c := fun x => c x-nativeDriftDivergence G x) hadj =
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff).flip := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change TauCeti.PDE.energyFormH1L0 hadj u v = TauCeti.PDE.energyFormH1L0 hcoeff v u
  have hL := TauCeti.PDE.energyFormH1L0_apply hadj u v
  have hR := TauCeti.PDE.energyFormH1L0_apply hcoeff v u
  have h := energyFormH1_adjoint_Green_of_memLp τ0 a G c hcoeff hadj (u : BallH1) (v : BallH1)
  rw [valueTraceL_zeroDirichlet,map_zero,inner_zero_left,mul_zero,add_zero] at h
  exact hL.trans (h.symm.trans hR.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAdjointDriftField
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeDriftDivergence
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNormalDriftCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_nativeAdjointDriftField
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_nativeDriftDivergence
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNormalDriftCoefficient_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_native_smoothH1Product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_adjoint_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.native_normalDrift_multiplier_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_nativeNormalDriftMultiplier_comm

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_adjoint_Green_of_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_adjoint_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_adjoint_zero_test

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNormalDriftBoundaryPairing_eq_probability_integral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_adjoint_flip

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereContinuousScalarMulL_native_value_ae

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoordinateBulkPairing_eq_integral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_adjoint_bulk_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoordinateProduct_boundary_sum
