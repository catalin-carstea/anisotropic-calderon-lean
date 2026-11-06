import Calderon.ActualPhysicalDensityProductsWeightedAdjunction

/-! DATA-only candidate; full upfront expansion is EXPANSION.md. No native check claimed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

set_option Elab.async false

theorem referencePhysicalDensityProducts_finiteCore_pairing
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (K : Set R3) (hKgeom : K ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ K, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible))
    (F G : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ K) (hGs : tsupport G.val ⊆ K) :
    let uF : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let uG : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) G
    let K0 : SphereL2 →L[ℝ] Neg :=
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Z : Half →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
    let Zeq : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
    let lift : Half →L[ℝ] SphereL2 := Zeq.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp Z
    let P : R3 → Hi →L[ℝ] Half := fun y => referencePhysicalDensityProductsHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
    let Pd : R3 → Hi →L[ℝ] Half := fun y => referencePhysicalDensityProductsAdjointHalfOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
    let pF : R3 → SphereL2 := fun y => lift (P y (uF y))
    let pdagG : R3 → SphereL2 := fun y => lift (Pd y (uG y))
    (∀ v : Half, K0 (lift v) = J v) ∧
      (∀ y : R3, ⟪pF y,G.val y⟫_ℝ = ⟪F.val y,pdagG y⟫_ℝ) ∧
      (∫ y : R3, referenceDensityFamily g L (q,y) * ⟪pF y,G.val y⟫_ℝ) =
        ∫ y : R3, referenceDensityFamily g L (q,y) * ⟪F.val y,pdagG y⟫_ℝ := by
  classical
  intro uF uG K0 I J Z Zeq lift P Pd pF pdagG
  have hFRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hGRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) G
  have hLift (v : Half) : K0 (lift v) = J v := by
    have hZero : Zeq (lift v) = Z v := Zeq.apply_symm_apply (Z v)
    have hMap : K0 (lift v) = sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z v) :=
      congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) hZero
    have hTrans : sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z v) = J v :=
      congrArg (fun T : Half →L[ℝ] Neg => T v)
        (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
    exact hMap.trans hTrans
  have hBaseF (y : R3) : Z (I (uF y)) = Zeq (F.val y) :=
    (congrArg (fun T : Hi →L[ℝ] SphereSobolev 0 => T (uF y))
      (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))).trans
        (hFRep.2.2.2.1 y)
  have hBaseG (y : R3) : Z (I (uG y)) = Zeq (G.val y) :=
    (congrArg (fun T : Hi →L[ℝ] SphereSobolev 0 => T (uG y))
      (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))).trans
        (hGRep.2.2.2.1 y)
  have hInner (y : R3) : ⟪pF y,G.val y⟫_ℝ = ⟪F.val y,pdagG y⟫_ℝ := by
    by_cases hy : y ∈ K
    · have hyU := hRoom y hy
      have hyNorm : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hKgeom hy
      have hRaw := inner_zero_referencePhysicalDensityProductsAdjointHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 q hq R hR y
          hyNorm hyU.1 hyU.2.2 hyU.2.1 (uF y) (uG y)
      have hRawTyped : ⟪Z (I (uG y)),Z (P y (uF y))⟫_ℝ =
          ⟪Z (Pd y (uG y)),Z (I (uF y))⟫_ℝ := hRaw
      have hPair : ⟪Z (P y (uF y)),Z (I (uG y))⟫_ℝ =
          ⟪Z (I (uF y)),Z (Pd y (uG y))⟫_ℝ :=
        (real_inner_comm (Z (I (uG y))) (Z (P y (uF y)))).trans
          (hRawTyped.trans (real_inner_comm (Z (I (uF y))) (Z (Pd y (uG y)))))
      have hFImage : Zeq (pF y) = Z (P y (uF y)) := Zeq.apply_symm_apply _
      have hGImage : Zeq (pdagG y) = Z (Pd y (uG y)) := Zeq.apply_symm_apply _
      have hLeft : ⟪Zeq (pF y),Zeq (G.val y)⟫_ℝ =
          ⟪Z (P y (uF y)),Z (I (uG y))⟫_ℝ :=
        congrArg₂ (fun a b : SphereSobolev 0 => ⟪a,b⟫_ℝ) hFImage (hBaseG y).symm
      have hRight : ⟪Z (I (uF y)),Z (Pd y (uG y))⟫_ℝ =
          ⟪Zeq (F.val y),Zeq (pdagG y)⟫_ℝ :=
        congrArg₂ (fun a b : SphereSobolev 0 => ⟪a,b⟫_ℝ) (hBaseF y) hGImage.symm
      exact (Zeq.inner_map_map (pF y) (G.val y)).symm.trans
        (hLeft.trans (hPair.trans (hRight.trans (Zeq.inner_map_map (F.val y) (pdagG y)))))
    · have hF0 : F.val y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hFs h))
      have hG0 : G.val y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hGs h))
      simp only [hF0,hG0,inner_zero_left,inner_zero_right]
  refine ⟨hLift,hInner,?_⟩
  have hDensityFun :
      (fun y : R3 => referenceDensityFamily g L (q,y) * ⟪pF y,G.val y⟫_ℝ) =
      (fun y : R3 => referenceDensityFamily g L (q,y) * ⟪F.val y,pdagG y⟫_ℝ) :=
    funext (fun y => congrArg
      (fun t : ℝ => referenceDensityFamily g L (q,y) * t) (hInner y))
  exact congrArg
    (fun k : R3 → ℝ => ∫ y : R3, k y ∂(volume : Measure R3)) hDensityFun

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
