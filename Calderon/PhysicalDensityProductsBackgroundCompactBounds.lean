import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.CompactParameterReferenceFramedNormalMetric
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Complete background cap with opaque component assembly. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

private theorem exists_compact_three_pair_norm_bound
    {X V W : Type*} [TopologicalSpace X]
    [instV : NormedAddCommGroup V] [instW : NormedAddCommGroup W]
    (K : Set X) (hK : IsCompact K)
    (A : Fin 3 → X → V) (B : Fin 3 → X → W)
    (hA : ∀ i : Fin 3, ContinuousOn (A i) K)
    (hB : ∀ i : Fin 3, ContinuousOn (B i) K) :
    ∃ CF : ℝ, 0 < CF ∧
      ∀ x ∈ K, ∀ i : Fin 3, ‖A i x‖ ≤ CF ∧ ‖B i x‖ ≤ CF := by
  classical
  have hSCont : ContinuousOn (fun x : X => ∑ i : Fin 3, (‖A i x‖+‖B i x‖)) K :=
    continuousOn_finsetSum _ (fun i _ => (hA i).norm.add (hB i).norm)
  obtain ⟨B0,hB0⟩ := hK.exists_bound_of_continuousOn hSCont
  let CF : ℝ := 1+|B0|
  have hCF : 0 < CF := by dsimp only [CF]; linarith [abs_nonneg B0]
  have hB0CF : |B0| ≤ CF := by dsimp only [CF]; linarith
  have hSum (x : X) (hx : x ∈ K) : (∑ j : Fin 3, (‖A j x‖+‖B j x‖)) ≤ |B0| := by
    have hScalar : |∑ j : Fin 3, (‖A j x‖+‖B j x‖)| ≤ B0 := by
      simpa only [Real.norm_eq_abs] using hB0 x hx
    exact (le_abs_self _).trans (hScalar.trans (le_abs_self B0))
  refine ⟨CF,hCF,?_⟩
  intro x hx i
  have hPair : ‖A i x‖+‖B i x‖ ≤ ∑ j : Fin 3, (‖A j x‖+‖B j x‖) :=
    Finset.single_le_sum
      (fun j _ => add_nonneg (norm_nonneg (A j x)) (norm_nonneg (B j x)))
      (Finset.mem_univ i)
  have hHigh : ‖A i x‖ ≤ ‖A i x‖+‖B i x‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hLow : ‖B i x‖ ≤ ‖A i x‖+‖B i x‖ := le_add_of_nonneg_left (norm_nonneg _)
  exact ⟨hHigh.trans (hPair.trans ((hSum x hx).trans hB0CF)),
    hLow.trans (hPair.trans ((hSum x hx).trans hB0CF))⟩

/-- Complete actual high/low correction cap on the canonical gradient-dual compact ball. -/
private theorem exists_referenceNativeMovingAdjointCorrections_compact_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) (ρ : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    letI backgroundHiEndNormedAddCommGroup :
        NormedAddCommGroup (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedAddCommGroup :
        NormedAddCommGroup (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedAddCommGroup :
        NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    let FH : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Hi →L[ℝ] Hi := fun i z =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) z i
    let FL : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Half →L[ℝ] Half := fun i z =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) z i
    ∃ CF : ℝ, 0 < CF ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        ∀ p ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1, ∀ i : Fin 3,
          ‖FH i ((q,y),p)‖ ≤ CF ∧ ‖FL i ((q,y),p)‖ ≤ CF := by
  classical
  letI backgroundHiEndNormedAddCommGroup :
      NormedAddCommGroup (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  let FH : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Hi →L[ℝ] Hi := fun i z =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) z i
  let FL : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Half →L[ℝ] Half := fun i z =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) z i
  change ∃ CF : ℝ, 0 < CF ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        ∀ p ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1, ∀ i : Fin 3,
          ‖FH i ((q,y),p)‖ ≤ CF ∧ ‖FL i ((q,y),p)‖ ≤ CF
  let K0 : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  let KF : Set ((ℝ × R3) × (R3 →L[ℝ] ℝ)) :=
    K0 ×ˢ closedBall (0 : R3 →L[ℝ] ℝ) 1
  letI dualFiniteDimensional : FiniteDimensional ℝ (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional (𝕜 := ℝ) (E := R3) (F := ℝ)
  letI dualProperSpace : ProperSpace (R3 →L[ℝ] ℝ) :=
    FiniteDimensional.proper_real (R3 →L[ℝ] ℝ)
  have hK0 : IsCompact K0 := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKF : IsCompact KF := hK0.prod (isCompact_closedBall _ _)
  have hFH (i : Fin 3) : ContinuousOn (FH i) KF :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection
      hF hO hD g hg L (3/2 : ℝ) i).continuous.continuousOn
  have hFL (i : Fin 3) : ContinuousOn (FL i) KF :=
    (contDiff_referenceNativeMovingAdjointParametricCorrection
      hF hO hD g hg L (1/2 : ℝ) i).continuous.continuousOn
  obtain ⟨CF,hCF,hFBounds⟩ := exists_compact_three_pair_norm_bound
    (X := (ℝ × R3) × (R3 →L[ℝ] ℝ))
    (V := Hi →L[ℝ] Hi) (W := Half →L[ℝ] Half)
    (instV := backgroundHiEndNormedAddCommGroup)
    (instW := backgroundHalfEndNormedAddCommGroup)
    KF hKF FH FL hFH hFL
  refine ⟨CF,hCF,?_⟩
  intro q hq y hy p hp i
  exact hFBounds ((q,y),p) ⟨⟨hq,hy⟩,hp⟩ i

/-- Complete actual principal, full-frame, opaque-coordinate and fixed high-multiplier caps. -/
private theorem exists_referencePhysicalDensityProducts_four_compact_bounds
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (y0 : R3) (ρ : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    letI backgroundHiEndNormedAddCommGroup :
        NormedAddCommGroup (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedAddCommGroup :
        NormedAddCommGroup (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedAddCommGroup :
        NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    letI backgroundFrameNormedAddCommGroup :
        NormedAddCommGroup (R3 →L[ℝ] R3) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
    letI backgroundFrameNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
    let Q : Fin 3 → Fin 3 → (ℝ × R3) → ℝ := fun i j b =>
      referenceDensityPrincipalFrameCoefficient g g2 L b.1 b.2 i j
    let Frame : (ℝ × R3) → R3 →L[ℝ] R3 := conformalReferenceGramFrameOperatorJoint g L
    let J : Fin 3 → Hi →L[ℝ] Hi := fun i =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
    ∃ CQ CFrame CV CM : ℝ,
      0 < CQ ∧ 0 < CFrame ∧ 0 < CV ∧ 0 < CM ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ i j : Fin 3,
        |Q i j (q,y)| ≤ CQ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ‖Frame (q,y)‖ ≤ CFrame) ∧
      (∀ i : Fin 3, ‖coordinateVector i‖ ≤ CV) ∧
      (∀ i : Fin 3, ‖J i‖ ≤ CM) := by
  classical
  letI backgroundHiEndNormedAddCommGroup :
      NormedAddCommGroup (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  let Q : Fin 3 → Fin 3 → (ℝ × R3) → ℝ := fun i j b =>
    referenceDensityPrincipalFrameCoefficient g g2 L b.1 b.2 i j
  let Frame : (ℝ × R3) → R3 →L[ℝ] R3 := conformalReferenceGramFrameOperatorJoint g L
  let J : Fin 3 → Hi →L[ℝ] Hi := fun i =>
    sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
  change ∃ CQ CFrame CV CM : ℝ,
      0 < CQ ∧ 0 < CFrame ∧ 0 < CV ∧ 0 < CM ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ i j : Fin 3,
        |Q i j (q,y)| ≤ CQ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ‖Frame (q,y)‖ ≤ CFrame) ∧
      (∀ i : Fin 3, ‖coordinateVector i‖ ≤ CV) ∧
      (∀ i : Fin 3, ‖J i‖ ≤ CM)
  let K0 : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  have hK0 : IsCompact K0 := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hQCont (i j : Fin 3) : ContinuousOn (Q i j) K0 :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.continuousOn
  have hQsumCont : ContinuousOn (fun b : ℝ × R3 => ∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j b‖) K0 :=
    continuousOn_finsetSum _ (fun i _ =>
      continuousOn_finsetSum _ (fun j _ => (hQCont i j).norm))
  obtain ⟨BQ,hBQ⟩ := hK0.exists_bound_of_continuousOn hQsumCont
  let CQ : ℝ := 1+|BQ|
  have hCQ : 0 < CQ := by dsimp only [CQ]; linarith [abs_nonneg BQ]
  have hBQle : |BQ| ≤ CQ := by dsimp only [CQ]; linarith
  have hQsumBound (b : ℝ × R3) (hb : b ∈ K0) :
      (∑ k : Fin 3, ∑ l : Fin 3, ‖Q k l b‖) ≤ |BQ| := by
    have hScalar : |∑ k : Fin 3, ∑ l : Fin 3, ‖Q k l b‖| ≤ BQ := by
      simpa only [Real.norm_eq_abs] using hBQ b hb
    exact (le_abs_self _).trans (hScalar.trans (le_abs_self BQ))
  have hQBound (b : ℝ × R3) (hb : b ∈ K0) (i j : Fin 3) : |Q i j b| ≤ CQ := by
    have hRow : ‖Q i j b‖ ≤ ∑ l : Fin 3, ‖Q i l b‖ :=
      Finset.single_le_sum (fun l _ => norm_nonneg (Q i l b)) (Finset.mem_univ j)
    have hRows : (∑ l : Fin 3, ‖Q i l b‖) ≤ ∑ k : Fin 3, ∑ l : Fin 3, ‖Q k l b‖ :=
      Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (Q k l b)))
        (Finset.mem_univ i)
    have hRaw : ‖Q i j b‖ ≤ CQ :=
      hRow.trans (hRows.trans ((hQsumBound b hb).trans hBQle))
    simpa only [Real.norm_eq_abs] using hRaw
  have hFrameCont : ContinuousOn Frame K0 :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).continuous.continuousOn
  obtain ⟨BG,hBG⟩ := hK0.exists_bound_of_continuousOn hFrameCont
  let CFrame : ℝ := 1+|BG|
  have hCFrame : 0 < CFrame := by dsimp only [CFrame]; linarith [abs_nonneg BG]
  have hBGle : |BG| ≤ CFrame := by dsimp only [CFrame]; linarith
  have hFrameBound (b : ℝ × R3) (hb : b ∈ K0) : ‖Frame b‖ ≤ CFrame :=
    (hBG b hb).trans ((le_abs_self BG).trans hBGle)
  let CV : ℝ := 1+∑ i : Fin 3, ‖coordinateVector i‖
  have hVecSum : 0 ≤ ∑ i : Fin 3, ‖coordinateVector i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg (coordinateVector i))
  have hCV : 0 < CV := by dsimp only [CV]; linarith
  have hVecBound (i : Fin 3) : ‖coordinateVector i‖ ≤ CV := by
    have hOne : ‖coordinateVector i‖ ≤ ∑ j : Fin 3, ‖coordinateVector j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (coordinateVector j)) (Finset.mem_univ i)
    exact hOne.trans (le_add_of_nonneg_left zero_le_one)
  let CM : ℝ := 1+∑ i : Fin 3, ‖J i‖
  have hMulSum : 0 ≤ ∑ i : Fin 3, ‖J i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg (J i))
  have hCM : 0 < CM := by dsimp only [CM]; linarith
  have hMulBound (i : Fin 3) : ‖J i‖ ≤ CM := by
    have hOne : ‖J i‖ ≤ ∑ j : Fin 3, ‖J j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (J j)) (Finset.mem_univ i)
    exact hOne.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨CQ,CFrame,CV,CM,hCQ,hCFrame,hCV,hCM,?_,?_,hVecBound,hMulBound⟩
  · intro q hq y hy i j
    exact hQBound (q,y) ⟨hq,hy⟩ i j
  · intro q hq y hy
    exact hFrameBound (q,y) ⟨hq,hy⟩

/-- Uniform actual correction, principal, frame and fixed-coordinate bounds. -/
theorem exists_referencePhysicalDensityProducts_background_compact_bounds
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (y0 : R3) (ρ : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    letI backgroundHiEndNormedAddCommGroup :
        NormedAddCommGroup (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedAddCommGroup :
        NormedAddCommGroup (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedAddCommGroup :
        NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
    letI backgroundFrameNormedAddCommGroup :
        NormedAddCommGroup (R3 →L[ℝ] R3) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
    letI backgroundFrameNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
    let FH : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Hi →L[ℝ] Hi := fun i z =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) z i
    let FL : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Half →L[ℝ] Half := fun i z =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) z i
    let Q : Fin 3 → Fin 3 → (ℝ × R3) → ℝ := fun i j b =>
      referenceDensityPrincipalFrameCoefficient g g2 L b.1 b.2 i j
    let Frame : (ℝ × R3) → R3 →L[ℝ] R3 := conformalReferenceGramFrameOperatorJoint g L
    let J : Fin 3 → Hi →L[ℝ] Hi := fun i =>
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
    ∃ CF CQ CFrame CV CM : ℝ,
      0 < CF ∧ 0 < CQ ∧ 0 < CFrame ∧ 0 < CV ∧ 0 < CM ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        ∀ p ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1, ∀ i : Fin 3,
          ‖FH i ((q,y),p)‖ ≤ CF ∧ ‖FL i ((q,y),p)‖ ≤ CF) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ i j : Fin 3,
        |Q i j (q,y)| ≤ CQ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ‖Frame (q,y)‖ ≤ CFrame) ∧
      (∀ i : Fin 3, ‖coordinateVector i‖ ≤ CV) ∧
      (∀ i : Fin 3, ‖J i‖ ≤ CM) := by
  classical
  letI backgroundHiEndNormedAddCommGroup :
      NormedAddCommGroup (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHiEndNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Hi) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Hi) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (Half →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundDualNormedSpace : NormedSpace ℝ (R3 →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedAddCommGroup :
      NormedAddCommGroup (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  letI backgroundFrameNormedSpace : NormedSpace ℝ (R3 →L[ℝ] R3) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := R3) (F := R3) (σ₁₂ := RingHom.id ℝ)
  let FH : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Hi →L[ℝ] Hi := fun i z =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) z i
  let FL : Fin 3 → ((ℝ × R3) × (R3 →L[ℝ] ℝ)) → Half →L[ℝ] Half := fun i z =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) z i
  let Q : Fin 3 → Fin 3 → (ℝ × R3) → ℝ := fun i j b =>
    referenceDensityPrincipalFrameCoefficient g g2 L b.1 b.2 i j
  let Frame : (ℝ × R3) → R3 →L[ℝ] R3 := conformalReferenceGramFrameOperatorJoint g L
  let J : Fin 3 → Hi →L[ℝ] Hi := fun i =>
    sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1)
  change ∃ CF CQ CFrame CV CM : ℝ,
      0 < CF ∧ 0 < CQ ∧ 0 < CFrame ∧ 0 < CV ∧ 0 < CM ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        ∀ p ∈ closedBall (0 : R3 →L[ℝ] ℝ) 1, ∀ i : Fin 3,
          ‖FH i ((q,y),p)‖ ≤ CF ∧ ‖FL i ((q,y),p)‖ ≤ CF) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ i j : Fin 3,
        |Q i j (q,y)| ≤ CQ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ‖Frame (q,y)‖ ≤ CFrame) ∧
      (∀ i : Fin 3, ‖coordinateVector i‖ ≤ CV) ∧
      (∀ i : Fin 3, ‖J i‖ ≤ CM)
  obtain ⟨CF,hCF,hFCompactBounds⟩ :=
    exists_referenceNativeMovingAdjointCorrections_compact_bound
      g hg L y0 ρ hF hO hD
  obtain ⟨CQ,CFrame,CV,CM,hCQ,hCFrame,hCV,hCM,hQCompactBounds,hFrameCompactBounds,hVecBound,hMulBound⟩ :=
    exists_referencePhysicalDensityProducts_four_compact_bounds
      g g2 hg hg2 L y0 ρ hF hO hD
  refine ⟨CF,CQ,CFrame,CV,CM,hCF,hCQ,hCFrame,hCV,hCM,?_,?_,?_,hVecBound,hMulBound⟩
  · intro q hq y hy p hp i
    exact hFCompactBounds q hq y hy p hp i
  · intro q hq y hy i j
    exact hQCompactBounds q hq y hy i j
  · intro q hq y hy
    exact hFrameCompactBounds q hq y hy

#print axioms exists_compact_three_pair_norm_bound
#print axioms exists_referenceNativeMovingAdjointCorrections_compact_bound
#print axioms exists_referencePhysicalDensityProducts_four_compact_bounds
#print axioms exists_referencePhysicalDensityProducts_background_compact_bounds

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
