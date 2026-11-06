import Calderon.ActualHighAdjointSmoothMultiplierBoundaryCommutator
import Calderon.ActualHighSmoothMultiplierBoundaryTopology
import Calderon.CoefficientFirstJetsCommonSupport
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.LocalUniformTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier SmoothSphereRotation

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]

local instance referenceAdjointCommonSupportGainEndIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

lemma contDiff_nativeThreeHalfCoefficientMulL_rotation_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t : T => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRotationJets 3 (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) i j)) := by
  let b : T × R3 → ℝ := fun z => unitBallSmoothCutoff z.2 *
    (fderiv ℝ m z) (0,rotationVector i j z.2)
  have hb : ContDiff ℝ ∞ b :=
    (unitBallSmoothCutoff.contDiff.comp contDiff_snd).mul
      ((hm.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const.prodMk ((contDiff_rotationVector i j).comp contDiff_snd)))
  let Kb : Set R3 := tsupport (fun x : R3 => unitBallSmoothCutoff x)
  have hKb : IsCompact Kb := unitBallSmoothCutoff.hasCompactSupport
  have hbz : ∀ t x, x ∉ Kb → b (t,x)=0 := by
    intro t x hx
    have hχ : unitBallSmoothCutoff x = 0 := by
      by_contra hn
      exact hx (subset_closure hn)
    change unitBallSmoothCutoff x * _ = 0
    rw [hχ,zero_mul]
  have hJets (t : T) :
      coefficientRotationJets 3 (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) i j =
        commonSupportCoefficientFamily 3 b hb Kb hKb hbz t := by
    apply smoothCoefficientJets_eq_of_coefficientValue_eq 3
    have hValue : coefficientValue 3 (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) =
        fun x : R3 => m (t,x) := by
      funext x
      exact coefficientValue_commonSupportCoefficientFamily 3 m hm Km hKm hmz t x
    funext x
    rw [coefficientValue_coefficientRotationJets,hValue,
      coefficientValue_commonSupportCoefficientFamily]
    have hSlice := (hm.differentiable (by simp) (t,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    have hAt := congrArg (fun A : R3 →L[ℝ] ℝ => A (rotationVector i j x)) hSlice.fderiv
    have hDerivative : sphereRotationDerivative i j (fun y : R3 => m (t,y)) x =
        fderiv ℝ m (t,x) (0,rotationVector i j x) := by
      simpa only [Function.comp_def,sphereRotationDerivative,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.id_apply] using hAt
    exact congrArg (fun u : ℝ => unitBallSmoothCutoff x * u) hDerivative
  have hSmooth := contDiff_nativeThreeHalfCoefficientMulL_commonSupport
    hcalc hF hO hD τ0 b hb Kb hKb hbz
  have hFamily : (fun t : T => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRotationJets 3 (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) i j)) =
      fun t : T => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 b hb Kb hKb hbz t) := by
    funext t
    exact congrArg (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0) (hJets t)
  exact hFamily.symm ▸ hSmooth

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
  (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalHighCommutatorFamily referenceGaugeNormalThreeHalfMultiplierFamily
  referenceGaugeNormalHighInvertibleLocus referenceStrongDriftFamily nativeThreeHalfCoefficientMulL

lemma contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutator_commonSupport_joint
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hp : p ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2) z.1) (p,t) := by
  have hRoom := hp
  unfold referenceGaugeNormalHighInvertibleLocus at hRoom
  have hB := contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0 p t hRoom.1 hRoom.2
  have hK := (contDiffAt_referenceGaugeNormalHighCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hp).comp (p,t) contDiffAt_fst
  have hM := (contDiff_nativeThreeHalfCoefficientMulL_commonSupport
    hcalc hF hO hD τ0 m hm Km hKm hmz).contDiffAt.comp (p,t) contDiffAt_snd
  have hW := (contDiff_referenceGaugeNormalThreeHalfMultiplierFamily_inverse
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt.comp (p,t) contDiffAt_fst
  have hR : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T => z.1.2.2 ^ 2) (p,t) := by
    fun_prop
  have hCoeff (i j : Fin 3) : ContDiff ℝ ∞
      (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)) := by
    unfold referenceGaugeTangentSecondRotationJetsFamily
    exact contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j)
      (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)
  have hT : ContDiff ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceGaugeTangentSecondHighMultiplierCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2) z.1) := by
    unfold referenceGaugeTangentSecondHighMultiplierCommutatorFamily
      nativeThreeHalfRotationFieldCommutatorGainL
    apply ContDiff.sum
    intro i hi
    apply ContDiff.sum
    intro j hj
    exact ((hCoeff i j).comp contDiff_fst).clm_comp
      ((contDiff_nativeThreeHalfCoefficientMulL_rotation_commonSupport
        hcalc hF hO hD τ0 m hm Km hKm hmz j i).comp contDiff_snd)
  unfold referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  exact ((hB.add (hK.clm_comp hM)).sub (hM.clm_comp hK)).add
    (hR.smul ((hT.contDiffAt.clm_comp hW).const_smul (2 : ℝ)))

local instance referenceAdjointCommonSupportGainCompleteSpaceThreeHalf :
    CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

lemma exists_reference_commonRadius_adjointHighSmoothMultiplier_commonSupport_bound
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ Kt : Set T, IsCompact Kt → ∃ C0 : ℝ, 0 ≤ C0 ∧
        ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
          ∀ t ∈ Kt, ∀ r : ℝ, |r| ≤ δ →
            ‖secondTaylorRemainder (fun τ : ℝ =>
              referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                  (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,τ))) r‖ ≤ C0/2 := by
  obtain ⟨lam,Lam,d,_,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d/2,by positivity,(by linarith),?_⟩
  intro Kt hKt
  let Kbase : Set ((ℝ × R3) × T) :=
    (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) ×ˢ Kt
  have hKbase : IsCompact Kbase := (isCompact_Icc.prod (isCompact_closedBall _ _)).prod hKt
  let F : (((ℝ × R3) × T) × ℝ) →
      SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun z =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.1.2) (z.1.1.1,(z.1.1.2,z.2))
  have hPerm : ContDiff ℝ ∞ (fun z : (((ℝ × R3) × T) × ℝ) =>
      ((z.1.1.1,(z.1.1.2,z.2)),z.1.2)) := by fun_prop
  have hSmooth : ∀ z ∈ Kbase ×ˢ Icc (-(d/2)) (d/2), ContDiffAt ℝ ∞ F z := by
    rintro ⟨⟨⟨q,y⟩,t⟩,r⟩ hz
    have hqr : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
      exact ⟨hz.1.1.1,hz.1.1.2,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
    have hp : (q,(y,r)) ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc := by
      unfold referenceGaugeNormalHighInvertibleLocus
      exact (hRoom (q,(y,r)) hqr).2.2.2.1
    exact (contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutator_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        m hm Km hKm hmz (q,(y,r)) t hp).comp (((q,y),t),r) hPerm.contDiffAt
  obtain ⟨C0,hC0,hBound⟩ := exists_compact_local_uniform_secondTaylorRemainder
    F Kbase hKbase (d/2) (by positivity) hSmooth
  refine ⟨C0,hC0,?_⟩
  intro q hq y hy t ht r hr
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  simpa only [F] using (hBound ((q,y),t) ⟨⟨hq,hyBall⟩,ht⟩ r hr).2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeThreeHalfCoefficientMulL_rotation_commonSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutator_commonSupport_joint

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointHighSmoothMultiplier_commonSupport_bound
